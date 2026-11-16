#!/usr/bin/env python3
"""Regression test for defect A1 (WF-clientsuites DIAGNOSIS; fixed in client 0.4.1): a second sign-in on the fixed callback port right after a first one.

    python -I test_login_port_reuse.py            (run from mreg/next/, or set MREG_PY to the client file)

Without the fix, on Linux the second bind fails with "Address already in use" for about 60 s (TIME_WAIT left by the first sign-in's
callback connection, which the server closes first). With the fix (allow_reuse_address on POSIX) it succeeds. On every platform a
socket that is still listening must keep refusing a second bind: the port is never shared."""
import importlib.util, os, socket, sys, threading, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("mreg_port", os.environ.get("MREG_PY") or os.path.join(HERE, "mreg.py"))
M = importlib.util.module_from_spec(spec)
spec.loader.exec_module(M)


def one_signin(port):
    """Bind the callback server, let a 'browser' deliver one callback, read the answer to EOF, close the server. Returns the server."""
    srv = M._Callback(("127.0.0.1", port), M._CallbackHandler)
    srv.result, srv.lock, srv.timeout = None, threading.Lock(), 5
    t = threading.Thread(target=srv.handle_request)
    t.start()
    p = srv.server_address[1]
    c = socket.create_connection(("127.0.0.1", p), timeout=10)
    c.sendall(f"GET /callback?code=a&state=b HTTP/1.1\r\nHost: 127.0.0.1:{p}\r\n\r\n".encode())
    while c.recv(65536):          # EOF: the SERVER closed its end first
        pass
    t.join(10)
    srv.server_close()
    c.close()                     # the client closes last, so TIME_WAIT sits on the server's port
    assert srv.result == {"code": "a", "state": "b"}, srv.result
    return p


class PortReuse(unittest.TestCase):
    def test_second_sign_in_binds_right_after_the_first(self):
        p = one_signin(0)
        srv2 = M._Callback(("127.0.0.1", p), M._CallbackHandler)      # raised OSError (EADDRINUSE) on Linux before the fix
        srv2.server_close()

    def test_a_listening_port_is_never_shared(self):
        srv = M._Callback(("127.0.0.1", 0), M._CallbackHandler)
        self.addCleanup(srv.server_close)
        with self.assertRaises(OSError):
            M._Callback(("127.0.0.1", srv.server_address[1]), M._CallbackHandler)

    def test_socket_options_per_platform(self):
        """The sharing options: POSIX has SO_REUSEADDR on and SO_REUSEPORT never; Windows has SO_EXCLUSIVEADDRUSE on and SO_REUSEADDR off."""
        srv = M._Callback(("127.0.0.1", 0), M._CallbackHandler)
        self.addCleanup(srv.server_close)
        g = lambda name: srv.socket.getsockopt(socket.SOL_SOCKET, getattr(socket, name))
        if os.name == "nt":
            self.assertEqual(g("SO_EXCLUSIVEADDRUSE"), 1)
            self.assertEqual(g("SO_REUSEADDR"), 0)
        else:
            self.assertNotEqual(g("SO_REUSEADDR"), 0)
            if hasattr(socket, "SO_REUSEPORT"):
                self.assertEqual(g("SO_REUSEPORT"), 0)


if __name__ == "__main__":
    unittest.main(verbosity=1)
