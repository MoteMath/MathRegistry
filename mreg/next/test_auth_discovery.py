#!/usr/bin/env python3
"""Tests for /.well-known/mreg-auth.json discovery and multi-port loopback fallback (mreg 0.5.1)."""
import http.server
import importlib.util
import json
import os
import socket
import threading
import unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("mreg_auth_disc", os.path.join(HERE, "mreg.py"))
M = importlib.util.module_from_spec(spec)
spec.loader.exec_module(M)


class _DiscoveryServer(http.server.ThreadingHTTPServer):
    daemon_threads = True

    def __init__(self, handler_fn):
        self.handler_fn = handler_fn
        super().__init__(("127.0.0.1", 0), _ReqHandler)
        threading.Thread(target=self.serve_forever, daemon=True).start()

    @property
    def url(self):
        return f"http://127.0.0.1:{self.server_port}"


class _ReqHandler(http.server.BaseHTTPRequestHandler):
    def log_message(self, *args):
        pass

    def do_GET(self):
        code, body = self.server.handler_fn(self.path)
        raw = body if isinstance(body, bytes) else json.dumps(body).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(raw)))
        self.end_headers()
        self.wfile.write(raw)


class AuthDiscoveryTests(unittest.TestCase):
    def _clean_env(self, **extra):
        env = dict(os.environ)
        for k in ("MREG_AUTH_URL", "MREG_KEYS_URL", "MREG_CLIENT_ID", "MREG_LOGIN_PORT", "MREG_REGISTRY"):
            env.pop(k, None)
        env.update(extra)
        return mock.patch.dict(os.environ, env, clear=True)

    def test_discovers_endpoints_and_env_takes_precedence(self):
        doc = {
            "schema": "mreg-auth/1",
            "auth_url": "https://auth.example.org",
            "keys_url": "https://keys.example.org",
            "client_id": "client_123",
            "login_ports": [8981, 8982],
            "account_page": "https://example.org/account",
        }
        srv = _DiscoveryServer(lambda p: (200, doc) if p == M.WELL_KNOWN_AUTH_PATH else (404, {}))
        self.addCleanup(srv.server_close)
        self.addCleanup(srv.shutdown)
        with self._clean_env(MREG_REGISTRY=srv.url):
            cfg = M.discover_auth_config()
        self.assertTrue(cfg["discovered"])
        self.assertEqual(cfg["auth_url"], "https://auth.example.org")
        self.assertEqual(cfg["keys_url"], "https://keys.example.org")
        self.assertEqual(cfg["client_id"], "client_123")
        self.assertEqual(cfg["login_ports"], [8981, 8982])
        self.assertEqual(cfg["account_page"], "https://example.org/account")

        with self._clean_env(MREG_REGISTRY=srv.url, MREG_AUTH_URL="http://127.0.0.1:9001", MREG_LOGIN_PORT="8999"):
            cfg2 = M.discover_auth_config()
        self.assertEqual(cfg2["auth_url"], "http://127.0.0.1:9001")
        self.assertEqual(cfg2["keys_url"], "https://keys.example.org")
        self.assertEqual(cfg2["login_ports"], [8999])

    def test_falls_back_to_constants_on_404_or_invalid_json(self):
        for reply in ((404, b"not found"), (200, b"not-json")):
            srv = _DiscoveryServer(lambda _p, r=reply: r)
            self.addCleanup(srv.server_close)
            self.addCleanup(srv.shutdown)
            with self._clean_env(MREG_REGISTRY=srv.url):
                cfg = M.discover_auth_config()
            self.assertFalse(cfg["discovered"])
            self.assertEqual(cfg["auth_url"], M.AUTH_URL)
            self.assertEqual(cfg["keys_url"], M.KEYS_URL)
            self.assertEqual(cfg["client_id"], M.CLIENT_ID)
            self.assertEqual(cfg["login_ports"], list(M.LOGIN_PORTS))

    def test_rejects_non_https_discovered_urls(self):
        srv = _DiscoveryServer(lambda _p: (200, {"schema": "mreg-auth/1", "auth_url": "http://insecure.example"}))
        self.addCleanup(srv.server_close)
        self.addCleanup(srv.shutdown)
        with self._clean_env(MREG_REGISTRY=srv.url):
            with self.assertRaises(SystemExit) as cm:
                M.discover_auth_config()
        self.assertIn("https address", str(cm.exception))

    def test_signin_falls_back_to_second_loopback_port_when_first_is_busy(self):
        busy = socket.socket()
        busy.bind(("127.0.0.1", 0))
        busy.listen(1)
        self.addCleanup(busy.close)
        p1 = busy.getsockname()[1]

        probe = socket.socket()
        probe.bind(("127.0.0.1", 0))
        p2 = probe.getsockname()[1]
        probe.close()

        opened = []

        def fake_open(url):
            opened.append(url)
            # Trigger callback asynchronously to the selected loopback port
            def send():
                import urllib.parse, urllib.request
                q = urllib.parse.parse_qs(urllib.parse.urlparse(url).query)
                redir = q["redirect_uri"][0]
                urllib.request.urlopen(f"{redir}?code=okcode&state={q['state'][0]}", timeout=5).read()
            threading.Thread(target=send, daemon=True).start()
            return True

        cfg = {"auth_url": "https://auth.example.org", "keys_url": "https://keys.example.org",
               "client_id": "cid", "login_ports": [p1, p2], "account_page": "https://example.org/account", "discovered": True}
        with mock.patch.object(M, "_open_browser", fake_open), \
                mock.patch.object(M, "_exchange", lambda auth, cid, redir, code, ver: f"idtoken:{redir}"):
            tok = M.signin(timeout=5.0, auth_cfg=cfg)
        self.assertEqual(tok, f"idtoken:http://localhost:{p2}/callback")
        self.assertEqual(len(opened), 1)
        self.assertIn(f"localhost%3A{p2}%2Fcallback", opened[0])

    def test_partial_discovery_document_is_ignored_atomically(self):
        srv = _DiscoveryServer(
            lambda p: (200, {"schema": "mreg-auth/1", "auth_url": "https://other.example"})
            if p == M.WELL_KNOWN_AUTH_PATH else (404, {})
        )
        self.addCleanup(srv.server_close)
        self.addCleanup(srv.shutdown)
        with self._clean_env(MREG_REGISTRY=srv.url):
            cfg = M.discover_auth_config()
        self.assertFalse(cfg["discovered"])
        self.assertEqual(cfg["auth_url"], M.AUTH_URL)
        self.assertEqual(cfg["keys_url"], M.KEYS_URL)
        self.assertEqual(cfg["client_id"], M.CLIENT_ID)

    def test_callback_ignores_unauthenticated_error_and_validates_state(self):
        import contextlib, io, urllib.error, urllib.parse, urllib.request
        cfg = {
            "auth_url": "https://auth.example.org",
            "keys_url": "https://keys.example.org",
            "client_id": "client_123",
            "login_ports": [0],
        }
        results = []
        done = threading.Event()

        def fake_open(url):
            qs = urllib.parse.parse_qs(urllib.parse.urlsplit(url).query)
            redir = urllib.parse.urlsplit(qs["redirect_uri"][0])
            port = redir.port
            st = qs["state"][0]

            def send_reqs():
                try:
                    try:
                        with urllib.request.urlopen(f"http://127.0.0.1:{port}/callback?error=access_denied", timeout=5) as r:
                            results.append(("no_state", r.status))
                    except urllib.error.HTTPError as e:
                        results.append(("no_state", e.code))
                        e.close()
                    with urllib.request.urlopen(
                        f"http://127.0.0.1:{port}/callback?error=access_denied&state={urllib.parse.quote(st)}", timeout=5
                    ) as r:
                        results.append(("with_state", r.status, r.read().decode("utf-8")))
                finally:
                    done.set()

            threading.Thread(target=send_reqs, daemon=True).start()
            return True

        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(M, "_open_browser", fake_open), contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            with self.assertRaises(SystemExit) as cm:
                M.signin(timeout=5.0, auth_cfg=cfg)
        self.assertTrue(done.wait(timeout=5.0))
        self.assertEqual(results[0], ("no_state", 400))
        self.assertEqual(results[1][0], "with_state")
        self.assertEqual(results[1][1], 200)
        self.assertIn("not completed", results[1][2])
        self.assertIn("not completed", str(cm.exception))


if __name__ == "__main__":
    unittest.main(verbosity=2)
