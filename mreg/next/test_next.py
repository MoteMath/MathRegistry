#!/usr/bin/env python3
"""Tests of mreg/next/mreg.py: `mreg login|logout|whoami` and the by-declaration syntax. Stdlib only.

    python test_next.py

No network, no AWS, no Lean, and never the real ~/.mreg: every test runs with a temporary home directory. The sign-in flow
runs against local fake servers (authorize, token, key service and registry on 127.0.0.1); the declaration tests build a
small registry in the registry's layout under a temporary directory and use it as a file:/// registry. The registry builder
below is adapted from promote/test_promote.py (make_build, make_project); it does not import that file.

The last class runs the EXISTING commands (view, train, install, ci, audit) with the live client (../mreg.py, only executed,
never edited) and with the copy against the same registry and compares output, exit code and lock file.
"""
import base64
import contextlib
import hashlib
import hmac
import http.client
import http.server
import importlib.util
import io
import json
import os
import pathlib
import re
import secrets
import shutil
import socket
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
import unittest
import urllib.parse
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
NEXT_PATH = os.path.join(HERE, "mreg.py")
BASE_PATH = os.path.join(os.path.dirname(HERE), "mreg.py")      # the live client: executed for comparison, never edited
spec = importlib.util.spec_from_file_location("mreg_next_under_test", NEXT_PATH)
M = importlib.util.module_from_spec(spec)
spec.loader.exec_module(M)

TOOLCHAIN = "leanprover/lean4:v4.35.0"
PLAT = M.platform_triple()
TRAIN = "lean-4.35.0"


def b64u(b):
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode()


def sha(b):
    return hashlib.sha256(b).hexdigest()


def free_port():
    s = socket.socket()
    s.bind(("127.0.0.1", 0))
    p = s.getsockname()[1]
    s.close()
    return p


# ======================================================================================= fake sign-in, key service, registry

class Fake:
    """One local HTTP server playing the pool (/oauth2/authorize, /oauth2/token), the key service (/keysvc/keys...) and the
    registry (/v1/index/trains.json). `mode` switches the failure cases."""

    def __init__(self):
        self.secret = "k" * 64
        self.mode = {"authorize": "ok", "token": "ok", "keys": "ok", "registry": "ok", "delete": "ok"}
        self.authz, self.token_reqs, self.created, self.deleted, self.reg_seen = [], [], [], [], []
        self.codes, self.id_tokens, self.verifiers, self.keys, self.key_ids = {}, set(), [], [], set()
        self.other_secrets = []
        fake = self

        class H(http.server.BaseHTTPRequestHandler):
            def log_message(self, *a):
                pass

            def send(self, code, obj=None, headers=None):
                body = b"" if obj is None else json.dumps(obj).encode()
                self.send_response(code)
                self.send_header("Content-Length", str(len(body)))
                for k, v in (headers or {}).items():
                    self.send_header(k, v)
                self.end_headers()
                self.wfile.write(body)

            def bearer(self):
                m = re.match(r"Bearer (\S+)$", self.headers.get("Authorization") or "")
                return m.group(1) if m and m.group(1) in fake.id_tokens else None

            def do_GET(self):
                u = urllib.parse.urlparse(self.path)
                q = {k: v[0] for k, v in urllib.parse.parse_qs(u.query).items()}
                if u.path == "/oauth2/authorize":
                    fake.authz.append(q)
                    mode = fake.mode["authorize"]
                    if mode == "page":
                        return self.send(200, {})
                    code = secrets.token_urlsafe(16)
                    fake.codes[code] = q
                    if mode == "deny":
                        loc = f"{q['redirect_uri']}?error=access_denied&state={q['state']}"
                    else:
                        st = "x" + q["state"] if mode == "tamper" else q["state"]
                        loc = f"{q['redirect_uri']}?code={code}&state={st}"
                    return self.send(302, None, {"Location": loc})
                if u.path == "/v1/index/trains.json":
                    tok = self.headers.get("x-mreg-token") or ""
                    fake.reg_seen.append(tok)
                    if fake.mode["registry"] == "ok" and tok in fake.keys and fake.valid(tok):
                        return self.send(200, {"trains": []})
                    return self.send(403)
                return self.send(404, {"error": "not_found"})

            def do_POST(self):
                n = int(self.headers.get("Content-Length") or 0)
                raw = self.rfile.read(n)
                if self.path == "/oauth2/token":
                    f = {k: v[0] for k, v in urllib.parse.parse_qs(raw.decode()).items()}
                    fake.token_reqs.append(f)
                    fake.verifiers.append(f.get("code_verifier", ""))
                    a = fake.codes.pop(f.get("code"), None)
                    if fake.mode["token"] == "badcode" or a is None:
                        return self.send(400, {"error": "invalid_grant"})
                    ok = (f.get("grant_type") == "authorization_code" and f.get("client_id") == a["client_id"]
                          and f.get("redirect_uri") == a["redirect_uri"]
                          and b64u(hashlib.sha256(f.get("code_verifier", "").encode()).digest()) == a["code_challenge"])
                    if not ok:
                        return self.send(400, {"error": "invalid_grant"})
                    tok = "h." + secrets.token_urlsafe(24) + ".s"
                    fake.id_tokens.add(tok)
                    other = {"access_token": "at-" + secrets.token_urlsafe(16), "refresh_token": "rt-" + secrets.token_urlsafe(16)}
                    fake.other_secrets += list(other.values())
                    return self.send(200, dict(other, id_token=tok))
                if self.path == "/keysvc/keys":
                    if not self.bearer():
                        return self.send(401, {"error": "unauthorized"})
                    label = json.loads(raw or b"{}").get("label")
                    if fake.mode["keys"] == "limit":
                        return self.send(409, {"error": "key_limit", "max": 10})
                    kid = "k" + secrets.token_urlsafe(9)
                    key = fake.mint(kid)
                    fake.keys.append(key)
                    fake.key_ids.add(kid)
                    fake.created.append({"id": kid, "label": label})
                    return self.send(201, {"key": key, "id": kid, "label": label, "scope": "read", "state": "active"})
                return self.send(404, {"error": "not_found"})

            def do_DELETE(self):
                m = re.match(r"/keysvc/keys/(k[A-Za-z0-9_-]{12})$", self.path)
                if not self.bearer():
                    return self.send(401, {"error": "unauthorized"})
                if not m:
                    return self.send(404, {"error": "not_found"})
                fake.deleted.append(m.group(1))
                if fake.mode["delete"] == "notfound" or m.group(1) not in fake.key_ids:
                    return self.send(404, {"error": "not_found"})
                fake.key_ids.discard(m.group(1))
                return self.send(200, {"id": m.group(1), "state": "revoked"})

        self.srv = http.server.ThreadingHTTPServer(("127.0.0.1", 0), H)
        self.srv.daemon_threads = True
        self.port = self.srv.server_address[1]
        self.base = f"http://127.0.0.1:{self.port}"
        threading.Thread(target=self.srv.serve_forever, daemon=True).start()

    def mint(self, kid, owner="us-east-1:owner-123", iat=1789000000):
        p = b64u(json.dumps({"v": 1, "k": kid, "o": owner, "s": "read", "i": iat}, separators=(",", ":")).encode())
        sig = b64u(hmac.new(self.secret.encode(), ("mreg-key-v1." + p).encode(), hashlib.sha256).digest())
        return f"mreg_{p}.{sig}"

    def valid(self, key):
        m = M.KEY_RE.match(key)
        if not m:
            return False
        want = b64u(hmac.new(self.secret.encode(), ("mreg-key-v1." + m.group(1)).encode(), hashlib.sha256).digest())
        info = M.decode_key(key)
        return want == m.group(2) and info is not None and info["k"] in self.key_ids

    def secrets_seen(self):
        return list(self.codes) + [f["code"] for f in self.token_reqs if "code" in f] + list(self.id_tokens) + [
            v for v in self.verifiers if v] + list(self.keys) + self.other_secrets

    def stop(self):
        self.srv.shutdown()
        self.srv.server_close()


def play_browser(url, stray=False):
    """What the user's browser does: open the authorize address, follow the redirect to the local callback."""
    u = urllib.parse.urlparse(url)
    c = http.client.HTTPConnection(u.hostname, u.port, timeout=10)
    c.request("GET", u.path + "?" + u.query)
    r = c.getresponse()
    loc = r.getheader("Location")
    r.read()
    c.close()
    if not loc:
        return
    cb = urllib.parse.urlparse(loc.replace("//localhost:", "//127.0.0.1:"))
    if stray:    # a favicon request and a request with a foreign Host header must not end or poison the flow
        for path, host in (("/favicon.ico", None), ("/callback?code=a&state=b", "evil.example")):
            c = http.client.HTTPConnection(cb.hostname, cb.port, timeout=10)
            c.putrequest("GET", path, skip_host=bool(host))
            if host:
                c.putheader("Host", host)
            c.endheaders()
            r = c.getresponse()
            stray_results.append(r.status)
            r.read()
            c.close()
    c = http.client.HTTPConnection(cb.hostname, cb.port, timeout=10)
    c.request("GET", cb.path + "?" + cb.query)
    c.getresponse().read()
    c.close()


stray_results = []


class LoginBase(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="mrn")
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.home = os.path.join(self.tmp, "home")
        os.makedirs(self.home)
        self.fake = Fake()
        self.addCleanup(self.fake.stop)
        self.port = free_port()
        env = {"HOME": self.home, "USERPROFILE": self.home, "MREG_AUTH_URL": self.fake.base,
               "MREG_KEYS_URL": self.fake.base + "/keysvc", "MREG_REGISTRY": self.fake.base,
               "MREG_LOGIN_PORT": str(self.port), "MREG_CLIENT_ID": "test-client"}
        p = mock.patch.dict(os.environ, env)
        p.start()
        self.addCleanup(p.stop)
        os.environ.pop("MREG_TOKEN", None)
        self.opened = []
        self.stray = False
        o = mock.patch.object(M, "_open_browser", side_effect=self._open)
        o.start()
        self.addCleanup(o.stop)
        self.token_file = os.path.join(self.home, ".mreg", "token")

    def _open(self, url):
        self.opened.append(url)
        threading.Thread(target=play_browser, args=(url, self.stray), daemon=True).start()
        return True

    def run_main(self, *args):
        """(exit code, stdout, stderr, text of any SystemExit message). Runs M.main in-process with output captured."""
        out, err, code, msg = io.StringIO(), io.StringIO(), 0, ""
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            try:
                M.main(list(args))
            except SystemExit as e:
                if isinstance(e.code, str):
                    code, msg = 1, e.code
                else:
                    code = e.code or 0
        return code, out.getvalue(), err.getvalue(), msg

    def no_secrets(self, *texts):
        blob = "\n".join(texts)
        for s in self.fake.secrets_seen():
            self.assertNotIn(s, blob, "a secret value appeared in output or in an error message")

    def stored(self):
        if not os.path.exists(self.token_file):
            return None
        with open(self.token_file, encoding="ascii") as f:
            return f.read()

    def put_token(self, text):
        os.makedirs(os.path.dirname(self.token_file), exist_ok=True)
        with open(self.token_file, "w", encoding="ascii", newline="\n") as f:
            f.write(text)


class TestLogin(LoginBase):
    def test_flow_end_to_end(self):
        code, out, err, msg = self.run_main("login", "--label", "my laptop", "--timeout", "20")
        self.assertEqual((code, msg), (0, ""), out + err)
        # the authorize request: PKCE S256, state, public client, the registered callback, the scopes
        self.assertEqual(len(self.fake.authz), 1)
        q = self.fake.authz[0]
        self.assertEqual((q["response_type"], q["code_challenge_method"], q["scope"], q["client_id"]),
                         ("code", "S256", "openid email", "test-client"))
        self.assertEqual(q["redirect_uri"], f"http://localhost:{self.port}/callback")
        self.assertGreaterEqual(len(q["state"]), 24)
        self.assertNotIn("identity_provider", q)
        self.assertEqual(len(self.fake.token_reqs), 1)
        v = self.fake.token_reqs[0]["code_verifier"]
        self.assertGreaterEqual(len(v), 43)
        self.assertEqual(b64u(hashlib.sha256(v.encode()).digest()), q["code_challenge"])
        # the key: created with the label, verified against the registry, stored
        key = self.fake.keys[0]
        self.assertEqual(self.fake.created[0]["label"], "my laptop")
        self.assertIn(key, self.fake.reg_seen)
        self.assertEqual(self.stored(), key + "\n")
        self.assertFalse(os.path.exists(self.token_file + ".new"))
        # what is printed: key id and label, nothing secret
        self.assertIn(self.fake.created[0]["id"], out)
        self.assertIn("my laptop", out)
        self.no_secrets(out, err, msg)
        # the stored key works for whoami without network
        code, out2, err2, msg2 = self.run_main("whoami")
        self.assertEqual(code, 0)
        self.assertIn(self.fake.created[0]["id"], out2)
        self.no_secrets(out2, err2)

    def test_default_label_and_provider_flag(self):
        code, out, err, msg = self.run_main("login", "--provider", "GITHUB", "--timeout", "20")
        self.assertEqual((code, msg), (0, ""), out + err)
        self.assertEqual(self.fake.authz[0]["identity_provider"], "GitHub")
        self.assertTrue(self.fake.created[0]["label"].startswith("mreg on "))
        self.assertLessEqual(len(self.fake.created[0]["label"]), 64)

    def test_no_browser_prints_the_address(self):
        buf = io.StringIO()
        res = {}

        def worker():
            with contextlib.redirect_stdout(buf):
                try:
                    M.main(["login", "--no-browser", "--provider", "google", "--timeout", "20"])
                    res["code"] = 0
                except SystemExit as e:
                    res["code"] = e.code
        t = threading.Thread(target=worker)
        t.start()
        end = time.time() + 15
        url = None
        while time.time() < end and url is None:
            m = re.search(r"(http://127\.0\.0\.1:\d+/oauth2/authorize\?\S+)", buf.getvalue())
            url = m.group(1) if m else None
            time.sleep(0.05)
        self.assertIsNotNone(url, buf.getvalue())
        self.assertEqual(self.opened, [], "--no-browser must not open a browser")
        play_browser(url)
        t.join(20)
        self.assertEqual(res.get("code"), 0, buf.getvalue())
        self.assertEqual(self.fake.authz[0]["identity_provider"], "Google")
        self.assertIsNotNone(self.stored())

    def test_stray_requests_do_not_end_or_poison_the_flow(self):
        self.stray = True
        del stray_results[:]
        code, out, err, msg = self.run_main("login", "--timeout", "20")
        self.assertEqual((code, msg), (0, ""), out + err)
        self.assertEqual(stray_results, [404, 400])
        self.assertIsNotNone(self.stored())

    def test_state_mismatch_is_refused_before_anything_is_sent(self):
        self.fake.mode["authorize"] = "tamper"
        self.put_token("OLD-SHARED-TOKEN\n")
        code, out, err, msg = self.run_main("login", "--timeout", "20")
        self.assertEqual(code, 1)
        self.assertIn("state mismatch", msg)
        self.assertEqual(self.fake.token_reqs, [], "the code must not be exchanged after a state mismatch")
        self.assertEqual(self.fake.created, [])
        self.assertEqual(self.stored(), "OLD-SHARED-TOKEN\n")
        self.no_secrets(out, err, msg)

    def test_wrong_code_is_refused(self):
        self.fake.mode["token"] = "badcode"
        code, out, err, msg = self.run_main("login", "--timeout", "20")
        self.assertEqual(code, 1)
        self.assertIn("invalid_grant", msg)
        self.assertEqual(self.fake.created, [])
        self.assertIsNone(self.stored())
        self.no_secrets(out, err, msg)

    def test_denied_at_the_provider(self):
        self.fake.mode["authorize"] = "deny"
        code, out, err, msg = self.run_main("login", "--timeout", "20")
        self.assertEqual(code, 1)
        self.assertIn("not completed", msg)
        self.assertIn("access_denied", msg)
        self.assertIsNone(self.stored())

    def test_port_in_use(self):
        blocker = socket.socket()
        blocker.bind(("127.0.0.1", self.port))
        blocker.listen(1)
        self.addCleanup(blocker.close)
        code, out, err, msg = self.run_main("login", "--timeout", "5")
        self.assertEqual(code, 1)
        self.assertIn("cannot listen on 127.0.0.1:%d" % self.port, msg)
        self.assertEqual(self.opened, [], "no browser may be opened when the callback port is not ours")
        self.assertIsNone(self.stored())

    def test_browser_closed_times_out(self):
        self.fake.mode["authorize"] = "page"      # the browser opens but nobody ever signs in
        t0 = time.time()
        code, out, err, msg = self.run_main("login", "--timeout", "1")
        self.assertEqual(code, 1)
        self.assertIn("no sign-in response within 1 s", msg)
        self.assertLess(time.time() - t0, 15)
        self.assertIsNone(self.stored())
        # and the port is free again
        s = socket.socket()
        s.bind(("127.0.0.1", self.port))
        s.close()

    def test_key_limit_changes_nothing(self):
        self.fake.mode["keys"] = "limit"
        self.put_token("OLD\n")
        code, out, err, msg = self.run_main("login", "--timeout", "20")
        self.assertEqual(code, 1)
        self.assertIn("revoke one", msg)
        self.assertIn("mathregistry.com/account", msg)
        self.assertEqual(self.stored(), "OLD\n")
        self.no_secrets(out, err, msg)

    def test_registry_refusing_the_new_key_revokes_it_and_keeps_the_old_value(self):
        self.fake.mode["registry"] = "403"
        self.put_token("OLD\n")
        code, out, err, msg = self.run_main("login", "--timeout", "20")
        self.assertEqual(code, 1)
        self.assertIn("did not accept the new key", msg)
        self.assertIn("revoked again", msg)
        self.assertEqual(self.fake.deleted, [self.fake.created[0]["id"]])
        self.assertEqual(self.stored(), "OLD\n")
        self.assertFalse(os.path.exists(self.token_file + ".new"))
        self.no_secrets(out, err, msg)

    def test_unwritable_token_file_revokes_the_new_key(self):
        self.put_token("OLD\n")
        with mock.patch.object(M, "store_token", side_effect=PermissionError(13, "Permission denied")):
            code, out, err, msg = self.run_main("login", "--timeout", "20")
        self.assertEqual(code, 1)
        self.assertIn("cannot write", msg)
        self.assertIn("revoked again", msg)
        self.assertEqual(self.fake.deleted, [self.fake.created[0]["id"]])
        self.assertEqual(self.stored(), "OLD\n")
        self.no_secrets(out, err, msg)

    def test_old_value_is_replaced_only_by_a_verified_key(self):
        self.put_token("OLD\n")
        code, out, err, msg = self.run_main("login", "--timeout", "20")
        self.assertEqual((code, msg), (0, ""))
        self.assertEqual(self.stored(), self.fake.keys[0] + "\n")

    def test_bad_label_is_refused_before_a_browser_opens(self):
        for bad in ("", "x" * 65, "a<b", "tab\there"):
            code, out, err, msg = self.run_main("login", "--label", bad)
            self.assertEqual(code, 1, bad)
            self.assertIn("--label", msg)
        self.assertEqual(self.opened, [])

    def test_non_https_endpoint_is_refused(self):
        with mock.patch.dict(os.environ, {"MREG_AUTH_URL": "http://example.com"}):
            code, out, err, msg = self.run_main("login")
        self.assertEqual(code, 1)
        self.assertIn("MREG_AUTH_URL must be an https address", msg)
        self.assertEqual(self.opened, [])

    def test_login_needs_an_http_registry(self):
        with mock.patch.dict(os.environ, {"MREG_REGISTRY": pathlib.Path(self.tmp).as_uri()}):
            code, out, err, msg = self.run_main("login")
        self.assertEqual(code, 1)
        self.assertIn("needs an http(s) registry", msg)
        self.assertEqual(self.opened, [])

    @unittest.skipIf(sys.platform == "win32", "POSIX mode bits")
    def test_token_file_is_owner_only_on_posix(self):
        self.assertEqual(self.run_main("login", "--timeout", "20")[0], 0)
        self.assertEqual(os.stat(self.token_file).st_mode & 0o777, 0o600)
        self.assertEqual(os.stat(os.path.dirname(self.token_file)).st_mode & 0o077, 0)

    def test_store_token_leaves_no_temporary_file_and_overwrites(self):
        M.store_token("mreg_one")
        M.store_token("mreg_two")
        self.assertEqual(sorted(os.listdir(os.path.dirname(self.token_file))), ["token"])
        self.assertEqual(self.stored(), "mreg_two\n")


class TestLogoutWhoami(LoginBase):
    def login(self):
        self.assertEqual(self.run_main("login", "--timeout", "20")[0], 0)
        return self.fake.keys[-1], self.fake.created[-1]["id"]

    def test_logout_deletes_the_file_and_says_the_key_still_works(self):
        key, kid = self.login()
        code, out, err, msg = self.run_main("logout")
        self.assertEqual((code, msg), (0, ""))
        self.assertFalse(os.path.exists(self.token_file))
        self.assertIn(kid, out)
        self.assertIn("still works until it is revoked", out)
        self.assertIn("mathregistry.com/account", out)
        self.assertEqual(self.fake.deleted, [])
        self.no_secrets(out, err)
        self.assertEqual(self.run_main("logout")[0], 0)      # nothing stored: not an error

    def test_logout_revoke_signs_in_again_and_revokes(self):
        key, kid = self.login()
        self.opened.clear()
        code, out, err, msg = self.run_main("logout", "--revoke", "--timeout", "20")
        self.assertEqual((code, msg), (0, ""), out + err)
        self.assertEqual(len(self.opened), 1, "revoking needs a fresh sign-in")
        self.assertEqual(self.fake.deleted, [kid])
        self.assertFalse(os.path.exists(self.token_file))
        self.assertIn("revoked key " + kid, out)
        self.no_secrets(out, err, msg)

    def test_logout_revoke_keeps_the_file_when_the_service_does_not_know_the_key(self):
        key, kid = self.login()
        self.fake.mode["delete"] = "notfound"
        code, out, err, msg = self.run_main("logout", "--revoke", "--timeout", "20")
        self.assertEqual(code, 1)
        self.assertIn("not found under the account", msg)
        self.assertEqual(self.stored(), key + "\n")
        self.no_secrets(out, err, msg)

    def test_logout_revoke_refuses_the_shared_token(self):
        self.put_token("SHAREDTOKEN123\n")
        code, out, err, msg = self.run_main("logout", "--revoke")
        self.assertEqual(code, 1)
        self.assertIn("not a per-user key", msg)
        self.assertEqual(self.opened, [])
        self.assertEqual(self.stored(), "SHAREDTOKEN123\n")

    def test_logout_plain_on_the_shared_token(self):
        self.put_token("SHAREDTOKEN123\n")
        code, out, err, msg = self.run_main("logout")
        self.assertEqual(code, 0)
        self.assertFalse(os.path.exists(self.token_file))
        self.assertIn("not a per-user key", out)
        self.assertNotIn("SHAREDTOKEN123", out + err)

    def test_whoami_per_user_key(self):
        key = self.fake.mint("kAbCdEfGhIjK", owner="us-east-1:abc-def", iat=1789000000)
        self.put_token(key + "\n")
        code, out, err, msg = self.run_main("whoami")
        self.assertEqual((code, msg), (0, ""))
        for want in ("per-user key", "kAbCdEfGhIjK", "us-east-1:abc-def", "scope: read", "issued: 2026-09-10"):
            self.assertIn(want, out)
        self.assertNotIn(key, out + err)
        self.assertNotIn(key.split(".")[1], out + err)
        self.assertIn("file " + self.token_file, out)

    def test_whoami_from_the_environment_wins(self):
        self.put_token("SHAREDTOKEN123\n")
        key = self.fake.mint("kAbCdEfGhIjK")
        with mock.patch.dict(os.environ, {"MREG_TOKEN": key}):
            code, out, err, msg = self.run_main("whoami")
        self.assertEqual(code, 0)
        self.assertIn("MREG_TOKEN", out)
        self.assertIn("per-user key", out)
        self.assertNotIn(key, out)

    def test_whoami_shared_token_form(self):
        self.put_token("SHAREDTOKEN123\n")
        code, out, err, msg = self.run_main("whoami")
        self.assertEqual(code, 0)
        self.assertIn("old shared access token", out)
        self.assertIn("retired on 2026-11-12", out)
        self.assertNotIn("SHAREDTOKEN123", out + err)

    def test_whoami_garbage_and_damaged_and_empty(self):
        for text, want in (("not a token\twith spaces\n", "not recognised"), ("\x01\x02garbage\n", "not recognised"),
                           ("mreg_!!!.???\n", "damaged"), ("mreg_" + b64u(b"not json") + "." + "A" * 43 + "\n", "damaged"),
                           ("mreg_" + b64u(b'{"v":2,"k":"x","o":"y","s":"read","i":1}') + "." + "A" * 43 + "\n", "damaged"),
                           ("mreg_" + b64u(b'{"v":1,"k":"x","o":"y","s":"read","i":"1"}') + "." + "A" * 43 + "\n", "damaged")):
            self.put_token(text)
            code, out, err, msg = self.run_main("whoami")
            self.assertEqual(code, 1, text)
            self.assertIn(want, out, text)
            self.assertNotIn(text.strip(), out + err)
        os.remove(self.token_file)
        code, out, err, msg = self.run_main("whoami")
        self.assertEqual(code, 1)
        self.assertIn("no key stored", out)

    def test_whoami_makes_no_network_call(self):
        self.put_token(self.fake.mint("kAbCdEfGhIjK") + "\n")
        self.fake.stop()      # nothing is listening any more
        self.assertEqual(self.run_main("whoami")[0], 0)


# ======================================================================================= a registry in the registry's layout

def zst(raw):
    try:
        from compression import zstd as z
        return z.compress(raw, level=3)
    except ImportError:
        return subprocess.run(["zstd", "-3", "-q", "-c"], input=raw, capture_output=True, check=True).stdout


def jl(rows):
    return "".join(json.dumps(r, separators=(",", ":")) + "\n" for r in rows).encode("utf-8")


def tar_of(members):
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w", format=tarfile.GNU_FORMAT) as tf:
        for rel, data in members:
            ti = tarfile.TarInfo(rel)
            ti.size, ti.mtime, ti.mode, ti.type = len(data), 0, 0o644, tarfile.REGTYPE
            tf.addfile(ti, io.BytesIO(data))
    return buf.getvalue()


def decl(name, module, kind="theorem", **kw):
    return dict({"t": "decl", "name": name, "module": module, "kind": kind, "th": "%016x" % (hash(name) & (2**64 - 1)),
                 "tu": [], "vh": "0" * 16, "vu": [], "helper": False}, **kw)


def demo_decls():
    return [decl("Demo.A.t1", "Demo.A"), decl("Demo.B.t2", "Demo.B"), decl("Demo.C.t3", "Demo.C"), decl("Demo.D.t4", "Demo.D"),
            decl("Demo.dup", "Demo.A"), decl("Demo.dup", "Demo.D", "def"),
            decl("Demo.A.t1.proof_1", "Demo.A", helper=True, helper_why="proof"), decl("Demo.Ünï.t5", "Demo.A")]


def build_package(root, pid="acme/demo", lake="Demo", commit="a" * 40, decls=None, graph=True, train=TRAIN, version="1.0.0"):
    """Write one build of one package into the registry directory `root`. Modules A, B (imports A), C (imports B), D."""
    mods = [f"{lake}.{x}" for x in "ABCD"]
    imports = {mods[0]: [], mods[1]: [mods[0]], mods[2]: [mods[1]], mods[3]: []}
    bk = "b" + sha(pid.encode())[:15]
    base = pathlib.Path(root, "v1", "blobs", *pid.split("/"), "-", version, bk)
    (base / "shards").mkdir(parents=True)
    (base / "reports").mkdir()
    files = {}

    def put(rel, data):
        files[rel] = data
        (base / rel).write_bytes(data)

    groups = [(None, [(".lake/build/pkg.trace", f"trace of {pid}".encode() * 20)])]
    for m in mods:
        path = m.replace(".", "/")
        groups.append((m, [(f".lake/build/lib/lean/{path}.{ext}", f"{m}.{ext}:{commit}".encode() * 40) for ext in ("olean", "ilean")]))
    shard, frames, index, off, sname = b"", [], [], 0, "shards/part-00000.tar.zst"
    for m, members in groups:
        raw = tar_of(members)
        comp = zst(raw)
        frames.append({"shard": sname, "offset": off, "length": len(comp), "raw_length": len(raw), "module": m,
                       "files": len(members), "sha256": sha(comp)})
        for rel, data in members:
            index.append({"path": rel, "sha256": sha(data), "bytes": len(data), "shard": sname, "module": m})
        shard += comp
        off += len(comp)
    modules = [{"module": m, "shards": [sname], "imports": imports[m]} for m in mods]
    put(sname, shard)
    put("shards/index.jsonl", jl(index))
    put("shards/frames.jsonl", jl(frames))
    put("shards/modules.jsonl", jl(modules))
    put("shards/frames.jsonl.zst", zst(jl(frames)))
    put("shards/modules.jsonl.zst", zst(jl(modules)))
    reports = {}
    if graph:
        rows = ([{"t": "header", "schema": "mreg-graph/1", "hash": "mreg-expr-hash64-v1", "modules_listed": 4}]
                + [{"t": "module", "module": m, "imports": imports[m], "init": True} for m in mods] + (decls or []))
        put("reports/graph.jsonl.zst", zst(jl(rows)))
        reports["reports/graph.jsonl.zst"] = sha(files["reports/graph.jsonl.zst"])
    closure = [(lake, commit)]
    rk = M.resolve_key(TOOLCHAIN, closure, {})
    aux = {k: {"sha256": sha(v), "bytes": len(v)} for k, v in files.items() if k.startswith("shards/") and not k.startswith("shards/part-")}
    man = {"schema": "lean-build-manifest/2", "id": pid, "version": version, "package": lake, "commit": commit,
           "toolchain": TOOLCHAIN, "platform": PLAT, "build_key": bk, "resolve_key": rk, "closure": [list(c) for c in closure],
           "source_changes": None, "trains": [train] if train else [], "usable_on": [{"platform": PLAT, "basis": "g3"}],
           "modules_built": 4, "frames": len(frames),
           "shards": [{"name": sname, "sha256": sha(shard), "bytes": len(shard)}],
           "aux_files": dict(sorted(aux.items())), "reports": reports}
    mbytes = json.dumps(man, indent=1).encode()
    (base / "manifest.json").write_bytes(mbytes)
    entry = {"build_key": bk, "resolve_key": rk, "toolchain": TOOLCHAIN, "modules": 4, "bytes_compressed": len(shard),
             "trains": man["trains"], "usable_on": man["usable_on"], "gates": {"G1": "pass"}, "signed": False, "labels": [],
             "manifest": {"sha256": sha(mbytes), "bytes": len(mbytes)}, "log_n": 1}
    doc = {"id": pid, "lake_name": lake, "license": {"spdx": "Apache-2.0"}, "ownership": "unclaimed",
           "dist_tags": {"latest": version},
           "versions": {version: {"commit": commit, "committed_at": "2026-11-01T00:00:00Z", "version_from": "test", "builds": [entry]}}}
    dp = pathlib.Path(root, "v1", "index", *pid.split("/"))
    dp.parent.mkdir(parents=True, exist_ok=True)
    pathlib.Path(str(dp) + ".json").write_text(json.dumps(doc), encoding="utf-8")
    return {"id": pid, "lake": lake, "commit": commit, "version": version, "frames": frames, "man": man}


def build_registry(root, with_train=True):
    pk = {"demo": build_package(root, "acme/demo", "Demo", "a" * 40, demo_decls()),
          "nograph": build_package(root, "acme/nograph", "Nog", "c" * 40, graph=False)}
    if with_train:
        pkgs = {p["id"]: {"lake_name": p["lake"], "commit": p["commit"], "version": p["version"], "modules": 4,
                          "module_roots": [p["lake"]], "git": "https://github.com/" + p["id"]} for p in pk.values()}
        idx = pathlib.Path(root, "v1", "index", "trains")
        idx.mkdir(parents=True, exist_ok=True)
        (idx / (TRAIN + ".json")).write_text(json.dumps({"train": TRAIN, "toolchain": TOOLCHAIN, "state": "open", "packages": pkgs,
                                                          "pins": {}, "module_roots": {}, "mathlib": {"rev": "0" * 40}}))
        (idx.parent / "trains.json").write_text(json.dumps({"trains": [{"train": TRAIN}]}))
    return pk


def make_project(d, deps=(("acme/demo", "Demo", "a" * 40),), imports=("Demo.B",)):
    os.makedirs(d, exist_ok=True)
    pk = []
    for pid, name, commit in deps:
        os.makedirs(os.path.join(d, ".lake", "packages", name), exist_ok=True)
        pk.append({"url": f"https://github.com/{pid}", "type": "git", "rev": commit, "name": name,
                   "manifestFile": "lake-manifest.json", "inputRev": "main", "inherited": False, "configFile": "lakefile.toml"})
    with open(os.path.join(d, "lean-toolchain"), "w", newline="\n") as f:
        f.write(TOOLCHAIN + "\n")
    with open(os.path.join(d, "lake-manifest.json"), "w", newline="\n") as f:
        json.dump({"version": "1.1.0", "packagesDir": ".lake/packages", "name": "Proj", "lakeDir": ".lake", "packages": pk}, f)
    with open(os.path.join(d, "Proj.lean"), "w", newline="\n") as f:
        f.write("".join(f"import {i}\n" for i in imports))


class RegBase(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="mrn")
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.reg = os.path.join(self.tmp, "reg")
        self.home = os.path.join(self.tmp, "home")
        os.makedirs(self.home)
        self.pk = build_registry(self.reg)

    def run_cli(self, script, *args, cwd=None):
        env = dict(os.environ, MREG_REGISTRY=pathlib.Path(self.reg).as_uri(), MREG_KEYS=os.path.join(self.tmp, "pins.json"),
                   PYTHONIOENCODING="utf-8", HOME=self.home, USERPROFILE=self.home)
        env.pop("MREG_TOKEN", None)
        args = list(args)
        if script in (NEXT_PATH, BASE_PATH) and args[:1] and args[0] in ("install", "ci", "add") and "--allow-unverified" not in args:
            args.append("--allow-unverified")     # these fixtures are unsigned builds, refused by default since 0.5.0 (test_admission.py tests the refusal)
        r = subprocess.run([sys.executable, script] + (["-C", cwd] if cwd else []) + args, capture_output=True, text=True,
                           env=env, encoding="utf-8")
        return r.returncode, r.stdout + r.stderr

    def mreg(self, *args, cwd=None):
        return self.run_cli(NEXT_PATH, *args, cwd=cwd)

    def project(self, name="proj", **kw):
        d = os.path.join(self.tmp, name)
        make_project(d, **kw)
        return d

    def olean(self, proj, mod, pkg="Demo"):
        return os.path.join(proj, ".lake", "packages", pkg, ".lake", "build", "lib", "lean", *mod.split(".")) + ".olean"

    def lock(self, proj):
        with open(os.path.join(proj, "mreg.lock"), encoding="utf-8") as f:
            return json.load(f)


class TestDeclarations(RegBase):
    def test_install_by_declaration_is_module_level_and_minimal(self):
        proj = self.project()
        rc, out = self.mreg("install", "acme/demo#Demo.B.t2", "--no-lake-check", cwd=proj)
        self.assertEqual(rc, 0, out)
        self.assertTrue(os.path.exists(self.olean(proj, "Demo.A")) and os.path.exists(self.olean(proj, "Demo.B")))
        self.assertFalse(os.path.exists(self.olean(proj, "Demo.C")), "C is not in the cone of Demo.B.t2")
        self.assertFalse(os.path.exists(self.olean(proj, "Demo.D")))
        frames = self.pk["demo"]["frames"]
        size = sum(f["length"] for f in frames if f["module"] in ("Demo.A", "Demo.B", None))
        line = [l for l in out.splitlines() if l.startswith("note: module-level install for now")]
        self.assertEqual(len(line), 1, out)
        self.assertIn("1 declaration in 1 module need 2 modules, " + M.human_bytes(size) + " compressed, from 1 package", line[0])
        self.assertIn("no declaration-level bundles yet", line[0])
        # the lock records what was asked (the declaration) and what was installed (modules)
        lock = self.lock(proj)
        self.assertEqual(lock["schema"], "mreg-lock/1")
        self.assertEqual(lock["install_level"], "module")
        self.assertEqual(lock["targets"], ["Demo.B"])
        e = next(p for p in lock["packages"] if p["lake_name"] == "Demo")
        self.assertEqual(e["declarations"], [{"entry": "acme/demo#Demo.B.t2", "name": "Demo.B.t2", "module": "Demo.B",
                                              "kind": "theorem", "th": decl("Demo.B.t2", "Demo.B")["th"]}])
        self.assertEqual(e["modules"], ["Demo.A", "Demo.B"])

    def test_lock_round_trip_ci_restores_and_checks_the_graph(self):
        proj = self.project()
        self.assertEqual(self.mreg("install", "acme/demo#Demo.B.t2", "--no-lake-check", cwd=proj)[0], 0)
        for m in ("Demo.A", "Demo.B"):
            os.remove(self.olean(proj, m))
        os.remove(os.path.join(proj, ".lake", "mreg-state.json"))      # ci skips what the state file says is installed
        rc, out = self.mreg("ci", "--no-lake-check", cwd=proj)
        self.assertEqual(rc, 0, out)
        self.assertTrue(os.path.exists(self.olean(proj, "Demo.A")) and os.path.exists(self.olean(proj, "Demo.B")))
        self.assertFalse(os.path.exists(self.olean(proj, "Demo.C")))
        self.assertIn("note: module-level install for now", out)
        e = next(p for p in self.lock(proj)["packages"] if p["lake_name"] == "Demo")
        self.assertEqual([d["name"] for d in e["declarations"]], ["Demo.B.t2"], "ci keeps the declarations in the lock")
        # a lock whose recorded statement hash differs from the build's graph is refused
        lp = os.path.join(proj, "mreg.lock")
        lock = self.lock(proj)
        for p in lock["packages"]:
            for d in p.get("declarations", []):
                d["th"] = "f" * 16
        with open(lp, "w") as f:
            json.dump(lock, f)
        rc, out = self.mreg("ci", "--no-lake-check", cwd=proj)
        self.assertEqual(rc, 1)
        self.assertIn("the locked build's graph says module Demo.B", out)

    def test_declarations_in_mreg_json_join_the_default_install(self):
        proj = self.project()
        with open(os.path.join(proj, "mreg.json"), "w") as f:
            json.dump({"registry": "x", "train": TRAIN, "declarations": ["acme/demo#Demo.D.t4"]}, f)
        rc, out = self.mreg("install", "--no-lake-check", cwd=proj)
        self.assertEqual(rc, 0, out)
        self.assertTrue(os.path.exists(self.olean(proj, "Demo.D")), "the recorded declaration's module is installed")
        self.assertTrue(os.path.exists(self.olean(proj, "Demo.B")), "and so is what the project's own imports need")
        self.assertFalse(os.path.exists(self.olean(proj, "Demo.C")))
        self.assertEqual(self.lock(proj)["targets"], ["Demo.B", "Demo.D"])

    def test_unicode_name(self):
        proj = self.project()
        rc, out = self.mreg("install", "acme/demo#Demo.Ünï.t5", "--no-lake-check", cwd=proj)
        self.assertEqual(rc, 0, out)
        self.assertTrue(os.path.exists(self.olean(proj, "Demo.A")))

    def test_dry_run_prints_the_line_and_writes_nothing(self):
        proj = self.project()
        rc, out = self.mreg("install", "acme/demo#Demo.B.t2", "--dry-run", cwd=proj)
        self.assertEqual(rc, 0, out)
        self.assertIn("note: module-level install for now", out)
        self.assertFalse(os.path.exists(os.path.join(proj, "mreg.lock")))
        self.assertFalse(os.path.exists(self.olean(proj, "Demo.A")))

    def assert_refused(self, proj, entry, needle):
        rc, out = self.mreg("install", entry, "--no-lake-check", cwd=proj)
        self.assertEqual(rc, 1, out)
        self.assertIn(needle, out)
        self.assertFalse(os.path.exists(os.path.join(proj, "mreg.lock")), "a refusal writes no lock")
        self.assertFalse(os.path.exists(self.olean(proj, "Demo.A")), "a refusal installs nothing")

    def test_errors(self):
        proj = self.project(deps=(("acme/demo", "Demo", "a" * 40), ("acme/nograph", "Nog", "c" * 40)))
        self.assert_refused(proj, "acme/demo#Demo.A.t9", "no declaration named 'Demo.A.t9'")
        self.assert_refused(proj, "acme/demo#t1", "did you mean Demo.A.t1")
        self.assert_refused(proj, "acme/demo#Demo.dup", "is ambiguous: defined in Demo.A, Demo.D")
        self.assert_refused(proj, "acme/demo#Demo.A.t1.proof_1", "generated helper (proof)")
        self.assert_refused(proj, "acme/nograph#Nog.X", "has no declaration graph")
        self.assert_refused(proj, "acme/other#X", "no registry build of acme/other")
        self.assert_refused(proj, "acme/demo#", "expected owner/pkg#Decl.name")
        self.assert_refused(proj, "#Demo.A.t1", "expected owner/pkg#Decl.name")

    def test_a_graph_that_does_not_match_the_manifest_is_refused(self):
        p = self.pk["demo"]
        gp = pathlib.Path(self.reg, "v1", "blobs", "acme", "demo", "-", p["version"], p["man"]["build_key"], "reports", "graph.jsonl.zst")
        data = bytearray(gp.read_bytes())
        data[len(data) // 2] ^= 1
        gp.write_bytes(bytes(data))
        self.assert_refused(self.project(), "acme/demo#Demo.B.t2", "does not match the manifest's SHA-256")

    def test_parse_decl(self):
        self.assertEqual(M.parse_decl("acme/demo#Demo.B.t2"), ("acme/demo", "Demo.B.t2"))
        self.assertEqual(M.parse_decl("a/b/sub#x'"), ("a/b/sub", "x'"))
        for bad in ("acme/demo", "acme#x", "acme/demo#", "#x", "acme/demo# x", "acme/demo#a#b", ""):
            self.assertIsNone(M.parse_decl(bad), bad)


class TestAdd(RegBase):
    def lakefile(self, d):
        with open(os.path.join(d, "lakefile.toml"), "w", newline="\n") as f:
            f.write('name = "Proj"\n')

    def test_add_records_the_declaration_and_the_require(self):
        proj = self.project()
        self.lakefile(proj)
        rc, out = self.mreg("add", "acme/demo#Demo.B.t2", "--no-lake-update", cwd=proj)
        self.assertEqual(rc, 0, out)
        self.assertIn("theorem defined in module Demo.B", out)
        self.assertIn("lake update skipped", out)
        self.assertIn('name = "Demo"', pathlib.Path(proj, "lakefile.toml").read_text())
        cfg = json.loads(pathlib.Path(proj, "mreg.json").read_text())
        self.assertEqual(cfg, {"registry": pathlib.Path(self.reg).as_uri(), "train": TRAIN, "declarations": ["acme/demo#Demo.B.t2"]})
        # adding again (and another one) keeps the list without duplicates; the package is already required
        rc, out = self.mreg("add", "acme/demo#Demo.B.t2", "acme/demo#Demo.D.t4", "--no-lake-update", cwd=proj)
        self.assertEqual(rc, 0, out)
        self.assertIn("already required", out)
        self.assertEqual(json.loads(pathlib.Path(proj, "mreg.json").read_text())["declarations"],
                         ["acme/demo#Demo.B.t2", "acme/demo#Demo.D.t4"])

    def test_add_a_plain_package_is_unchanged(self):
        proj = self.project()
        self.lakefile(proj)
        rc, out = self.mreg("add", "acme/demo", "--no-lake-update", cwd=proj)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.exists(os.path.join(proj, "mreg.json")), "no declaration, no mreg.json")

    def test_add_with_an_unknown_declaration_changes_nothing(self):
        proj = self.project()
        self.lakefile(proj)
        for entry, needle in (("acme/demo#Demo.nope", "no declaration named"), ("acme/nograph#X", "has no declaration graph"),
                              ("acme/zzz#X", "is not on train"), ("acme/demo#", "expected")):
            rc, out = self.mreg("add", entry, "--no-lake-update", cwd=proj)
            self.assertEqual(rc, 1, out)
            self.assertIn(needle, out)
        self.assertEqual(pathlib.Path(proj, "lakefile.toml").read_text(), 'name = "Proj"\n')
        self.assertFalse(os.path.exists(os.path.join(proj, "mreg.json")))


class TestLockCompatibility(RegBase):
    def test_install_without_declarations_still_writes_lock_0(self):
        proj = self.project()
        rc, out = self.mreg("install", "--no-lake-check", cwd=proj)
        self.assertEqual(rc, 0, out)
        lock = self.lock(proj)
        self.assertEqual(lock["schema"], "mreg-lock/0")
        self.assertNotIn("install_level", lock)
        self.assertNotIn("declarations", json.dumps(lock))
        self.assertNotIn("note: module-level", out)

    def test_old_lock_files_load(self):
        proj = self.project()
        self.assertEqual(self.mreg("install", "--no-lake-check", cwd=proj)[0], 0)
        os.remove(self.olean(proj, "Demo.A"))
        os.remove(os.path.join(proj, ".lake", "mreg-state.json"))
        rc, out = self.mreg("ci", "--no-lake-check", cwd=proj)
        self.assertEqual(rc, 0, out)
        self.assertTrue(os.path.exists(self.olean(proj, "Demo.A")))
        self.assertEqual(self.lock(proj)["schema"], "mreg-lock/0", "ci on a /0 lock writes /0 back")

    def test_unknown_lock_schema_is_refused(self):
        proj = self.project()
        self.assertEqual(self.mreg("install", "--no-lake-check", cwd=proj)[0], 0)
        lock = self.lock(proj)
        lock["schema"] = "mreg-lock/9"
        with open(os.path.join(proj, "mreg.lock"), "w") as f:
            json.dump(lock, f)
        rc, out = self.mreg("ci", "--no-lake-check", cwd=proj)
        self.assertEqual(rc, 1)
        self.assertIn("unknown lock schema", out)

    def test_the_live_client_reads_a_lock_without_declarations_written_by_the_copy(self):
        proj = self.project()
        self.assertEqual(self.mreg("install", "--no-lake-check", cwd=proj)[0], 0)
        rc, out = self.run_cli(BASE_PATH, "ci", "--no-lake-check", cwd=proj)
        self.assertEqual(rc, 0, out)


class TestTamperAndVerify(RegBase):
    """A changed installed file is caught by `install --check`, `ci` and `verify`; `verify` on nothing fails; `verify --json`
    writes one JSON document on stdout; the key-pin note goes to stderr."""

    def installed(self):
        proj = self.project()
        rc, out = self.mreg("install", "--no-lake-check", cwd=proj)
        self.assertEqual(rc, 0, out)
        return proj

    def flip(self, path):
        with open(path, "rb") as f:
            data = bytearray(f.read())
        orig = bytes(data)
        data[len(data) // 2] ^= 0x01
        with open(path, "wb") as f:
            f.write(bytes(data))
        return orig

    def test_install_check_and_ci_fail_on_a_flipped_byte_and_pass_when_restored(self):
        proj = self.installed()
        target = self.olean(proj, "Demo.B")
        orig = self.flip(target)
        for args in (("install", "--check", "--no-lake-check"), ("ci", "--no-lake-check")):
            rc, out = self.mreg(*args, cwd=proj)
            self.assertEqual(rc, 1, (args, out))
            self.assertIn("MISMATCH Demo: .lake/build/lib/lean/Demo/B.olean", out)
            self.assertNotIn("re-hashed the installed files", out)
        self.assertEqual(self.mreg("verify", cwd=proj)[0], 1)
        with open(target, "wb") as f:
            f.write(orig)
        for args in (("install", "--check", "--no-lake-check"), ("ci", "--no-lake-check"), ("verify",)):
            rc, out = self.mreg(*args, cwd=proj)
            self.assertEqual(rc, 0, (args, out))
        rc, out = self.mreg("ci", "--no-lake-check", cwd=proj)
        self.assertIn("re-hashed the installed files: ", out)
        self.assertNotIn("MISMATCH", out)

    def test_a_missing_installed_file_fails_too(self):
        proj = self.installed()
        os.remove(self.olean(proj, "Demo.A"))
        for args in (("install", "--check", "--no-lake-check"), ("ci", "--no-lake-check")):
            rc, out = self.mreg(*args, cwd=proj)
            self.assertEqual(rc, 1, (args, out))
            self.assertIn("MISMATCH Demo: .lake/build/lib/lean/Demo/A.olean", out)

    def test_verify_on_an_empty_project_fails(self):
        proj = self.project()
        rc, out = self.mreg("verify", cwd=proj)
        self.assertEqual(rc, 1, out)
        self.assertIn("nothing to verify: no .lake/mreg-state.json", out)
        self.assertNotIn("0 of 0", out)
        rc, out = self.mreg("verify", "--json", cwd=proj)       # also with --json: one document, still a failure
        self.assertEqual(rc, 1)
        rc, out = self.run_cli(NEXT_PATH, "verify", "--json", cwd=proj)
        doc = json.loads(out[:out.rindex("}") + 1])
        self.assertFalse(doc["ok"])
        # a state file that lists nothing checks nothing either
        os.makedirs(os.path.join(proj, ".lake"), exist_ok=True)
        with open(os.path.join(proj, ".lake", "mreg-state.json"), "w") as f:
            json.dump({"packages": {}}, f)
        rc, out = self.mreg("verify", cwd=proj)
        self.assertEqual(rc, 1, out)
        self.assertIn("nothing to verify", out)

    def stdout_stderr(self, *args, cwd):
        env = dict(os.environ, MREG_REGISTRY=pathlib.Path(self.reg).as_uri(), MREG_KEYS=os.path.join(self.tmp, "pins.json"),
                   PYTHONIOENCODING="utf-8", HOME=self.home, USERPROFILE=self.home)
        env.pop("MREG_TOKEN", None)
        r = subprocess.run([sys.executable, NEXT_PATH, "-C", cwd] + list(args), capture_output=True, text=True, env=env, encoding="utf-8")
        return r.returncode, r.stdout, r.stderr

    def test_verify_json_is_one_document_for_a_module_level_project(self):
        proj = self.installed()
        rc, out, err = self.stdout_stderr("verify", "--json", cwd=proj)
        self.assertEqual(rc, 0, err)
        doc = json.loads(out)                         # the whole of stdout is one JSON document
        self.assertTrue(doc["ok"])
        self.assertGreater(doc["files"], 0)
        self.assertEqual(doc["mismatched"], [])
        self.assertIn("hashes matched:", err)
        self.flip(self.olean(proj, "Demo.B"))
        rc, out, err = self.stdout_stderr("verify", "--json", cwd=proj)
        self.assertEqual(rc, 1)
        doc = json.loads(out)
        self.assertFalse(doc["ok"])
        self.assertEqual(doc["mismatched"], ["Demo: .lake/build/lib/lean/Demo/B.olean"])
        self.assertIn("MISMATCH Demo: .lake/build/lib/lean/Demo/B.olean", err)

    def test_verify_json_with_both_locks_is_one_document(self):
        proj = self.installed()
        with open(os.path.join(proj, "mreg-chunks.lock.json"), "w") as f:
            json.dump({"schema": M.CHUNK_LOCK_SCHEMA, "chunk_dir": ".lake/mreg-chunks", "chunks": [], "train": TRAIN,
                       "build": "b1", "variant": "checking"}, f)
        rc, out, err = self.stdout_stderr("verify", "--json", cwd=proj)
        self.assertEqual(rc, 0, err)
        doc = json.loads(out)
        self.assertEqual(doc["schema"], M.NI_SCHEMA)
        self.assertTrue(doc["ok"])
        self.assertTrue(doc["module_level"]["ok"])
        self.flip(self.olean(proj, "Demo.A"))
        rc, out, err = self.stdout_stderr("verify", "--json", cwd=proj)
        self.assertEqual(rc, 1)
        doc = json.loads(out)
        self.assertFalse(doc["ok"])
        self.assertEqual(doc["module_level"]["mismatched"], ["Demo: .lake/build/lib/lean/Demo/A.olean"])

    def test_the_pin_note_goes_to_stderr(self):
        import types
        pins = os.path.join(self.tmp, "own-pins.json")
        reg = types.SimpleNamespace(base="https://example.invalid", accept_new_key=False)
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.dict(os.environ, {"MREG_KEYS": pins}), contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            self.assertIsNone(M.pin_key(reg, "f4ac93fa070519ea"))
        self.assertEqual(out.getvalue(), "")
        self.assertIn("note: pinned signing key f4ac93fa070519ea", err.getvalue())
        with mock.patch.dict(os.environ, {"MREG_KEYS": pins}), contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            self.assertIn("not one pinned", M.pin_key(reg, "0000000000000000"))      # a DIFFERENT key later is refused
        self.assertEqual(out.getvalue(), "")


class TestNoRegression(RegBase):
    """The existing commands, run by the live client and by the copy against the same file:/// registry."""

    def norm(self, text, *dirs):
        for d in dirs:
            text = text.replace(d, "<proj>")
        text = re.sub(r"in \d+ s ", "in N s ", text)
        text = re.sub(r"with \d+ requests", "with N requests", text)
        text = re.sub(r"nothing written; \d+ requests so far", "nothing written; N requests so far", text)     # 0.5.0: admission reads the audit records       # ci and install --check re-fetch the manifest and index to re-hash
        # The copy's human summaries say "hashes matched ... not a check of proofs"; the live client still says "verified".
        # Both are mapped to the same token, keeping the numbers, so the comparison still covers the counts.
        text = re.sub(r"^re-hashed the installed files: .*\n?", "", text, flags=re.M)     # added by the tamper fix (ci, install --check)
        text = re.sub(r"every frame matched its SHA-256|every frame's SHA-256 matched the registry's recorded hash \(not a check of proofs\)",
                      "<frames-hash-note>", text)
        text = re.sub(r"^verified (\d+) files of (\d+) packages against the registry: (\d+) compiled-file mismatches, (\d+) bookkeeping files rewritten locally$",
                      lambda m: f"<verify n={m[1]} packages={m[2]} bad={m[3]} book={m[4]}>", text, flags=re.M)
        text = re.sub(r"^hashes matched: (\d+) of (\d+) files of (\d+) packages equal .*?: (\d+) compiled-file mismatches, (\d+) bookkeeping files rewritten locally$",
                      lambda m: f"<verify n={m[2]} packages={m[3]} bad={m[4]} book={m[5]}>", text, flags=re.M)
        # 0.4.0 additions: `view` ends each build line with labels and signed/unsigned; `audit --lenient` prints a warning on stderr
        text = re.sub(r"  labels=\S+  (?:signed|unsigned: no registry gate record)$", "", text, flags=re.M)
        text = re.sub(r"^warning: --lenient is on\..*\n?", "", text, flags=re.M)
        text = re.sub(r"^\s*UNVERIFIED:.*\n?", "", text, flags=re.M)          # 0.5.0: admission banner and per-package status lines (copy only)
        text = re.sub(r"^status \S+ \S+: downloaded=.*\n?", "", text, flags=re.M)
        text = re.sub(r"^audited (\d+) builds: (\d+) verified, (\d+) failed(.*)$",
                      lambda m: f"<audit builds={m[1]} ok={m[2]} bad={m[3]}>{m[4]}", text, flags=re.M)
        text = re.sub(r"^audit: (\d+) of (\d+) builds with consistent signature, reports and log; (\d+) without \(.*?\)( \(required: .*\))?$",
                      lambda m: f"<audit builds={m[2]} ok={m[1]} bad={m[3]}>{m[4] or ''}", text, flags=re.M)
        return text

    def both(self, args, setup=None, projname="p"):
        res = []
        for tag, script in (("base", BASE_PATH), ("next", NEXT_PATH)):
            d = self.project(f"{projname}-{tag}")
            if setup:
                setup(d)
            rc, out = self.run_cli(script, *args, cwd=d)
            res.append((rc, self.norm(out, d), d))
        return res

    def test_view_train_install_ci_audit_verify_are_identical(self):
        for args in (["view", "acme/demo"], ["view", "acme/missing"], ["train"], ["train", "nope"]):
            (rb, ob, _), (rn, on, _) = self.both(args)
            self.assertEqual((rb, ob), (rn, on), args)
        (rb, ob, db), (rn, on, dn) = self.both(["install", "--no-lake-check"])
        self.assertEqual((rb, ob), (rn, on))
        self.assertEqual(rb, 0, ob)
        lb, ln = self.lock(db), self.lock(dn)
        lb.pop("generated_at"), ln.pop("generated_at")
        self.assertEqual(lb, ln)
        for args in (["ci", "--no-lake-check"], ["audit"], ["verify"], ["install", "Demo.B", "--no-lake-check"],
                     ["install", "--dry-run"], ["install", "--all", "--no-lake-check"]):
            out = {}
            for tag, script, d in (("base", BASE_PATH, db), ("next", NEXT_PATH, dn)):
                # 0.4.0: audit is strict by default; the comparison with the live client is of the old behaviour, so `--lenient`
                rc, o = self.run_cli(script, *(args + ["--lenient"] if args == ["audit"] else args), cwd=d)
                out[tag] = (rc, self.norm(o, db, dn))
            self.assertEqual(out["base"], out["next"], args)
        # audit on this unsigned registry reports problems (rc 1) in both: same text
        for script, d in ((BASE_PATH, db), (NEXT_PATH, dn)):
            rc, o = self.run_cli(script, "audit", cwd=d)
            self.assertEqual(rc, 1, o)
            self.assertIn("audit (strict)", o)


if __name__ == "__main__":
    unittest.main(verbosity=1)
