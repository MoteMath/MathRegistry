#!/usr/bin/env python3
"""T-C4 tests: how mreg/next/mreg.py answers HTTP 451, 429/503 with Retry-After, and the optional response header x-mreg-denial.

    python -I test_statuses.py

A local mock HTTP server on 127.0.0.1 answers a script of (status, headers) first and then serves a synthetic registry from a directory.
Stdlib only, no network beyond localhost, no Lean. Needs Python 3.14 (compression.zstd) for the synthetic registry, as test_named_import.py.

The table the tests pin (named-import commands; the legacy commands `view`, `train`, `install` die with the same message, exit 1):

  response                                   retries   exit code / kind            message
  451                                        none      17 missing_object           "451 ... taken down ... nothing was retried"; error.http_status 451
  403/401/405 + x-mreg-denial: bad_signature none      13 auth                     message names the signature; error.denial, error.http_status
  403 + revoked / owner_blocked              none      13 auth                     message names revoked / owner blocked
  405 + method_not_allowed                   none      1  error                    message names the method
  403 without the header, or with an unknown value     13 auth                     the message the client had before (token missing, wrong or revoked)
  429 / 503 with Retry-After                 retries   after the retries: 16       sleeps min(Retry-After, RETRY_AFTER_CAP=30) seconds, not the backoff
  429 / 503 without Retry-After                        as before                   the backoff
"""
import http.server, importlib.util, json, os, shutil, sys, threading, unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import test_named_import as T       # noqa: E402  (its Mirror builds the synthetic registry; its Base gives run_cli with schema validation)

M = T.M
ENTRY = f"{T.MATHLIB}#Mathlib.n60_0"


class _Srv(http.server.ThreadingHTTPServer):
    daemon_threads = True


def serve(root, script=(), token="tok"):
    """script: [(status, {header: value})] consumed one per request, in order; afterwards the directory `root` is served (token checked)."""
    log, todo, lock = [], list(script), threading.Lock()

    class H(http.server.BaseHTTPRequestHandler):
        def log_message(self, *a):
            pass

        def do_GET(self):
            log.append(self.path)
            with lock:
                step = todo.pop(0) if todo else None
            if step is not None:
                st, hd = step
                self.send_response(st)
                for k, v in hd.items():
                    self.send_header(k, v)
                self.send_header("Content-Length", "0")
                self.end_headers()
                return
            if self.headers.get("x-mreg-token") != token:
                self.send_response(403); self.send_header("Content-Length", "0"); self.end_headers(); return
            p = os.path.join(root, *self.path.split("/"))
            if not os.path.isfile(p):
                self.send_response(404); self.send_header("Content-Length", "0"); self.end_headers(); return
            b = open(p, "rb").read()
            self.send_response(200)
            self.send_header("Content-Length", str(len(b)))
            self.end_headers()
            self.wfile.write(b)
    srv = _Srv(("127.0.0.1", 0), H)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    return srv, log


@unittest.skipIf(T._zstd is None, "needs Python 3.14 compression.zstd")
class Statuses(T.Base):
    def go(self, script, entry=ENTRY, retries="1", cmd="add", extra=("--allow-unverified",)):
        self.m = self.m if hasattr(self, "m") and self.m else None
        srv, log = serve(self.reg, script)
        self.addCleanup(srv.shutdown)
        env = {"MREG_REGISTRY": f"http://127.0.0.1:{srv.server_address[1]}", "MREG_TOKEN": "tok", "MREG_RETRIES": retries}
        sleeps = []
        with mock.patch.object(M.time, "sleep", lambda s: sleeps.append(s)):
            r = self.run_cli(cmd, entry, *extra, env=env)
        return r, log, sleeps

    def setUp(self):
        super().setUp()
        self.m = self.mirror()

    # ---- 451
    def test_451_is_a_takedown_without_retries(self):
        for hd in ({}, {"Retry-After": "5"}):
            (c, js, o, e), log, sleeps = self.go([(451, hd)] * 10, retries="3")
            self.assertEqual((c, js["error"]["kind"], js["error"]["exit_code"]), (17, "missing_object", 17))
            self.assertEqual(js["error"]["http_status"], 451)
            self.assertIn("taken down", js["error"]["message"])
            self.assertIn("nothing was retried", js["error"]["message"])
            self.assertEqual(len(log), 1, "no second request after a 451")
            self.assertEqual(sleeps, [])

    # ---- x-mreg-denial
    def test_denial_header_chooses_the_message_and_stops_retries(self):
        for kind, status, code, ek, word in (("bad_signature", 403, 13, "auth", "signature"), ("revoked", 403, 13, "auth", "revoked"),
                                             ("owner_blocked", 403, 13, "auth", "blocked"),
                                             ("method_not_allowed", 405, 1, "error", "method")):
            (c, js, o, e), log, sleeps = self.go([(status, {M.DENIAL_HEADER: kind})] * 10, retries="3")
            self.assertEqual((c, js["error"]["kind"]), (code, ek), kind)
            self.assertEqual((js["error"]["denial"], js["error"]["http_status"]), (kind, status))
            self.assertIn(word, js["error"]["message"])
            self.assertNotIn("tok", js["error"]["message"].replace("token", ""))
            self.assertEqual(len(log), 1, kind)
            self.assertEqual(sleeps, [])

    def test_header_absent_or_unknown_behaves_as_before(self):
        for hd in ({}, {M.DENIAL_HEADER: "something_else"}, {M.DENIAL_HEADER: ""}):
            (c, js, o, e), log, sleeps = self.go([(403, hd)] * 10, retries="3")
            self.assertEqual((c, js["error"]["kind"]), (13, "auth"))
            self.assertIn("the token is missing, wrong or revoked", js["error"]["message"])
            self.assertNotIn("denial", js["error"])
            self.assertNotIn("http_status", js["error"])
            self.assertEqual(len(log), 1)

    def test_denial_name_is_one_constant(self):
        self.assertEqual(M.DENIAL_HEADER, "x-mreg-denial")
        with mock.patch.object(M, "DENIAL_HEADER", "x-other-name"):
            (c, js, o, e), log, sleeps = self.go([(403, {"x-other-name": "revoked"})] * 3)
        self.assertEqual(js["error"]["denial"], "revoked")

    # ---- Retry-After
    def test_retry_after_is_honoured_on_429_and_503(self):
        for st in (429, 503):
            (c, js, o, e), log, sleeps = self.go([(st, {"Retry-After": "2"})], retries="2")
            self.assertEqual(c, 0, (o, e))
            self.assertEqual(sleeps, [2.0], st)         # waited what the server said, instead of the backoff (0 here)

    def test_retry_after_is_capped(self):
        self.assertEqual(M.RETRY_AFTER_CAP, 30.0)
        (c, js, o, e), log, sleeps = self.go([(429, {"Retry-After": "86400"})] * 5, retries="2")
        self.assertEqual((c, js["error"]["kind"]), (16, "network"))
        self.assertEqual(sleeps, [30.0, 30.0])           # two retries, each at most the cap
        self.assertEqual(len(log), 3)

    def test_retry_after_http_date_and_garbage(self):
        import email.utils, time
        h = lambda v: type("H", (), {"get": lambda self, k, d=None: v})()
        self.assertEqual(M.retry_after_of(h("7")), 7.0)
        self.assertEqual(M.retry_after_of(h("0")), 0.0)
        self.assertIsNone(M.retry_after_of(h("soon")))
        self.assertIsNone(M.retry_after_of(h("")))
        self.assertIsNone(M.retry_after_of(h(None)))
        self.assertEqual(M.retry_after_of(h("-5")), None)
        d = email.utils.formatdate(time.time() + 3600, usegmt=True)
        self.assertEqual(M.retry_after_of(h(d)), 30.0)
        d = email.utils.formatdate(time.time() - 3600, usegmt=True)
        self.assertEqual(M.retry_after_of(h(d)), 0.0)

    def test_without_retry_after_the_old_backoff_applies(self):
        (c, js, o, e), log, sleeps = self.go([(503, {})], retries="2")
        self.assertEqual(c, 0)
        self.assertEqual(sleeps, [0.0])                  # MREG_BACKOFF=0 in these tests: backoff * attempt

    def test_other_5xx_keep_the_backoff_even_with_retry_after(self):
        (c, js, o, e), log, sleeps = self.go([(500, {"Retry-After": "9"})], retries="2")
        self.assertEqual(c, 0)
        self.assertEqual(sleeps, [0.0])

    # ---- the ranged reads
    def test_range_reads(self):
        srv, log = serve(self.reg, [(451, {}), (403, {M.DENIAL_HEADER: "revoked"}), (503, {"Retry-After": "4"}), (503, {})])
        self.addCleanup(srv.shutdown)
        with mock.patch.dict(os.environ, {"MREG_REGISTRY": f"http://127.0.0.1:{srv.server_address[1]}", "MREG_TOKEN": "tok"}):
            f = M.Fetcher()
            with self.assertRaises(M.NIError) as cm:
                f.open_range("/x/a", 0, 10, 100)
            self.assertEqual((cm.exception.kind, cm.exception.extra["http_status"]), ("missing_object", 451))
            with self.assertRaises(M.NIError) as cm:
                f.open_range("/x/a", 0, 10, 100)
            self.assertEqual((cm.exception.kind, cm.exception.extra["denial"]), ("auth", "revoked"))
            with self.assertRaises(M.RangeError) as cm:
                f.open_range("/x/a", 0, 10, 100)
            self.assertEqual((cm.exception.kind, cm.exception.retry, cm.exception.retry_after), ("status", True, 4.0))
            with self.assertRaises(M.RangeError) as cm:
                f.open_range("/x/a", 0, 10, 100)
            self.assertEqual((cm.exception.retry, cm.exception.retry_after), (True, None))

    # ---- the legacy client path (view, train, install)
    def test_legacy_registry_get(self):
        for script, word, n in (([(451, {})] * 9, "taken down", 1), ([(403, {M.DENIAL_HEADER: "owner_blocked"})] * 9, "blocked", 1),
                                ([(403, {})] * 9, "token is missing, wrong or revoked", 1)):
            srv, log = serve(self.reg, script)
            self.addCleanup(srv.shutdown)
            with mock.patch.dict(os.environ, {"MREG_REGISTRY": f"http://127.0.0.1:{srv.server_address[1]}", "MREG_TOKEN": "tok"}):
                with mock.patch.object(M.time, "sleep", lambda s: None):
                    with self.assertRaises(SystemExit) as cm:
                        M.Registry().get("/v1/index/trains.json")
            self.assertIn(word, str(cm.exception))
            self.assertEqual(len(log), n)
        srv, log = serve(self.reg, [(429, {"Retry-After": "3"}), (503, {"Retry-After": "99999"})])
        self.addCleanup(srv.shutdown)
        sleeps = []
        with mock.patch.dict(os.environ, {"MREG_REGISTRY": f"http://127.0.0.1:{srv.server_address[1]}", "MREG_TOKEN": "tok"}):
            with mock.patch.object(M.time, "sleep", lambda s: sleeps.append(s)):
                body = M.Registry().get("/v1/index/trains.json")
        self.assertEqual(sleeps, [3.0, 30.0])
        self.assertTrue(body.startswith(b"{"))

    # ---- the JSON schema allows the extra fields
    def test_json_error_document_still_validates(self):
        (c, js, o, e), log, sleeps = self.go([(451, {})])
        T.validate(js)       # run_cli validated it too: kind in EXIT, exit_code equal, message a string; unknown fields are allowed there
        self.assertGreaterEqual(set(js["error"]), {"kind", "exit_code", "message", "http_status"})


if __name__ == "__main__":
    unittest.main(verbosity=1)
