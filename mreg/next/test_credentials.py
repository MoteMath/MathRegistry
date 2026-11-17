#!/usr/bin/env python3
"""T-C5: where a credential may come from, that it never appears in any output, and `mreg doctor`.

No network beyond 127.0.0.1 (a local mock registry), no Lean, no lake: `doctor` runs against stub executables on a temporary PATH.
Run: python -I test_credentials.py
"""
import base64, http.server, json, os, re, shutil, subprocess, sys, tempfile, threading, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
MREG = os.path.join(HERE, "mreg.py")
WIN = sys.platform == "win32"

PAYLOAD = base64.urlsafe_b64encode(json.dumps({"v": 1, "k": "kQWERTYUIOP", "o": "owner-fake", "s": "read", "i": 1700000000}).encode()).decode().rstrip("=")
SIG = "Zx9Qw3Er5Ty7Ui1Op0As2Df4Gh6Jk8Lm_nBvCxZq-pL"[:43].ljust(43, "A")
FAKE_KEY = f"mreg_{PAYLOAD}.{SIG}"
OLD_STYLE = "oldsharedtoken-0123456789abcdefghijkl"     # not a per-user key

RUNNER = r'''
import importlib.util, sys, time
spec = importlib.util.spec_from_file_location("mregmod", sys.argv[1])
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
time.sleep = lambda s: None                      # the retry loops of the failing paths do not wait
mode = sys.argv[2]
args = sys.argv[3:]
if mode == "leak-die":
    m.cmd_whoami = lambda a: m.die("oops " + m.read_token()[0])
elif mode == "leak-print":
    m.cmd_whoami = lambda a: print("token is", m.read_token()[0], "and window", m.read_token()[0][5:40])
elif mode == "leak-raise":
    def boom(a):
        raise ValueError("bad header value %r" % m.read_token()[0])
    m.cmd_whoami = boom
elif mode == "leak-stderr":
    m.cmd_whoami = lambda a: print("err:", m.read_token()[0], file=sys.stderr)
sys.argv = ["mreg"] + args
m.main()
'''


class Mock(http.server.ThreadingHTTPServer):
    daemon_threads = True

    def __init__(self):
        self.mode, self.log = "ok", []
        super().__init__(("127.0.0.1", 0), Handler)
        self.port = self.server_address[1]
        threading.Thread(target=self.serve_forever, daemon=True).start()

    @property
    def url(self):
        return f"http://127.0.0.1:{self.port}"


class Handler(http.server.BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def do_GET(self):
        s = self.server
        tok = self.headers.get("x-mreg-token") or ""
        s.log.append({"path": self.path, "range": self.headers.get("Range"), "has_token": bool(tok),
                      "auth": self.headers.get("Authorization")})
        echo = {"x-echo": tok.replace("\n", " ")[:300]}
        mode = s.mode
        if mode == "403":
            return self.reply(403, b"forbidden " + tok.encode("latin-1", "replace"), echo)
        if mode == "403d":
            return self.reply(403, b"", dict(echo, **{"x-mreg-denial": "revoked"}))
        if mode == "451":
            return self.reply(451, b"gone", echo)
        if mode == "500":
            return self.reply(500, b"internal " + tok.encode("latin-1", "replace"), echo)
        if mode == "garbage":
            return self.reply(200, b"<html>" + tok.encode("latin-1", "replace") + b"</html>", echo)
        body = b'{"schema": "mreg-decl-store/1", "trains": []}' + b" " * 100
        rng = self.headers.get("Range")
        m = re.match(r"bytes=(\d+)-(\d+)$", rng or "")
        if m and "/x/decl/" in self.path:
            a, b = int(m.group(1)), min(int(m.group(2)), len(body) - 1)
            return self.reply(206, body[a:b + 1], dict(echo, **{"Content-Range": f"bytes {a}-{b}/{len(body)}"}))
        return self.reply(200, body, echo)

    def reply(self, code, body, headers):
        self.send_response(code)
        for k, v in headers.items():
            try:
                self.send_header(k, v)
            except Exception:
                pass
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)


def windows(key, n=20):
    return {key[i:i + n] for i in range(len(key) - n + 1)}


def leaks(text, key):
    """Why `text` shows the key, or None. The whole key, any 20 consecutive characters of it, or any key-shaped string."""
    if key in text:
        return "the whole key"
    for w in windows(key):
        if w in text:
            return f"a 20-character window of the key ({w[:4]}...)"
    for m in re.finditer(r"mreg_[A-Za-z0-9_.-]{20,}", text):
        return "a key-shaped string"
    return None


class Base(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.mkdtemp(prefix="tc5-")
        cls.runner = os.path.join(cls.tmp, "runner.py")
        with open(cls.runner, "w") as f:
            f.write(RUNNER)
        cls.home = os.path.join(cls.tmp, "home")
        os.makedirs(os.path.join(cls.home, ".mreg"))
        cls.proj = os.path.join(cls.tmp, "proj")
        os.makedirs(cls.proj)
        cls.server = Mock()
        cls.defstubs = os.path.join(cls.tmp, "defstubs")       # no real git, lake or lean is ever on the PATH of a test run
        os.makedirs(cls.defstubs)
        make_stubs(cls.defstubs, os.path.join(cls.tmp, "defcalls.log"))

    @classmethod
    def tearDownClass(cls):
        cls.server.shutdown()
        cls.server.server_close()
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def env(self, token=None, registry=None, file_token=None, path=None, **extra):
        e = {k: v for k, v in os.environ.items() if not k.startswith("MREG_")}
        e.update({"HOME": self.home, "USERPROFILE": self.home, "MREG_STORE": os.path.join(self.tmp, "store"),
                  "MREG_REGISTRY": registry or self.server.url, "MREG_RETRIES": "0", "MREG_BACKOFF": "0", "MREG_TIMEOUT": "10",
                  "PYTHONIOENCODING": "utf-8", "PYTHONUTF8": "1"})
        if token is not None:
            e["MREG_TOKEN"] = token
        e["PATH"] = path if path is not None else self.defstubs
        e.update(extra)
        tf = os.path.join(self.home, ".mreg", "token")
        if file_token is None:
            if os.path.exists(tf):
                os.remove(tf)
        else:
            with open(tf, "w") as f:
                f.write(file_token + "\n")
        return e

    def run_mreg(self, args, env, mode="run", timeout=120):
        r = subprocess.run([sys.executable, "-I", self.runner, MREG, mode] + args, env=env, capture_output=True, timeout=timeout,
                           stdin=subprocess.DEVNULL, cwd=self.proj)
        return r.returncode, r.stdout.decode("utf-8", "replace"), r.stderr.decode("utf-8", "replace")


class TestNoLeak(Base):
    """Every command, with a recognisable key in the environment (and again in the file), against a mock registry, on success and
    on failing paths, with and without --json: nothing on stdout or stderr shows the key."""
    COMMANDS = [
        ["train"], ["view", "owner/pkg"], ["resolve", "owner/pkg#Foo.bar"], ["resolve", "owner/pkg#Foo.bar", "--json"],
        ["index"], ["index", "--json"], ["env"], ["env", "--json"], ["verify"], ["verify", "--json"], ["audit"], ["audit", "--json"],
        ["install", "owner/pkg#Foo.bar"], ["install", "owner/pkg#Foo.bar", "--json"], ["install", "--dry-run"],
        ["add", "owner/pkg#Foo.bar", "--dry-run", "--json"], ["add", "owner/pkg", "--no-lake-update"], ["ci"], ["ci", "--json"],
        ["init", "newproj"], ["whoami"], ["logout"], ["doctor"], ["doctor", "--json"],
        ["login", "--no-browser", "--timeout", "1"],
    ]

    def scan(self, args, env, key, where):
        rc, out, err = self.run_mreg(args, env)
        why = leaks(out + "\n" + err, key)
        self.assertIsNone(why, f"{where}: `mreg {' '.join(args)}` (exit {rc}) shows {why}")
        return rc, out, err

    def test_key_in_environment_all_modes(self):
        n0 = 0
        for mode in ("ok", "403d", "451", "garbage"):
            self.server.mode = mode
            env = self.env(token=FAKE_KEY, MREG_KEYS_URL=self.server.url, MREG_AUTH_URL=self.server.url, MREG_LOGIN_PORT="0")
            for args in self.COMMANDS:
                self.scan(args, env, FAKE_KEY, f"env, mock {mode}")
        self.assertGreater(len(self.server.log), 20, "the commands did not reach the mock registry: the test proves nothing")

    def test_500_and_403_paths(self):
        for mode in ("500", "403"):
            self.server.mode = mode
            env = self.env(token=FAKE_KEY)
            for args in (["train"], ["resolve", "owner/pkg#Foo.bar", "--json"], ["resolve", "owner/pkg#Foo.bar"], ["index", "--json"],
                         ["doctor", "--json"], ["view", "x"]):
                self.scan(args, env, FAKE_KEY, f"env, mock {mode}")

    def test_key_in_file(self):
        for mode in ("ok", "403d"):
            self.server.mode = mode
            env = self.env(file_token=FAKE_KEY)
            for args in (["train"], ["resolve", "owner/pkg#Foo.bar", "--json"], ["whoami"], ["doctor"], ["doctor", "--json"],
                         ["logout"], ["index"]):
                self.scan(args, env, FAKE_KEY, f"file, mock {mode}")
                if args == ["logout"]:
                    self.env(file_token=FAKE_KEY)

    def test_file_registry(self):
        reg = os.path.join(self.tmp, "reg")
        os.makedirs(os.path.join(reg, "v1", "index"))
        env = self.env(token=FAKE_KEY, registry="file:///" + reg.replace("\\", "/").lstrip("/"))
        for args in (["train"], ["resolve", "owner/pkg#Foo.bar", "--json"], ["doctor", "--json"], ["view", "nothing"]):
            self.scan(args, env, FAKE_KEY, "file registry")

    def test_unusable_key_text(self):
        """A key that makes the HTTP layer raise (newline, non-latin-1): the exception text must not carry it."""
        bad_keys = [FAKE_KEY[:30] + "\n" + FAKE_KEY[30:], FAKE_KEY[:30] + "\u00e9\u4e2d" + FAKE_KEY[30:]]
        self.server.mode = "ok"
        for bad in bad_keys:
            env = self.env(token=bad)
            for args in (["train"], ["resolve", "owner/pkg#Foo.bar", "--json"], ["doctor", "--json"], ["whoami"]):
                rc, out, err = self.run_mreg(args, env)
                for part in (FAKE_KEY[:30], FAKE_KEY[30:]):
                    for w in windows(part):
                        self.assertNotIn(w, out + err, f"`mreg {' '.join(args)}` shows part of an unusable key")

    def test_scrub_catches_deliberate_leaks(self):
        """A bug that prints, raises or dies with the key is stopped by the output filter (the code paths above do not leak, so the
        filter is exercised here by injecting such bugs)."""
        for mode in ("leak-die", "leak-print", "leak-raise", "leak-stderr"):
            for env in (self.env(token=FAKE_KEY), self.env(file_token=FAKE_KEY), self.env(token=OLD_STYLE)):
                key = env.get("MREG_TOKEN") or FAKE_KEY
                rc, out, err = self.run_mreg(["whoami"], env, mode=mode)
                self.assertIsNone(leaks(out + err, key), f"{mode}: key shown")
                self.assertNotEqual(OLD_STYLE in (out + err), True, f"{mode}: plain token shown")
                self.assertNotEqual(rc, 0 if mode in ("leak-die", "leak-raise") else 99)
                if mode == "leak-raise":
                    self.assertIn("unexpected error", err)

    def test_debug_traceback_is_scrubbed(self):
        env = self.env(token=FAKE_KEY, MREG_DEBUG="1")
        rc, out, err = self.run_mreg(["whoami"], env, mode="leak-raise")
        self.assertIn("Traceback", err)
        self.assertIsNone(leaks(out + err, FAKE_KEY))


class TestRefusals(Base):
    def setUp(self):
        self.server.mode = "ok"
        self.server.log.clear()

    def refused(self, args, env, key=FAKE_KEY):
        n = len(self.server.log)
        rc, out, err = self.run_mreg(args, env)
        self.assertEqual(rc, 1, (args, out, err))
        self.assertIsNone(leaks(out + err, key), (args, out, err))
        self.assertEqual(len(self.server.log), n, f"`mreg {' '.join(args)}` sent a request")
        return out + err

    def test_flags_refused(self):
        env = self.env()
        for args in (["--token", FAKE_KEY, "train"], ["train", "--token", FAKE_KEY], ["train", "--token=" + FAKE_KEY],
                     ["train", "--key", FAKE_KEY], ["resolve", "--api-key=" + FAKE_KEY, "a/b#c"], ["train", "-token", FAKE_KEY],
                     ["view", FAKE_KEY], ["train", FAKE_KEY], ["add", "owner/pkg#" + FAKE_KEY], ["--password", "x", "train"],
                     ["doctor", "--secret", "x"]):
            msg = self.refused(args, env)
            self.assertIn("never accepted on the command line", msg)
            self.assertIn("MREG_TOKEN", msg)

    def test_registry_url_refused(self):
        host = self.server.url.replace("http://", "")
        for reg in (f"http://user:{FAKE_KEY}@{host}", f"http://{FAKE_KEY}@{host}", f"{self.server.url}?token={FAKE_KEY}",
                    f"{self.server.url}/#{FAKE_KEY}", f"http://u:p@{host}", f"{self.server.url}?x=1", f"{self.server.url}/{FAKE_KEY}"):
            env = self.env(token=FAKE_KEY, registry=reg)
            for args in (["train"], ["resolve", "owner/pkg#Foo.bar", "--json"], ["resolve", "owner/pkg#Foo.bar"], ["index"],
                         ["login", "--no-browser", "--timeout", "1"]):
                msg = self.refused(args, env)
                self.assertTrue("MREG_REGISTRY is refused" in msg or '"message"' in msg, (reg, args, msg))
            rc, out, err = self.run_mreg(["doctor", "--json"], env)
            self.assertEqual(rc, 1)
            self.assertIsNone(leaks(out + err, FAKE_KEY))
            doc = json.loads(out)
            self.assertEqual(doc["registry"]["requests"], 0)
            self.assertIn("refused", doc["registry"]["error"])
        self.assertEqual(self.server.log, [])

    def test_bearer_header_not_used(self):
        """The edge accepts `Authorization: Bearer <key>` as well, since 2026-11-12; the client keeps `x-mreg-token`."""
        env = self.env(token=FAKE_KEY)
        self.run_mreg(["doctor", "--json"], env)
        self.run_mreg(["train"], env)
        self.assertTrue(self.server.log)
        for e in self.server.log:
            self.assertTrue(e["has_token"])
            self.assertIsNone(e["auth"])

    def test_no_key_no_request(self):
        env = self.env()
        rc, out, err = self.run_mreg(["train"], env)
        self.assertEqual(rc, 1)
        self.assertIn("no access token", out + err)
        self.assertEqual(self.server.log, [])


class TestScrubUnit(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import importlib.util
        spec = importlib.util.spec_from_file_location("mregmod_unit", MREG)
        cls.m = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.m)

    def setUp(self):
        self.m._SECRETS = [OLD_STYLE]
        self.m._EXTRA_SECRETS[:] = []

    def test_shapes(self):
        s = self.m.scrub(f"a {FAKE_KEY} b mreg_{PAYLOAD} c")
        self.assertNotIn(PAYLOAD, s)
        self.assertIn("[redacted]", s)

    def test_stored_secret_and_windows(self):
        self.assertNotIn(OLD_STYLE, self.m.scrub("x " + OLD_STYLE + " y"))
        w = OLD_STYLE[7:30]
        out = self.m.scrub("before " + w + "tail after")
        self.assertNotIn(OLD_STYLE[7:27], out)
        self.assertIn("before", out)
        self.assertIn("after", out)

    def test_ordinary_text_untouched(self):
        t = "mreg: 3 chunks, sha256 " + "ab" * 32 + " in Mreg.X1f.C0123456789abcdef0123456789abcdef and mreg-chunks.lock.json"
        self.assertEqual(self.m.scrub(t), t)

    def test_register_secret(self):
        self.m.register_secret("eyJhbGciOi.payloadpayloadpayload.sig")
        self.assertNotIn("payloadpayloadpayload", self.m.scrub("t eyJhbGciOi.payloadpayloadpayload.sig"))

    def test_registry_url_problem(self):
        p = self.m.registry_url_problem
        for ok in ("https://mathregistry.com", "http://127.0.0.1:8000", "file:///C:/reg", "s3://bucket/prefix", "http://localhost:9/x/y"):
            self.assertIsNone(p(ok), ok)
        for bad in ("https://u:p@h", "https://u@h", "https://h?a=1", "https://h#f", "https://h/a;b?c", "https://h/" + FAKE_KEY):
            self.assertIsNotNone(p(bad), bad)

    def test_source_does_not_format_credentials_into_messages(self):
        """No print, die, raise or NIError line interpolates a variable that holds a key or sign-in token."""
        bad = re.compile(r"\{[^}]*\b(tok|token|self\.tok|idt|id_token|key)\b(?!_)[^}]*\}")
        offenders = []
        for n, line in enumerate(open(MREG, encoding="utf-8").read().splitlines(), 1):
            st = line.strip()
            if st.startswith("#"):
                continue
            if re.search(r"\b(print|die|NIError|RangeError|raise)\b\(?", st) and bad.search(st):
                offenders.append((n, st[:120]))
        self.assertEqual(offenders, [])


def make_stubs(d, log):
    """Stub git, lake, lean (and no zstd): each writes its arguments to `log` and prints a fixed version."""
    for name, ver in (("git", "git version 9.9.9 (stub)"), ("lake", "Lake version 8.8.8 (stub)"), ("lean", "Lean (version 7.7.7, stub)")):
        if WIN:
            with open(os.path.join(d, name + ".cmd"), "w") as f:
                f.write(f"@echo off\r\necho {name} %* >> \"{log}\"\r\necho {ver}\r\n")
        else:
            p = os.path.join(d, name)
            with open(p, "w") as f:
                f.write(f"#!/bin/sh\necho \"{name} $*\" >> '{log}'\necho '{ver}'\n")
            os.chmod(p, 0o755)


class TestDoctor(Base):
    def setUp(self):
        self.server.mode = "ok"
        self.server.log.clear()
        self.stubs = tempfile.mkdtemp(prefix="stubs-", dir=self.tmp)
        self.calls = os.path.join(self.tmp, "calls.log")
        if os.path.exists(self.calls):
            os.remove(self.calls)
        make_stubs(self.stubs, self.calls)
        self.sysroot = os.environ.get("SystemRoot", "")

    def path(self):
        return self.stubs

    def doctor(self, env, *flags):
        rc, out, err = self.run_mreg(["doctor"] + list(flags), env)
        return rc, out, err

    def test_json_parses_and_is_complete(self):
        env = self.env(token=FAKE_KEY, path=self.path())
        rc, out, err = self.doctor(env, "--json")
        doc = json.loads(out)
        self.assertEqual(doc["schema"], "mreg-doctor/0")
        self.assertIs(doc["schema_frozen"], False)
        self.assertEqual(doc["mreg_version"], "0.6.6")
        self.assertTrue(doc["python"]["ok"])
        for n, v in (("git", "9.9.9"), ("lake", "8.8.8"), ("lean", "7.7.7")):
            self.assertIsNotNone(doc["tools"][n]["found"])
            self.assertIn(v, doc["tools"][n]["version"])
        self.assertIn("usable", doc["zstd"])
        self.assertIn("address space", doc["address_space"]["note"].lower())
        self.assertIn("8.1 to 9.2 GiB", doc["address_space"]["note"])
        self.assertEqual(doc["credential"]["kind"], "per_user_key")
        self.assertEqual(doc["credential"]["source"], "environment")
        self.assertTrue(doc["store"]["writable"])
        rg = doc["registry"]
        self.assertEqual((rg["status"], rg["requests"], rg["ok"]), (206, 1, True))
        self.assertLessEqual(rg["bytes"], 64)
        self.assertEqual(rg["path"], "/x/decl/lean-4.35.0/current.json")
        self.assertEqual(len(self.server.log), 1)
        self.assertEqual(self.server.log[0]["range"], "bytes=0-63")
        self.assertEqual(self.server.log[0]["path"], "/x/decl/lean-4.35.0/current.json")
        self.assertIsNone(self.server.log[0]["auth"])
        self.assertIsNone(leaks(out + err, FAKE_KEY))
        self.assertNotIn("owner-fake", out)
        self.assertNotIn("kQWERTYUIOP", out)
        self.assertEqual(rc, 0 if doc["ok"] else 1)
        self.assertEqual(doc["ok"], not doc["problems"])
        if doc["zstd"]["usable"]:
            self.assertEqual(rc, 0, doc["problems"])

    def test_lean_only_asked_for_its_version(self):
        env = self.env(token=FAKE_KEY, path=self.path())
        self.doctor(env, "--json")
        self.doctor(env)
        lines = [x.strip() for x in open(self.calls).read().splitlines() if x.strip()]
        self.assertTrue(lines)
        for x in lines:
            self.assertTrue(x.endswith("--version"), x)
        self.assertTrue(any(x.startswith("lean ") for x in lines))
        self.assertEqual({x.split()[0] for x in lines}, {"git", "lake", "lean"})

    def test_human_output(self):
        env = self.env(token=FAKE_KEY, path=self.path())
        rc, out, err = self.doctor(env)
        for word in ("python:", "git:", "lake:", "lean:", "zstd:", "address space:", "credential:", "store:", "registry (http)", "result:"):
            self.assertIn(word, out)
        self.assertIn("per_user_key", out)
        self.assertIsNone(leaks(out + err, FAKE_KEY))

    def test_tools_missing_are_warnings(self):
        empty = tempfile.mkdtemp(prefix="empty-", dir=self.tmp)
        env = self.env(token=FAKE_KEY, path=empty)
        rc, out, err = self.doctor(env, "--json")
        doc = json.loads(out)
        for n in ("git", "lake", "lean"):
            self.assertIsNone(doc["tools"][n]["found"])
        self.assertEqual(len([w for w in doc["warnings"] if "not found" in w]), 3)
        self.assertFalse(os.path.exists(self.calls))

    def test_old_style_token_is_not_a_per_user_key(self):
        self.server.mode = "403d"
        env = self.env(token=OLD_STYLE, path=self.path())
        rc, out, err = self.doctor(env, "--json")
        doc = json.loads(out)
        self.assertEqual(rc, 1)
        self.assertEqual(doc["credential"]["kind"], "not_a_per_user_key")
        self.assertIn("will be refused", doc["credential"]["note"])
        self.assertEqual(doc["registry"]["status"], 403)
        self.assertEqual(doc["registry"]["denial"], "revoked")
        self.assertFalse(doc["ok"])
        self.assertNotIn(OLD_STYLE, out + err)
        self.assertTrue(any("not a per-user key" in p for p in doc["problems"]))

    def test_damaged_key(self):
        env = self.env(token="mreg_notbase64!!.short", path=self.path())
        rc, out, err = self.doctor(env, "--json")
        self.assertEqual(json.loads(out)["credential"]["kind"], "damaged_key")
        self.assertEqual(rc, 1)
        env = self.env(token="mreg_" + "A" * 30 + "." + "B" * 43, path=self.path())
        self.assertEqual(json.loads(self.doctor(env, "--json")[1])["credential"]["kind"], "damaged_key")

    def test_no_credential_sends_nothing(self):
        env = self.env(path=self.path())
        rc, out, err = self.doctor(env, "--json")
        doc = json.loads(out)
        self.assertEqual(rc, 1)
        self.assertEqual(doc["credential"]["kind"], "none")
        self.assertFalse(doc["credential"]["present"])
        self.assertEqual(doc["registry"]["requests"], 0)
        self.assertEqual(self.server.log, [])

    def test_key_from_file_and_permission_note(self):
        env = self.env(file_token=FAKE_KEY, path=self.path())
        doc = json.loads(self.doctor(env, "--json")[1])
        self.assertEqual(doc["credential"]["source"], "file")
        self.assertTrue(doc["credential"]["file"]["exists"])
        note = doc["credential"]["file"]["permission_note"]
        self.assertTrue(note)
        if WIN:
            self.assertIn("Windows", note)
            self.assertIn("not enforced", note)
        else:
            os.chmod(os.path.join(self.home, ".mreg", "token"), 0o644)
            doc = json.loads(self.doctor(env, "--json")[1])
            self.assertIn("chmod 600", doc["credential"]["file"]["permission_note"])

    def test_env_overrides_file_warning(self):
        env = self.env(token=FAKE_KEY, file_token=FAKE_KEY, path=self.path())
        doc = json.loads(self.doctor(env, "--json")[1])
        self.assertTrue(any("takes precedence" in w for w in doc["warnings"]))

    def test_unreachable_registry(self):
        s = Mock()
        port = s.port
        s.shutdown()
        s.server_close()
        env = self.env(token=FAKE_KEY, registry=f"http://127.0.0.1:{port}", path=self.path())
        rc, out, err = self.doctor(env, "--json")
        doc = json.loads(out)
        self.assertEqual(rc, 1)
        self.assertIn("cannot reach", doc["registry"]["error"])
        self.assertIsNone(leaks(out + err, FAKE_KEY))

    def test_status_codes_reported(self):
        for mode, code in (("451", 451), ("500", 500), ("403", 403)):
            self.server.mode = mode
            env = self.env(token=FAKE_KEY, path=self.path())
            rc, out, err = self.doctor(env, "--json")
            doc = json.loads(out)
            self.assertEqual(doc["registry"]["status"], code)
            self.assertFalse(doc["registry"]["ok"])
            self.assertEqual(rc, 1)
            self.assertIsNone(leaks(out + err, FAKE_KEY))

    def test_store_not_writable(self):
        blocker = os.path.join(self.tmp, "afile")
        with open(blocker, "w") as f:
            f.write("x")
        env = self.env(token=FAKE_KEY, path=self.path(), MREG_STORE=os.path.join(blocker, "store"))
        rc, out, err = self.doctor(env, "--json")
        doc = json.loads(out)
        self.assertFalse(doc["store"]["writable"])
        self.assertEqual(rc, 1)

    def test_store_existing_is_writable_and_unchanged(self):
        d = os.path.join(self.tmp, "store2")
        os.makedirs(d)
        env = self.env(token=FAKE_KEY, path=self.path(), MREG_STORE=d)
        doc = json.loads(self.doctor(env, "--json")[1])
        self.assertTrue(doc["store"]["writable"])
        self.assertEqual(os.listdir(d), [])

    def test_file_registry(self):
        reg = os.path.join(self.tmp, "reg2")
        os.makedirs(os.path.join(reg, "x", "decl", "lean-4.35.0"))
        with open(os.path.join(reg, "x", "decl", "lean-4.35.0", "current.json"), "w") as f:
            f.write("{}")
        env = self.env(path=self.path(), registry="file:///" + reg.replace("\\", "/").lstrip("/"))
        rc, out, err = self.doctor(env, "--json")
        doc = json.loads(out)
        self.assertEqual(doc["registry"]["base_kind"], "file")
        self.assertTrue(doc["registry"]["ok"])
        self.assertEqual(doc["registry"]["requests"], 0)
        self.assertEqual(self.server.log, [])

    def test_exit_codes_in_table(self):
        """doctor exits 0 or 1 only: both already exist in the table of NAMED_IMPORT.md."""
        for token in (FAKE_KEY, OLD_STYLE, None):
            env = self.env(token=token, path=self.path())
            self.assertIn(self.doctor(env, "--json")[0], (0, 1))


class TestClientHardening(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import importlib.util
        spec = importlib.util.spec_from_file_location("mregmod_hardening", MREG)
        cls.m = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.m)

    def test_no_redirect_and_safe_redirect_handlers(self):
        import urllib.error, urllib.request
        seen = []

        class _H(http.server.BaseHTTPRequestHandler):
            def log_message(self, *a):
                pass

            def do_GET(self):
                seen.append((self.server.label, self.path, self.headers.get("x-mreg-token"), self.headers.get("Authorization")))
                if self.path == "/to-same":
                    self.send_response(302)
                    self.send_header("Location", "/target")
                    self.end_headers()
                elif self.path == "/to-cross":
                    self.send_response(302)
                    self.send_header("Location", self.server.other_url + "/target")
                    self.end_headers()
                elif self.path == "/to-http":
                    self.send_response(302)
                    self.send_header("Location", "http://evil.example/steal")
                    self.end_headers()
                else:
                    body = b"ok"
                    self.send_response(200)
                    self.send_header("Content-Length", str(len(body)))
                    self.end_headers()
                    self.wfile.write(body)

        srv1 = http.server.ThreadingHTTPServer(("127.0.0.1", 0), _H)
        srv2 = http.server.ThreadingHTTPServer(("127.0.0.1", 0), _H)
        srv1.label, srv2.label = "s1", "s2"
        srv1.other_url = f"http://127.0.0.1:{srv2.server_port}"
        srv2.other_url = f"http://127.0.0.1:{srv1.server_port}"
        threading.Thread(target=srv1.serve_forever, daemon=True).start()
        threading.Thread(target=srv2.serve_forever, daemon=True).start()
        self.addCleanup(srv1.server_close)
        self.addCleanup(srv2.server_close)
        self.addCleanup(srv1.shutdown)
        self.addCleanup(srv2.shutdown)

        base1 = f"http://127.0.0.1:{srv1.server_port}"
        # _no_redirect_open refuses 302 outright
        with self.assertRaises(urllib.error.HTTPError) as ctx:
            self.m._no_redirect_open(urllib.request.Request(base1 + "/to-same", headers={"x-mreg-token": FAKE_KEY}), timeout=5)
        self.assertEqual(ctx.exception.code, 302)

        # Same-origin 302 keeps x-mreg-token
        seen.clear()
        with self.m._safe_redirect_open(urllib.request.Request(base1 + "/to-same", headers={"x-mreg-token": FAKE_KEY}), timeout=5) as r:
            self.assertEqual(r.read(), b"ok")
        self.assertEqual(seen[-1], ("s1", "/target", FAKE_KEY, None))

        # Cross-origin 302 (different port) strips x-mreg-token and Authorization
        seen.clear()
        with self.m._safe_redirect_open(
            urllib.request.Request(base1 + "/to-cross", headers={"x-mreg-token": FAKE_KEY, "Authorization": "Bearer secret"}), timeout=5
        ) as r:
            self.assertEqual(r.read(), b"ok")
        self.assertEqual(seen[-1], ("s2", "/target", None, None))

        # Redirect to non-loopback http:// is refused before connecting
        with self.assertRaises(urllib.error.HTTPError) as ctx2:
            self.m._safe_redirect_open(urllib.request.Request(base1 + "/to-http", headers={"x-mreg-token": FAKE_KEY}), timeout=5)
        self.assertIn("refusing redirect to insecure URL", str(ctx2.exception))

    @unittest.skipUnless(WIN, "Windows protected DACL test")
    def test_store_token_windows_protected_acl(self):
        from unittest import mock
        with tempfile.TemporaryDirectory() as d1, tempfile.TemporaryDirectory() as d2:
            with mock.patch.dict(os.environ, {"HOME": d1, "USERPROFILE": d1}):
                self.m.store_token(FAKE_KEY)
                p1 = self.m.token_path()
                self.assertTrue(os.path.isfile(p1))
                self.assertTrue(self.m._win_has_protected_acl(p1))
                rep1, _ = self.m._credential_state()
                self.assertEqual(rep1["file"]["permission_note"], "Windows: protected ACL (owner-only)")

            with mock.patch.dict(os.environ, {"HOME": d2, "USERPROFILE": d2}):
                p2 = self.m.token_path()
                os.makedirs(os.path.dirname(p2), exist_ok=True)
                with open(p2, "w", encoding="ascii", newline="\n") as f:
                    f.write(FAKE_KEY + "\n")
                rep2, _ = self.m._credential_state()
                self.assertIn("not enforced", rep2["file"]["permission_note"])


if __name__ == "__main__":
    unittest.main(verbosity=1)
