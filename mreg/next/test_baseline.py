#!/usr/bin/env python3
"""T-C1 baseline tests for mreg/next/mreg.py (stdlib only, no network, no Lean).

    python -I test_baseline.py

1. The precedence of mreg.lock, mreg-chunks.lock.json and lake-manifest.json (stated in NAMED_IMPORT.md, section 6).
2. What `mreg audit` without --require counts as passing (the behaviour as it is: see the test names).
3. No code path prompts for input.
"""
import argparse, ast, base64, contextlib, hashlib, importlib.util, io, json, os, shutil, sys, tempfile, unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("mreg_next_base", os.path.join(HERE, "mreg.py"))
M = importlib.util.module_from_spec(spec)
spec.loader.exec_module(M)


def sha(b):
    return hashlib.sha256(b).hexdigest()


def run_main(argv, env=None):
    out, err, code = io.StringIO(), io.StringIO(), 0
    with mock.patch.dict(os.environ, env or {}, clear=False), contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        try:
            M.main(argv)
        except SystemExit as x:
            code = x.code if isinstance(x.code, int) else (0 if x.code is None else x.code)
    return code, out.getvalue(), err.getvalue()


class Precedence(unittest.TestCase):
    """NAMED_IMPORT.md section 6. Order of the three files, as the code applies it."""

    def setUp(self):
        self.d = tempfile.mkdtemp(prefix="mreg-base-")
        self.addCleanup(shutil.rmtree, self.d, True)
        self.w("lean-toolchain", "leanprover/lean4:v4.35.0\n")
        self.manifest = {"version": "1.1.0", "packagesDir": ".lake/packages", "name": "proj", "lakeDir": ".lake",
                         "packages": [{"name": "mathlib", "url": "https://github.com/leanprover-community/mathlib4", "rev": "c" * 40}]}
        self.w("lake-manifest.json", json.dumps(self.manifest))

    def w(self, rel, text):
        with open(os.path.join(self.d, rel), "w", encoding="utf-8", newline="\n") as f:
            f.write(text)

    def module_lock(self, manifest_sha):
        return {"schema": "mreg-lock/0", "registry": "file:///x", "toolchain": "leanprover/lean4:v4.35.0",
                "lake_manifest_sha256": manifest_sha, "targets": [], "packages": []}

    def test_lake_manifest_is_the_reference_the_module_lock_must_match(self):
        self.w("mreg.lock", json.dumps(self.module_lock("0" * 64)))
        code, out, err = run_main(["-C", self.d, "ci", "--no-lake-check"], {"MREG_REGISTRY": "file:///" + self.d.replace("\\", "/").lstrip("/")})
        self.assertNotEqual(code, 0)
        self.assertIn("lake-manifest.json is not the one this lock was made for", str(code) + err + out)

    def test_module_lock_is_accepted_when_the_manifest_hash_matches_then_toolchain_is_checked(self):
        mh = M.sha256_file(os.path.join(self.d, "lake-manifest.json"))
        lk = self.module_lock(mh)
        lk["toolchain"] = "leanprover/lean4:v4.34.1"
        self.w("mreg.lock", json.dumps(lk))
        code, out, err = run_main(["-C", self.d, "ci", "--no-lake-check"], {"MREG_REGISTRY": "file:///" + self.d.replace("\\", "/").lstrip("/")})
        self.assertIn("the lock is for leanprover/lean4:v4.34.1", str(code))     # past the manifest check, the next check speaks

    def test_chunk_lock_is_restored_first_and_the_module_lock_second(self):
        self.w("mreg-chunks.lock.json", "{}")
        self.w("mreg.lock", json.dumps(self.module_lock("0" * 64)))
        order = []
        with mock.patch.object(M, "ni_ci", lambda a: order.append("chunks") or 0):
            code, out, err = run_main(["-C", self.d, "ci", "--no-lake-check"], {"MREG_REGISTRY": "file:///" + self.d.replace("\\", "/").lstrip("/")})
        self.assertEqual(order, ["chunks"])
        self.assertIn("lake-manifest.json is not the one this lock was made for", str(code))   # the module lock was then read

    def test_chunks_only_never_reads_the_module_lock(self):
        self.w("mreg-chunks.lock.json", "{}")
        self.w("mreg.lock", json.dumps(self.module_lock("0" * 64)))
        with mock.patch.object(M, "ni_ci", lambda a: 0), mock.patch.object(M, "Project", side_effect=AssertionError("module lock read")):
            code, out, err = run_main(["-C", self.d, "ci", "--chunks-only"], {"MREG_REGISTRY": "file:///" + self.d.replace("\\", "/").lstrip("/")})
        self.assertEqual(code, 0)

    def test_a_failing_chunk_lock_stops_before_the_module_lock(self):
        self.w("mreg-chunks.lock.json", "{}")
        self.w("mreg.lock", json.dumps(self.module_lock("0" * 64)))

        def bad(a):
            raise M.NIError("hash_mismatch", "boom")
        with mock.patch.object(M, "ni_ci", bad), mock.patch.object(M, "Project", side_effect=AssertionError("module lock read")):
            code, out, err = run_main(["-C", self.d, "ci", "--json"], {"MREG_REGISTRY": "file:///" + self.d.replace("\\", "/").lstrip("/")})
        self.assertEqual(code, M.EXIT["hash_mismatch"])

    def test_module_packages_attribute_the_reason_in_a_fixed_order(self):
        # lake-manifest.json, then lakefile.toml, then the module state, then mreg.lock: the first that names a package is the reason given
        self.w("lakefile.toml", '[[require]]\nname = "mathlib"\n')
        os.makedirs(os.path.join(self.d, ".lake"))
        self.w(M.STATE, json.dumps({"packages": {"mathlib": {}}}))
        self.w("mreg.lock", json.dumps({"packages": [{"from": "registry", "lake_name": "mathlib"}]}))
        self.assertEqual(M.module_packages(self.d)["mathlib"], "lake-manifest.json")
        os.unlink(os.path.join(self.d, "lake-manifest.json"))
        self.assertEqual(M.module_packages(self.d)["mathlib"], "lakefile.toml [[require]]")
        os.unlink(os.path.join(self.d, "lakefile.toml"))
        self.assertEqual(M.module_packages(self.d)["mathlib"], M.STATE)
        os.unlink(os.path.join(self.d, M.STATE))
        self.assertEqual(M.module_packages(self.d)["mathlib"], "mreg.lock")

    def test_module_files_and_chunks_of_one_package_are_refused_together(self):
        self.w("mreg-chunks.lock.json", json.dumps({"schema": M.CHUNK_LOCK_SCHEMA, "train": "t", "build": "b", "covers_packages": ["mathlib"]}))
        with self.assertRaises(M.NIError) as cm:
            M.reverse_mix(self.d, ["mathlib"])
        self.assertEqual(cm.exception.kind, "forbidden_mix")
        self.assertEqual(cm.exception.code, 15)
        with self.assertRaises(M.NIError) as cm:       # and the other direction: chunks asked for a package whose files are in the manifest
            M.check_mix(self.d, ["mathlib"], "t", "b", "checking", None, os.path.join(self.d, "cd"))
        self.assertEqual(cm.exception.kind, "forbidden_mix")
        self.assertIn("lake-manifest.json", cm.exception.message)


# ---------------------------------------------------------------- audit without --require

class FakeReg:
    """A registry that serves a dict of path -> bytes. Counts nothing; no network."""
    def __init__(self, files):
        self.files, self.base, self.accept_new_key = files, "file:///fake", False

    def get(self, path, rng=None, missing_ok=False):
        if path in self.files:
            return self.files[path]
        if missing_ok:
            return None
        raise SystemExit("mreg: 404 from the registry: " + path)

    def json(self, path, **kw):
        b = self.get(path, **kw)
        return None if b is None else json.loads(b)


def synthetic_build(gates, labels=("flagged",)):
    """A registry holding one internally consistent signed-looking build (id demo/pkg 1.0.0) whose gate statuses are `gates`."""
    pid, ver, key = "demo/pkg", "1.0.0", "k" * 8
    verify = json.dumps({"gates": {g: {"status": s} for g, s in gates.items()}}).encode()
    man = json.dumps({"id": pid, "version": ver, "build_key": key, "gates": {g: {"status": s} for g, s in gates.items()},
                      "reports": {"reports/verify.json": sha(verify)}}).encode()
    msha, sigraw = sha(man), b'{"synthetic": true}'
    base = f"/v1/blobs/{pid}/-/{ver}/{key}/"
    doc = {"id": pid, "dist_tags": {"latest": ver},
           "versions": {ver: {"builds": [{"build_key": key, "manifest": {"sha256": msha}, "labels": list(labels), "log_n": 1}]}}}
    entry = json.dumps({"id": pid, "version": ver, "build_key": key, "manifest_sha256": msha, "sig_sha256": sha(sigraw),
                        "labels": list(labels), "type": "promote"}).encode()
    files = {f"/v1/index/{pid}.json": json.dumps(doc).encode(), base + "manifest.json": man, base + "manifest.json.sig": sigraw,
             base + "reports/verify.json": verify, "/v1/log/1.json": entry}
    return FakeReg(files), (pid, ver, key, msha)


class AuditWithoutRequire(unittest.TestCase):
    """`mreg audit` without --require. As the code is (cmd_audit, audit_build, finish_row): a build passes ("OK", exit 0) when its
    signature, its reports and its log entry agree with each other. The gate statuses are printed but are NOT judged unless --require
    names the gate: a gate with status "flag" or "not run" does not fail the build. The summary line says so
    ("consistent signature, reports and log ... not a check of proofs")."""

    def audit(self, gates, require=()):
        reg, (pid, ver, key, msha) = synthetic_build(gates)
        sg = {"labels": ["flagged"], "promoted_at": "2026-11-12T00:00:00Z"}
        with mock.patch.object(M, "check_signature", lambda *a: (sg, [])), mock.patch.object(M, "chain_problems", lambda *a: []):
            return M.audit_build(reg, pid, ver, key, msha, list(require), {}), (reg, pid)

    def test_flagged_gate_without_require_passes(self):
        row, _ = self.audit({"G1": "pass", "G6": "pass", "G8": "flag"})
        self.assertEqual(row["problems"], [])
        self.assertTrue(row["ok"])
        self.assertEqual(row["gates"]["G8"], "flag")

    def test_g6_not_run_without_require_passes(self):
        row, _ = self.audit({"G1": "pass", "G6": "not run"})
        self.assertEqual(row["problems"], [])
        self.assertTrue(row["ok"])

    def test_failed_gate_without_require_also_passes(self):
        row, _ = self.audit({"G1": "pass", "G6": "fail"})
        self.assertTrue(row["ok"], "no gate is judged unless named by --require")

    def test_with_require_a_flagged_or_not_run_gate_fails(self):
        row, _ = self.audit({"G1": "pass", "G6": "not run", "G8": "flag"}, require=["G6", "G8"])
        self.assertFalse(row["ok"])
        self.assertIn("required gate G6 is not run, not pass", row["problems"])
        self.assertIn("required gate G8 is flag, not pass", row["problems"])
        row, _ = self.audit({"G1": "pass"}, require=["G6"])
        self.assertIn("required gate G6 is missing, not pass", row["problems"])

    def test_command_exit_code_and_text(self):
        reg, (pid, ver, key, msha) = synthetic_build({"G1": "pass", "G6": "not run", "G8": "flag"})
        sg = {"labels": ["flagged"], "promoted_at": "2026-11-12T00:00:00Z"}
        d = tempfile.mkdtemp(prefix="mreg-audit-")
        self.addCleanup(shutil.rmtree, d, True)
        for require, want_code in ((None, 0), ("G6", 1)):
            argv = ["-C", d, "audit", pid, "--lenient"] + (["--require", require] if require else [])   # 0.4.0: strict is the default; this is the old behaviour
            with mock.patch.object(M, "Registry", lambda token=None: reg), \
                    mock.patch.object(M, "check_signature", lambda *a: (sg, [])), mock.patch.object(M, "chain_problems", lambda *a: []):
                code, out, err = run_main(argv)
            self.assertEqual(code, want_code, out)
            self.assertIn("1 of 1 builds with consistent signature, reports and log" if want_code == 0 else "0 of 1 builds", out)
            self.assertIn("G8:flag", out)             # shown, not judged
            self.assertNotIn("G6:not run", out)       # "not run" gates are left out of the printed list


# ---------------------------------------------------------------- no prompts

class NoPrompt(unittest.TestCase):
    def test_no_call_that_reads_a_terminal(self):
        tree = ast.parse(open(os.path.join(HERE, "mreg.py"), encoding="utf-8").read())
        bad = []
        for n in ast.walk(tree):
            if isinstance(n, ast.Call):
                f = n.func
                name = f.id if isinstance(f, ast.Name) else f.attr if isinstance(f, ast.Attribute) else ""
                if name in ("input", "raw_input", "getpass", "getuser_prompt"):
                    bad.append((name, n.lineno))
            if isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name) and n.value.id == "sys" and n.attr == "stdin":
                bad.append(("sys.stdin", n.lineno))
            if isinstance(n, (ast.Import, ast.ImportFrom)):
                for a in n.names:
                    if a.name.split(".")[0] in ("getpass", "readline", "curses", "msvcrt", "termios"):
                        bad.append((a.name, n.lineno))
        self.assertEqual(bad, [])

    def test_commands_run_with_stdin_closed(self):
        with tempfile.TemporaryDirectory() as d, mock.patch("sys.stdin", None):
            code, out, err = run_main(["-C", d, "whoami"], {"MREG_TOKEN": "mreg_x"})
        self.assertNotIn("EOF", err)
        self.assertNotIn("stdin", err)


if __name__ == "__main__":
    unittest.main(verbosity=1)
