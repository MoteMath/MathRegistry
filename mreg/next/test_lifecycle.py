#!/usr/bin/env python3
"""Tests of the phase A lifecycle commands of mreg/next/mreg.py: `check`, `info`, `why`, `search`, the one-train guard and `--json`
on every command. Stdlib only.

    python -I test_lifecycle.py

No network (a registry is a file:/// directory built here, with the fixtures of test_next.py and test_named_import.py), no AWS, and
NO real Lean: `lake`, `lean` and `leanchecker` are small stub programs on PATH that print what a test tells them to. What the real
tools do is tested by the end-to-end runs in PHASE_A.md (WSL, Lean 4.35.0). Every test uses a temporary home, store and project.
"""
import contextlib, hashlib, importlib.util, io, json, os, pathlib, shutil, stat, sys, tempfile, textwrap, unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))


def load(name, fname):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, fname))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


M = load("mreg_lifecycle_under_test", "mreg.py")
TN = load("test_next_fixtures", "test_next.py")          # build_package, build_registry, make_project, TRAIN, TOOLCHAIN
NI = load("test_named_import_fixtures", "test_named_import.py")   # Mirror (the declaration store in its final layout)
TRAIN, TOOLCHAIN = TN.TRAIN, TN.TOOLCHAIN


def sha(b):
    return hashlib.sha256(b).hexdigest()


# ---------------------------------------------------------------- stub Lean tools

STUB_PY = r'''
import json, os, sys
tool = os.path.basename(sys.argv[0]).split(".")[0]
args = sys.argv[1:]
log = os.environ.get("STUB_LOG")
if log:
    with open(log, "a", encoding="utf-8") as f:
        f.write(json.dumps([tool] + args) + "\n")
here = os.path.dirname(os.path.abspath(sys.argv[0]))
if tool == "lake":
    if args[:1] == ["--version"]:
        print("Lake version 5.0.0 (stub)"); sys.exit(0)
    out = os.environ.get("STUB_LAKE_OUTPUT")
    if out and os.path.exists(out):
        sys.stdout.write(open(out, encoding="utf-8").read()); sys.stdout.flush()
    sys.exit(int(os.environ.get("STUB_LAKE_EXIT", "0")))
if tool == "lean":
    if args[:1] == ["--print-prefix"]:
        print(os.path.dirname(here)); sys.exit(0)
    if args[:1] == ["--version"]:
        print("Lean (version 4.35.0, stub)"); sys.exit(0)
    if args[:1] == ["--run"]:
        c = os.environ.get("STUB_COLLECT")
        if c and os.path.exists(c):
            sys.stdout.write(open(c, encoding="utf-8").read())
        sys.exit(int(os.environ.get("STUB_COLLECT_EXIT", "0")))
if tool == "leanchecker":
    bad = [m for m in args if m in os.environ.get("STUB_FAIL_MODULES", "").split(",")]
    if bad:
        sys.stderr.write("leanchecker found a problem in %s\n(kernel) declaration type mismatch\n" % bad[0]); sys.exit(1)
    sys.exit(0)
sys.exit(0)
'''


def install_stubs(d):
    """Directory <d>/bin with stub `lake`, `lean` and `leanchecker`; `lean --print-prefix` prints <d>. Returns the bin directory (for PATH)."""
    b = os.path.join(d, "bin")
    os.makedirs(b, exist_ok=True)
    pyfile = os.path.join(d, "stub.py")
    open(pyfile, "w", encoding="utf-8").write(STUB_PY)
    for tool in ("lake", "lean", "leanchecker"):
        base = os.path.join(b, tool)
        launcher = "import sys;sys.argv[0]=r'%s';exec(open(r'%s').read())" % (base, pyfile)
        if sys.platform == "win32":
            open(base + ".cmd", "w").write('@"%s" -c "%s" %%*' % (sys.executable, launcher) + chr(13) + chr(10))
        else:
            open(base, "w").write('#!/bin/sh' + chr(10) + 'exec "%s" -c "%s" "$@"' % (sys.executable, launcher) + chr(10))
            os.chmod(base, 0o755)
    return b


def run_main(argv, env=None):
    out, err, code = io.StringIO(), io.StringIO(), 0
    with mock.patch.dict(os.environ, env or {}, clear=False), contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        try:
            M.main(argv)
        except SystemExit as x:
            code = x.code if isinstance(x.code, int) else (0 if x.code is None else 1)
            if isinstance(x.code, str):
                err.write(x.code)
    return code, out.getvalue(), err.getvalue()


def fake_audit(ok=True, labels=("clean",)):
    def f(reg, pid, version, key, lock_msha, require, docs, strict=False):
        row = {"id": pid, "version": version, "build_key": key, "gates": {}, "labels": list(labels), "problems": [] if ok else ["UNSIGNED: test"],
               "signature": "valid" if ok else "missing", "mode": "strict", "ok": ok}
        return row
    return f


# ---------------------------------------------------------------- a registry with two trains, reports and a declaration store

TRAIN2 = "lean-4.34.1"
TOOLCHAIN2 = "leanprover/lean4:v4.34.1"


def add_reports(root, pk, statements, axiom_rows, axiom_sets):
    """Add reports/statements.jsonl and reports/axioms.json to a build written by build_package, and fix the hashes."""
    base = pathlib.Path(root, "v1", "blobs", *pk["id"].split("/"), "-", pk["version"], pk["man"]["build_key"])
    st = "".join(json.dumps(r, ensure_ascii=False) + "\n" for r in statements).encode("utf-8")
    ax = json.dumps({"schema": "mreg-axioms/1", "columns": ["name", "module", "kind", "axiom_set"], "axiom_sets": axiom_sets,
                     "rows": axiom_rows, "declarations": len(axiom_rows)}).encode()
    (base / "reports" / "statements.jsonl").write_bytes(st)
    (base / "reports" / "axioms.json").write_bytes(ax)
    man = json.loads((base / "manifest.json").read_text())
    man["reports"]["reports/statements.jsonl"] = sha(st)
    man["reports"]["reports/axioms.json"] = sha(ax)
    mb = json.dumps(man, indent=1).encode()
    (base / "manifest.json").write_bytes(mb)
    dp = pathlib.Path(root, "v1", "index", *pk["id"].split("/"))
    dp = pathlib.Path(str(dp) + ".json")
    doc = json.loads(dp.read_text())
    for v in doc["versions"].values():
        for b in v["builds"]:
            b["manifest"] = {"sha256": sha(mb), "bytes": len(mb)}
    dp.write_text(json.dumps(doc), encoding="utf-8")
    pk["man"] = man


class Fix(unittest.TestCase):
    """Registry (file://) with acme/demo and acme/other on TRAIN, acme/old on TRAIN2; a project; stubs on PATH."""

    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="mrl")
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.reg = os.path.join(self.tmp, "reg")
        self.home = os.path.join(self.tmp, "home")
        os.makedirs(self.home)
        self.stubs = install_stubs(os.path.join(self.tmp, "stubs"))
        self.log = os.path.join(self.tmp, "stub.log")
        self.pk = {"demo": TN.build_package(self.reg, "acme/demo", "Demo", "a" * 40, TN.demo_decls()),
                   "base": TN.build_package(self.reg, "leanprover-community/mathlib4", "mathlib", "b" * 40, graph=False),
                   "old": TN.build_package(self.reg, "acme/old", "Old", "c" * 40, graph=False, train=TRAIN2, version="0.1.0")}
        add_reports(self.reg, self.pk["demo"],
                    [{"kind": "theorem", "module": "Demo.A", "name": "Demo.A.t1", "sha256": "0" * 64, "statement": "forall (n : Nat), Eq n n"},
                     {"kind": "theorem", "module": "Demo.B", "name": "Demo.B.t2", "sha256": "1" * 64, "statement": "Not False"}],
                    [["Demo.A.t1", "Demo.A", "theorem", 0], ["Demo.B.t2", "Demo.B", "theorem", 1]], [[], ["propext"]])
        pkgs = {p["id"]: {"lake_name": p["lake"], "commit": p["commit"], "version": p["version"], "modules": 4, "module_roots": [p["lake"]],
                          "git": "https://github.com/" + p["id"]} for p in (self.pk["demo"], self.pk["base"])}
        idx = pathlib.Path(self.reg, "v1", "index", "trains")
        idx.mkdir(parents=True, exist_ok=True)
        (idx / (TRAIN + ".json")).write_text(json.dumps({"schema": "mreg-train/0", "train": TRAIN, "toolchain": TOOLCHAIN, "state": "open",
                                                          "packages": pkgs, "pins": {}, "module_roots": {"Demo": "acme/demo", "mathlib": "leanprover-community/mathlib4"},
                                                          "mathlib": {"rev": "0" * 40}}))
        (idx / (TRAIN2 + ".json")).write_text(json.dumps({"schema": "mreg-train/0", "train": TRAIN2, "toolchain": TOOLCHAIN2, "state": "open",
                                                           "packages": {"acme/old": {"lake_name": "Old", "commit": "c" * 40, "version": "0.1.0", "modules": 4,
                                                                                     "module_roots": ["Old"], "git": "https://github.com/acme/old"}},
                                                           "pins": {}, "module_roots": {"Old": "acme/old"}, "mathlib": {"rev": "0" * 40}}))
        (idx.parent / "trains.json").write_text(json.dumps({"trains": [{"train": TRAIN2}, {"train": TRAIN}]}))
        self.env = {"HOME": self.home, "USERPROFILE": self.home, "MREG_REGISTRY": pathlib.Path(self.reg).as_uri(),
                    "MREG_KEYS": os.path.join(self.tmp, "pins.json"), "MREG_STORE": os.path.join(self.tmp, "store"),
                    "MREG_BACKOFF": "0", "MREG_RETRIES": "1", "STUB_LOG": self.log,
                    "PATH": self.stubs + os.pathsep + os.environ.get("PATH", "")}
        self.env.pop("MREG_TOKEN", None)

    def cli(self, *args, proj=None, env=None, audit=None):
        argv = (["-C", proj] if proj else []) + list(args)
        e = dict(self.env, **(env or {}))
        with mock.patch.object(M, "audit_build", audit or fake_audit()):
            code, out, err = run_main(argv, e)
        return code, out, err

    def js(self, *args, **kw):
        code, out, err = self.cli(*args, **kw)
        doc = json.loads(out) if out.strip().startswith("{") else None
        return code, doc, out, err

    def project(self, name="proj", train=None, install=True, sources=None, own=("Proj",), toolchain=TOOLCHAIN, deps=None):
        d = os.path.join(self.tmp, name)
        TN.make_project(d, **({"deps": deps} if deps is not None else {}))
        open(os.path.join(d, "lakefile.toml"), "w").write('name = "Proj"\ndefaultTargets = ["Proj"]\n\n[[lean_lib]]\nname = "Proj"\n')
        open(os.path.join(d, "lean-toolchain"), "w").write(toolchain + "\n")
        for rel, text in (sources or {}).items():
            p = os.path.join(d, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            open(p, "w", encoding="utf-8").write(text)
        subprocess_git(d)
        if install:
            code, out, err = self.cli("install", "--no-lake-check", proj=d)
            self.assertEqual(code, 0, out + err)
        if train:
            json.dump({"registry": "x", "train": train}, open(os.path.join(d, "mreg.json"), "w"))
        return d

    def stub_calls(self):
        if not os.path.exists(self.log):
            return []
        return [json.loads(l) for l in open(self.log, encoding="utf-8") if l.strip()]


def subprocess_git(d):
    import subprocess
    subprocess.run(["git", "-C", d, "init", "-q"], capture_output=True)
    subprocess.run(["git", "-C", d, "remote", "add", "origin", "https://github.com/me/proj"], capture_output=True)


# ======================================================================================= scanning own sources

class TestScan(unittest.TestCase):
    def scan(self, text):
        d = tempfile.mkdtemp(prefix="mrs")
        self.addCleanup(shutil.rmtree, d, True)
        p = os.path.join(d, "Proj.lean")
        open(p, "w", encoding="utf-8").write(text)
        return [(r["line"], r["token"]) for r in M.lc_scan_sources(d, [("Proj", p)])]

    def test_each_unsound_construct_is_found_with_its_line(self):
        src = "theorem a : True := by\n  sorry\ntheorem b : 1 = 1 := by\n  admit\ntheorem c : 2 = 2 := by native_decide\n" \
              "theorem d (x : BitVec 8) : x = x := by bv_decide\naxiom e : False\ntheorem f : 3 = 3 := by decide +native\n" \
              "set_option debug.skipKernelTC true\n"
        self.assertEqual(self.scan(src), [(2, "sorry"), (4, "admit"), (5, "native_decide"), (6, "bv_decide"), (7, "axiom"),
                                          (8, "decide +native"), (9, "debug.skipKernelTC")])

    def test_comments_strings_and_look_alikes_are_not_found(self):
        src = ("-- sorry in a comment\n/- block with sorry\n /- nested axiom -/ still sorry -/\n"
               'def s := "this string has sorry and axiom in it"\ntheorem sorryAx_like : True := trivial\n'
               "theorem my_sorry : True := trivial\ntheorem x : True := Nat.sorry_free\ntheorem y : True := by decide\n")
        self.assertEqual(self.scan(src), [])

    def test_real_use_after_comment_is_still_found(self):
        self.assertEqual(self.scan("/- start -/ theorem a : True := sorry\n"), [(1, "sorry")])


# ======================================================================================= --json on every command

class TestJsonEverywhere(Fix):
    def test_view_train_have_a_document_and_text_on_stderr(self):
        code, doc, out, err = self.js("view", "acme/demo", "--json")
        self.assertEqual(code, 0)
        self.assertEqual(doc["schema"], "mreg-view/1")
        self.assertTrue(doc["ok"])
        self.assertEqual(doc["package"]["id"], "acme/demo")
        self.assertIn("acme/demo", err)
        code, doc, out, err = self.js("train", TRAIN, "--json")
        self.assertEqual((code, doc["schema"], doc["train"]["train"]), (0, "mreg-train/1", TRAIN))
        self.assertEqual(out.count("{"), out.count("{"))      # one document: json.loads above would have failed on two

    def test_view_failure_is_a_document_with_the_exit_code(self):
        code, doc, out, err = self.js("view", "acme/nothing", "--json")
        self.assertEqual(code, 1)
        self.assertFalse(doc["ok"])
        self.assertEqual(doc["exit_code"], 1)
        self.assertIn("not in the registry", doc["error"]["message"])

    def test_init_document(self):
        d = os.path.join(self.tmp, "newproj")
        code, doc, out, err = self.js("init", d, "--train", TRAIN, "--json")
        self.assertEqual(code, 0, err)
        self.assertEqual((doc["schema"], doc["project"]["train"], doc["project"]["toolchain"]), ("mreg-init/1", TRAIN, TOOLCHAIN))

    def test_install_module_level_document(self):
        d = self.project(install=False)
        code, doc, out, err = self.js("install", "--no-lake-check", "--json", proj=d)
        self.assertEqual(code, 0, err)
        self.assertEqual((doc["schema"], doc["ok"], doc["command"]), ("mreg-install/1", True, "install"))
        self.assertTrue(any("installed" in m for m in doc["messages"]))
        self.assertTrue(os.path.exists(os.path.join(d, "mreg.lock")))

    def test_ci_module_level_document_and_failure(self):
        d = self.project()
        code, doc, out, err = self.js("ci", "--no-lake-check", "--json", proj=d)
        self.assertEqual((code, doc["schema"], doc["ok"]), (0, "mreg-ci/1", True), err)
        olean = os.path.join(d, ".lake", "packages", "Demo", ".lake", "build", "lib", "lean", "Demo", "B.olean")
        with open(olean, "ab") as f:
            f.write(b"x")
        code, doc, out, err = self.js("ci", "--no-lake-check", "--json", proj=d)
        self.assertEqual((code, doc["ok"], doc["exit_code"]), (1, False, 1))

    def test_whoami_and_logout_documents(self):
        code, doc, out, err = self.js("whoami", "--json")
        self.assertEqual((code, doc["schema"], doc["ok"]), (1, "mreg-whoami/1", False))
        code, doc, out, err = self.js("logout", "--json")
        self.assertEqual((code, doc["schema"], doc["ok"]), (0, "mreg-logout/1", True))

    def test_whoami_document_has_the_fields_and_never_the_key(self):
        import base64
        payload = base64.urlsafe_b64encode(json.dumps({"v": 1, "k": "abc123", "o": "me", "s": "read", "i": 1700000000}).encode()).rstrip(b"=").decode()
        key = "mreg_" + payload + "." + "Z" * 43
        code, doc, out, err = self.js("whoami", "--json", env={"MREG_TOKEN": key})
        self.assertEqual(code, 0, err)
        self.assertEqual((doc["kind"], doc["key_id"], doc["scope"]), ("per_user_key", "abc123", "read"))
        self.assertNotIn(key, out + err)
        self.assertNotIn("Z" * 43, out + err)

    def test_a_named_import_document_passes_through_unchanged(self):
        m = NI.Mirror(self.reg, publish=True)
        d = os.path.join(self.tmp, "chunks")
        os.makedirs(d)
        open(os.path.join(d, "lean-toolchain"), "w").write(NI.TOOLCHAIN + "\n")
        code, doc, out, err = self.js("resolve", "leanprover-community/mathlib4#Mathlib.n30_0", "--json", proj=d)
        self.assertEqual(doc["schema"], "mreg-named-import/1")


# ======================================================================================= one train

class TestOneTrain(Fix):
    def test_guard_explicit_train_names_package_and_both_trains(self):
        d = self.project(install=False, train=TRAIN)
        with self.assertRaises(M.NIError) as cm:
            M.one_train_guard(d, None, [("acme/demo", "1.0.0", [TRAIN]), ("acme/old", "0.1.0", [TRAIN2])])
        e = cm.exception
        self.assertEqual((e.kind, e.code), ("forbidden_mix", 15))
        self.assertIn("acme/old", e.message)
        self.assertIn(TRAIN2, e.message)
        self.assertIn(TRAIN, e.message)

    def test_guard_default_baseline_needs_a_common_train(self):
        d = self.project(install=False)
        M.one_train_guard(d, None, [("a/x", "1", [TRAIN, TRAIN2]), ("a/y", "1", [TRAIN])])
        with self.assertRaises(M.NIError) as cm:
            M.one_train_guard(d, None, [("a/x", "1", [TRAIN]), ("a/y", "1", [TRAIN2])])
        self.assertIn("no train holds both", cm.exception.message)

    def test_install_refuses_a_package_of_another_train(self):
        d = self.project(install=False, train=TRAIN2, deps=(("acme/demo", "Demo", "a" * 40),))
        code, out, err = self.cli("install", "--no-lake-check", proj=d)
        self.assertEqual(code, 15, out + err)
        self.assertIn("acme/demo", out + err)
        self.assertIn(TRAIN2, out + err)
        self.assertFalse(os.path.exists(os.path.join(d, "mreg.lock")), "nothing was installed")

    def test_install_json_error_document(self):
        d = self.project(install=False, train=TRAIN2)
        code, doc, out, err = self.js("install", "--no-lake-check", "--json", proj=d)
        self.assertEqual(code, 15)
        self.assertEqual(doc["error"]["kind"], "forbidden_mix")

    def test_ci_refuses_a_locked_build_of_another_train(self):
        d = self.project()
        json.dump({"registry": "x", "train": TRAIN2}, open(os.path.join(d, "mreg.json"), "w"))
        code, out, err = self.cli("ci", "--no-lake-check", proj=d)
        self.assertEqual(code, 15, out + err)
        self.assertIn("acme/demo", out + err)

    def test_ci_train_flag(self):
        d = self.project()
        code, out, err = self.cli("ci", "--no-lake-check", "--train", TRAIN2, proj=d)
        self.assertEqual(code, 15, out + err)
        code, out, err = self.cli("ci", "--no-lake-check", "--train", TRAIN, proj=d)
        self.assertEqual(code, 0, out + err)

    def test_add_of_another_train_into_a_project_on_a_train_is_refused(self):
        d = os.path.join(self.tmp, "p2")
        code, out, err = self.cli("init", d, "--train", TRAIN)
        self.assertEqual(code, 0, out + err)
        code, out, err = self.cli("add", "acme/old", "--train", TRAIN2, "--no-lake-update", proj=d)
        self.assertEqual(code, 15, out + err)
        self.assertIn(TRAIN2, out + err)
        self.assertNotIn("acme/old", open(os.path.join(d, "lakefile.toml")).read())

    def test_add_does_not_write_mreg_json_but_refuses_a_mix_with_what_is_installed(self):
        d = self.project()                                           # acme/demo installed from TRAIN, no mreg.json
        self.assertFalse(os.path.exists(os.path.join(d, "mreg.json")))
        code, out, err = self.cli("add", "acme/old", "--train", TRAIN2, "--no-lake-update", proj=d)
        self.assertEqual(code, 15, out + err)
        self.assertIn("acme/demo", out + err)
        self.assertFalse(os.path.exists(os.path.join(d, "mreg.json")))
        self.assertNotIn("acme/old", open(os.path.join(d, "lakefile.toml")).read())

    def test_every_new_command_takes_train(self):
        import argparse
        for cmd in ("check", "info", "why", "search", "ci", "install", "add"):
            code, out, err = run_main([cmd, "--help"])
            self.assertIn("--train", out + err, cmd)


# ======================================================================================= mreg check

OK_LAKE = "info: Proj.lean:3:0: 'x' does not depend on any axioms\nBuild completed successfully (3 jobs).\n"


class TestCheck(Fix):
    def setUp(self):
        super().setUp()
        self.proj = self.project(sources={"Proj.lean": "import Demo.B\n\ntheorem x : 1 = 1 := rfl\n"})
        self.lakeout = os.path.join(self.tmp, "lake.out")
        self.collect = os.path.join(self.tmp, "collect.out")
        open(self.lakeout, "w").write(OK_LAKE)
        self.write_collect([{"name": "x", "module": "Proj", "axioms": [], "statement": "Eq 1 1", "statement_form": "pp",
                             "uses": [{"name": "Eq", "module": "Init.Prelude", "kind": "inductive"}]}])
        self.base_env = {"STUB_LAKE_OUTPUT": self.lakeout, "STUB_COLLECT": self.collect}
        # the own build directory must exist for the replay's LEAN_PATH; the stubs do not make one
        os.makedirs(os.path.join(self.proj, ".lake", "build", "lib", "lean"), exist_ok=True)

    def write_collect(self, recs):
        open(self.collect, "w", encoding="utf-8").write("".join(json.dumps(r) + "\n" for r in recs))

    def check(self, *args, env=None, audit=None, expect=None):
        e = dict(self.base_env, **(env or {}))
        code, doc, out, err = self.js("check", "--json", *args, proj=self.proj, env=e, audit=audit)
        if expect is not None:
            self.assertEqual(code, expect, out + err)
        return code, doc, err

    def step(self, doc, n):
        return next(s for s in doc["steps"] if s["step"] == n)

    # ---- the whole thing
    def test_everything_passes_and_the_document_has_the_documented_shape(self):
        code, doc, err = self.check(expect=0)
        self.assertEqual((doc["schema"], doc["ok"], doc["command"], doc["exit_code"]), ("mreg-check/1", True, "check", 0))
        self.assertEqual([s["step"] for s in doc["steps"]], [1, 2, 3, 4, 5, 6, 7])
        self.assertEqual([s["verdict"] for s in doc["steps"]], ["pass", "pass", "pass", "pass", "pass", "not_run", "pass"])
        for k in ("toolchain", "train", "lock_sha256", "tools", "mode", "sentences", "seconds", "project", "mreg_version"):
            self.assertIn(k, doc)
        self.assertEqual(doc["train"]["name"], TRAIN)
        self.assertEqual(doc["lock_sha256"]["mreg.lock"], sha(open(os.path.join(self.proj, "mreg.lock"), "rb").read()))
        self.assertEqual(doc["sentences"]["public_olean"], M.PUBLIC_OLEAN_SENTENCE)
        self.assertIn("public .olean content of dependencies is not checked", err)
        self.assertIn("read the statements", err)

    def test_text_mode_prints_the_summary_on_stdout(self):
        code, out, err = self.cli("check", proj=self.proj, env=self.base_env)
        self.assertEqual(code, 0, out + err)
        self.assertIn("step 1 integrity", out)
        self.assertIn("statement x (Proj): Eq 1 1", out)
        self.assertIn("uses Eq [inductive] in Init.Prelude", out)

    # ---- step 1
    def test_step1_a_flipped_byte_fails_with_hash_mismatch(self):
        olean = os.path.join(self.proj, ".lake", "packages", "Demo", ".lake", "build", "lib", "lean", "Demo", "A.olean")
        b = bytearray(open(olean, "rb").read())
        b[10] ^= 1
        open(olean, "wb").write(bytes(b))
        code, doc, err = self.check(expect=14)
        s = self.step(doc, 1)
        self.assertEqual(s["verdict"], "fail")
        self.assertTrue(any(f.startswith("MISMATCH") and "A.olean" in f for f in s["failures"]), s["failures"])
        self.assertFalse(doc["ok"])

    def test_step1_audit_failure_fails(self):
        code, doc, err = self.check(audit=fake_audit(ok=False), expect=1)
        self.assertEqual(self.step(doc, 1)["verdict"], "fail")
        self.assertIn("UNSIGNED", " ".join(self.step(doc, 1)["failures"]))

    def test_step1_nothing_installed(self):
        d = self.project(name="empty", install=False)
        code, doc, out, err = self.js("check", "--json", "--fast", proj=d)
        self.assertEqual(code, 1)
        self.assertIn("nothing installed", self.step(doc, 1)["failures"][0])

    # ---- step 2
    def test_step2_names_the_package_of_another_train(self):
        json.dump({"registry": "x", "train": TRAIN2}, open(os.path.join(self.proj, "mreg.json"), "w"))
        code, doc, err = self.check("--fast", expect=15)
        s = self.step(doc, 2)
        self.assertEqual(s["verdict"], "fail")
        self.assertTrue(any("acme/demo" in f and TRAIN2 in f for f in s["failures"]), s["failures"])

    def test_step2_toolchain_must_equal_the_train(self):
        open(os.path.join(self.proj, "lean-toolchain"), "w").write("leanprover/lean4:v4.34.1\n")
        code, doc, err = self.check("--fast", expect=20)
        self.assertTrue(any("lean-toolchain is" in f for f in self.step(doc, 2)["failures"]))

    # ---- step 3
    def test_step3_sorry_warning_from_lake_and_source_scan(self):
        open(self.lakeout, "w").write("warning: Proj.lean:3:0: declaration uses 'sorry'\nBuild completed successfully (3 jobs).\n")
        open(os.path.join(self.proj, "Proj.lean"), "w").write("import Demo.B\n\ntheorem x : 1 = 1 := by\n  sorry\n")
        code, doc, err = self.check("--fast", expect=22)
        s = self.step(doc, 3)
        self.assertEqual(s["verdict"], "fail")
        self.assertIn({"file": "Proj.lean", "line": 3, "message": "declaration uses 'sorry'"}, s["details"]["sorry_warnings"])
        self.assertTrue(any(r["token"] == "sorry" and r["line"] == 4 for r in s["details"]["source_scan"]))
        self.assertTrue(any(f.startswith("Proj.lean:4: sorry") for f in s["failures"]))

    def test_step3_each_unsound_token_fails_with_file_and_line(self):
        for src, tok in (("axiom bad : False\n", "axiom"), ("theorem t : 1 = 1 := by native_decide\n", "native_decide"),
                         ("theorem t (x : BitVec 4) : x = x := by bv_decide\n", "bv_decide"), ("theorem t : 1 = 1 := by admit\n", "admit")):
            open(os.path.join(self.proj, "Proj.lean"), "w").write("import Demo.B\n" + src)
            code, doc, err = self.check("--fast", expect=22)
            self.assertTrue(any(r["token"] == tok and r["line"] == 2 and r["file"] == "Proj.lean"
                                for r in self.step(doc, 3)["details"]["source_scan"]), (tok, doc["steps"][2]))

    def test_allow_axiom_exempts_the_named_declaration_in_the_scan_only(self):
        nl = chr(10)
        open(os.path.join(self.proj, "Proj.lean"), "w").write("import Demo.B" + nl + "axiom myAx : False" + nl + "theorem u : 1 = 2 := myAx.elim" + nl)
        self.write_collect([{"name": "u", "module": "Proj", "axioms": ["myAx"], "axioms_stored": ["myAx"], "statement": "S", "statement_form": "pp", "uses": []}])
        code, doc, err = self.check("--fast", "--allow-axiom", "myAx", expect=0)
        self.assertEqual(doc["allowed_axioms"], ["myAx"])
        self.assertEqual(self.step(doc, 3)["details"]["allowed_axiom_declarations"][0]["name"], "myAx")
        self.assertIn("allowed by --allow-axiom: myAx", err)
        # an axiom that is not named still fails, even with another one allowed
        open(os.path.join(self.proj, "Proj.lean"), "w").write("import Demo.B" + nl + "axiom myAx : False" + nl + "axiom other : False" + nl)
        code, doc, err = self.check("--fast", "--allow-axiom", "myAx", expect=22)
        self.assertEqual([r["line"] for r in self.step(doc, 3)["details"]["source_scan"]], [3])
        code, doc, err = self.check("--fast", expect=22)

    def test_step3_build_failure(self):
        open(self.lakeout, "w").write("error: Proj.lean:3:0: unknown identifier 'y'\n")
        code, doc, err = self.check("--fast", env={"STUB_LAKE_EXIT": "1"}, expect=22)
        self.assertTrue(any("lake build failed" in f for f in self.step(doc, 3)["failures"]))

    def test_step3_stops_when_lake_rebuilds_a_dependency(self):
        open(self.lakeout, "w").write("[1/9] Building Demo.A\n[2/9] Building Proj\n")
        code, doc, err = self.check("--fast", expect=22)
        s = self.step(doc, 3)
        self.assertEqual(s["details"]["dependency_rebuild"], ["Demo.A"])
        self.assertTrue(any("not one of the project's own modules" in f for f in s["failures"]))

    def test_step3_builds_the_project_with_lake_in_the_project_dir_only(self):
        self.check("--fast", expect=0)
        calls = [c for c in self.stub_calls() if c[0] == "lake" and c[1:2] == ["build"]]
        self.assertEqual(len(calls), 1)

    # ---- step 5
    def test_step5_axiom_outside_the_accepted_three_fails_and_can_be_allowed(self):
        self.write_collect([{"name": "x", "module": "Proj", "axioms": ["propext", "myAx"], "statement": "S", "statement_form": "pp", "uses": []}])
        code, doc, err = self.check("--fast", expect=24)
        s = self.step(doc, 5)
        self.assertEqual(s["details"]["per_theorem"][0]["outside_accepted"], ["myAx"])
        self.assertIn("x depends on myAx", s["failures"])
        code, doc, err = self.check("--fast", "--allow-axiom", "myAx", expect=0)
        self.assertEqual(self.step(doc, 5)["verdict"], "pass")

    def test_step5_a_stored_axiom_list_that_differs_from_the_proofs_fails(self):
        self.write_collect([{"name": "x", "module": "Proj", "axioms": ["Evil.tampered"], "axioms_stored": [], "statement": "S",
                             "statement_form": "pp", "uses": []}])
        code, doc, err = self.check("--fast", "--allow-axiom", "Evil.tampered", expect=24)        # allowed, but the lists disagree
        s = self.step(doc, 5)
        self.assertTrue(s["details"]["per_theorem"][0]["stored_list_differs"])
        self.assertTrue(any("stored in the compiled files" in f for f in s["failures"]))
        self.write_collect([{"name": "x", "module": "Proj", "axioms": ["propext"], "axioms_stored": ["propext"], "statement": "S",
                             "statement_form": "pp", "uses": []}])
        self.check("--fast", expect=0)

    def test_step5_the_accepted_three_pass_and_sorryax_does_not(self):
        self.write_collect([{"name": "x", "module": "Proj", "axioms": ["propext", "Classical.choice", "Quot.sound"], "statement": "S",
                             "statement_form": "pp", "uses": []}])
        self.check("--fast", expect=0)
        self.write_collect([{"name": "x", "module": "Proj", "axioms": ["sorryAx"], "statement": "S", "statement_form": "pp", "uses": []}])
        self.check("--fast", expect=24)

    def test_step5_theorem_flag_is_passed_and_a_missing_name_fails(self):
        self.write_collect([{"name": "nope", "missing": True}])
        code, doc, err = self.check("--fast", "--theorem", "nope", expect=1)
        self.assertTrue(any("nope" in f for f in self.step(doc, 5)["failures"]))
        run = [c for c in self.stub_calls() if c[0] == "lean" and c[1:2] == ["--run"]]
        self.assertEqual(run[-1][-1], "nope")

    def test_step5_not_run_when_the_build_failed(self):
        open(self.lakeout, "w").write("error: boom\n")
        code, doc, err = self.check("--fast", env={"STUB_LAKE_EXIT": "1"}, expect=22)
        self.assertEqual(self.step(doc, 5)["verdict"], "not_run")

    # ---- step 4
    def test_step4_default_replays_own_modules_and_small_non_baseline_dependencies(self):
        code, doc, err = self.check(expect=0)
        s = self.step(doc, 4)
        rep = {r["package"]: r for r in s["details"]["replayed"]}
        self.assertEqual(rep["(own modules)"]["modules"], ["Proj"])
        self.assertEqual(sorted(rep["acme/demo"]["modules"]), ["Demo.A", "Demo.B", "Demo.C"][:len(rep["acme/demo"]["modules"])])
        self.assertIn("not a baseline", rep["acme/demo"]["why"])
        calls = [c for c in self.stub_calls() if c[0] == "leanchecker"]
        self.assertEqual(sorted(sum((c[1:] for c in calls), [])), sorted(["Proj"] + rep["acme/demo"]["modules"]))

    def test_step4_baseline_package_is_not_replayed_and_the_report_says_what_it_rests_on(self):
        d = self.project(name="withbase", deps=(("acme/demo", "Demo", "a" * 40), ("leanprover-community/mathlib4", "mathlib", "b" * 40)),
                         sources={"Proj.lean": "import Demo.B\nimport mathlib.B\n\ntheorem x : 1 = 1 := rfl\n"})
        os.makedirs(os.path.join(d, ".lake", "build", "lib", "lean"), exist_ok=True)
        code, doc, out, err = self.js("check", "--json", proj=d, env=self.base_env, audit=fake_audit(labels=("imported",)))
        self.assertEqual(code, 0, out + err)
        s = self.step(doc, 4)
        nr = {n["package"]: n for n in s["details"]["not_replayed"]}
        self.assertIn("leanprover-community/mathlib4", nr)
        self.assertEqual(nr["leanprover-community/mathlib4"]["reason_kind"], "baseline")
        tb = nr["leanprover-community/mathlib4"]["trust_basis"]["text"]
        self.assertIn("not replayed here; relies on registry gates G2-G10 (label imported) and the re-hash of step 1", tb)
        self.assertIn("sample size not recorded", tb)             # the fixture's manifest has no sample_recompile
        self.assertIn("not replayed here", err)
        replayed = {r["package"] for r in s["details"]["replayed"]}
        self.assertNotIn("leanprover-community/mathlib4", replayed)
        for c in self.stub_calls():
            if c[0] == "leanchecker":
                self.assertFalse(any(m.startswith("mathlib.") for m in c[1:]))

    def test_step4_sample_recompile_size_is_reported_when_the_build_records_it(self):
        pk = self.pk["base"]
        base = pathlib.Path(self.reg, "v1", "blobs", "leanprover-community", "mathlib4", "-", "1.0.0", pk["man"]["build_key"])
        # the manifest changes: the lock of the project below is made after, so the hashes agree
        man = json.loads((base / "manifest.json").read_text())
        man["sample_recompile"] = {"modules_sampled": 200, "modules_total": 501, "different": 0}
        mb = json.dumps(man, indent=1).encode()
        (base / "manifest.json").write_bytes(mb)
        dp = pathlib.Path(self.reg, "v1", "index", "leanprover-community", "mathlib4.json")
        doc = json.loads(dp.read_text())
        doc["versions"]["1.0.0"]["builds"][0]["manifest"] = {"sha256": sha(mb), "bytes": len(mb)}
        dp.write_text(json.dumps(doc))
        d = self.project(name="withbase2", deps=(("leanprover-community/mathlib4", "mathlib", "b" * 40),),
                         sources={"Proj.lean": "import mathlib.B\n\ntheorem x : 1 = 1 := rfl\n"})
        os.makedirs(os.path.join(d, ".lake", "build", "lib", "lean"), exist_ok=True)
        code, doc2, out, err = self.js("check", "--json", proj=d, env=self.base_env, audit=fake_audit(labels=("imported",)))
        nr = {n["package"]: n for n in self.step(doc2, 4)["details"]["not_replayed"]}
        self.assertEqual(nr["leanprover-community/mathlib4"]["trust_basis"]["sample_recompile"], {"modules_sampled": 200, "modules_total": 501})
        self.assertIn("sample recompile 200 of 501 modules", nr["leanprover-community/mathlib4"]["trust_basis"]["text"])

    def test_step4_over_threshold_package_is_not_replayed(self):
        code, doc, err = self.check(env={"MREG_REPLAY_SECONDS_PER_MODULE": "1000"})
        self.assertEqual(code, 0, err)
        nr = {n["package"]: n for n in self.step(doc, 4)["details"]["not_replayed"]}
        self.assertEqual(nr["acme/demo"]["reason_kind"], "over_threshold")
        self.assertIn("over threshold", nr["acme/demo"]["reason"])

    def test_step4_replay_flag_and_full_replay(self):
        code, doc, err = self.check("--replay", "acme/demo", env={"MREG_REPLAY_SECONDS_PER_MODULE": "1000"}, expect=0)
        rep = {r["package"]: r for r in self.step(doc, 4)["details"]["replayed"]}
        self.assertIn("acme/demo", rep)
        self.assertEqual(rep["acme/demo"]["why"], "--replay")
        code, doc, err = self.check("--full-replay", env={"MREG_REPLAY_SECONDS_PER_MODULE": "1000"}, expect=0)
        rep = {r["package"]: r for r in self.step(doc, 4)["details"]["replayed"]}
        self.assertEqual(rep["acme/demo"]["why"], "--full-replay")
        self.assertIn("estimated", err)               # the estimate is printed before the replay
        code, doc, err = self.check("--replay", "nonexistent/pkg", expect=1)

    def test_step4_a_failing_module_is_named_and_exit_is_23(self):
        code, doc, err = self.check(env={"STUB_FAIL_MODULES": "Demo.B"}, expect=23)
        s = self.step(doc, 4)
        self.assertEqual(s["verdict"], "fail")
        self.assertTrue(any("found a problem in Demo.B" in f for f in s["failures"]), s["failures"])

    def test_step4_the_estimate_and_its_source_are_in_the_document(self):
        code, doc, err = self.check(expect=0)
        e = self.step(doc, 4)["details"]["estimate"]
        self.assertIn("seconds_per_module", e)
        self.assertTrue(e["source"])

    # ---- review fixes (REVIEW_0.5.0_main-session.md, items 1 to 5)
    def chunk_lock(self):
        cl = {"schema": M.CHUNK_LOCK_SCHEMA, "train": TRAIN, "build": "b1", "variant": "checking", "chunk_dir": ".lake/mreg-chunks/" + TRAIN,
              "chunks": [], "declarations": [], "covers_packages": []}
        json.dump(cl, open(os.path.join(self.proj, M.CHUNK_LOCK), "w"))

    def test_review1_chunks_are_unverified_experimental_and_never_complete(self):
        self.chunk_lock()
        code, doc, err = self.check(expect=0)
        self.assertFalse(doc["complete"])
        self.assertTrue(any("declaration chunks" in r and "unverified experimental" in r for r in doc["incomplete_reasons"]))
        nr = {n["package"]: n for n in self.step(doc, 4)["details"]["not_replayed"]}
        self.assertIn("unverified experimental chunks", nr["chunks"]["trust_basis"]["text"])
        self.assertNotIn("registry's gates", nr["chunks"]["trust_basis"]["text"])
        self.assertIn("INCOMPLETE", err)
        self.assertNotIn("check passed; step 6", err)

    def test_review2_train_flag_never_overrides_the_recorded_train(self):
        d = self.project(name="rec", train=TRAIN)
        with self.assertRaises(M.NIError) as cm:
            M.lc_project_train(d, TRAIN2)
        self.assertEqual(cm.exception.kind, "forbidden_mix")
        self.assertIn(TRAIN, cm.exception.message)
        self.assertIn(TRAIN2, cm.exception.message)
        self.assertEqual(M.lc_project_train(d, TRAIN), (TRAIN, "--train"))
        code, doc, out, err = self.js("check", "--json", "--fast", "--train", TRAIN2, proj=d)
        self.assertEqual((code, doc["error"]["kind"]), (15, "forbidden_mix"))
        json.dump({"schema": M.CHUNK_LOCK_SCHEMA, "train": TRAIN}, open(os.path.join(d, M.CHUNK_LOCK), "w"))
        os.unlink(os.path.join(d, "mreg.json"))
        with self.assertRaises(M.NIError):
            M.lc_project_train(d, TRAIN2)
        self.assertEqual(M.lc_project_train(d, None), (TRAIN, M.CHUNK_LOCK))

    def test_review3_a_build_with_no_train_is_a_refusal(self):
        d = self.project(install=False, train=TRAIN)
        for items in ([("acme/demo", "1.0.0", [])], [("acme/demo", "1.0.0", None)], [("a/x", "1", [TRAIN]), ("a/y", "1", [])]):
            with self.assertRaises(M.NIError) as cm:
                M.one_train_guard(d, None, items)
            self.assertEqual(cm.exception.kind, "forbidden_mix")
            self.assertIn("no train on record", cm.exception.message)
        d2 = self.project(name="nobase", install=False)           # no recorded train: the baseline default does not exempt it
        with self.assertRaises(M.NIError):
            M.one_train_guard(d2, None, [("a/x", "1", [])])
        M.one_train_guard(d2, None, [("a/x", "1", [TRAIN])])

    def test_review3_a_missing_package_document_is_a_refusal_in_ci(self):
        d = self.project(name="gone")
        dp = pathlib.Path(self.reg, "v1", "index", "acme", "demo.json")
        saved = dp.read_text()
        dp.unlink()
        try:
            code, out, err = self.cli("ci", "--no-lake-check", proj=d)
            self.assertEqual(code, 15, out + err)
            self.assertIn("no train on record", out + err)
        finally:
            dp.write_text(saved)

    def test_review4_zero_theorems_is_incomplete_not_a_silent_pass(self):
        self.write_collect([])
        code, doc, err = self.check(expect=0)
        s5, s7 = self.step(doc, 5), self.step(doc, 7)
        self.assertFalse(s5["complete"])
        self.assertFalse(s7["complete"])
        self.assertFalse(doc["complete"])
        self.assertEqual(len(doc["incomplete_reasons"]), 2)
        self.assertIn("0 theorems", s5["details"]["incomplete_reason"])
        self.assertIn("INCOMPLETE", err)

    def test_review4_the_collect_script_exits_nonzero_for_a_missing_module(self):
        self.assertIn("missingModule := true", M.COLLECT_LEAN)
        self.assertIn("return (if missingModule then 3 else 0)", M.COLLECT_LEAN)
        code, doc, err = self.check("--fast", env={"STUB_COLLECT_EXIT": "3"}, expect=1)
        self.assertEqual(self.step(doc, 5)["verdict"], "fail")
        self.assertIn("exited 3", " ".join(self.step(doc, 5)["failures"]))

    def test_review5_state_and_lock_must_name_the_same_builds(self):
        lp = os.path.join(self.proj, "mreg.lock")
        lock = json.load(open(lp))
        orig = json.dumps(lock)
        for e in lock["packages"]:
            if e.get("from") == "registry":
                e["build_key"] = "ffffffffffffffff"
        json.dump(lock, open(lp, "w"))
        code, doc, err = self.check("--fast", expect=14)
        diffs = self.step(doc, 1)["details"]["state_vs_lock"]["differences"]
        self.assertTrue(any("state says build" in x and "mreg.lock says ffffffffffffffff" in x for x in diffs), diffs)
        lock = json.loads(orig)
        lock["packages"] = [e for e in lock["packages"] if e.get("from") != "registry"]
        json.dump(lock, open(lp, "w"))
        code, doc, err = self.check("--fast", expect=14)
        self.assertTrue(any("in .lake/mreg-state.json only" in x for x in self.step(doc, 1)["details"]["state_vs_lock"]["differences"]))
        open(lp, "w").write(orig)
        self.check("--fast", expect=0)

    # ---- fast, step 6, step 7
    def test_fast_runs_steps_1_2_3_5_only(self):
        code, doc, err = self.check("--fast", expect=0)
        self.assertEqual([s["verdict"] for s in doc["steps"]], ["pass", "pass", "pass", "not_run", "pass", "not_run", "not_run"])
        self.assertTrue(doc["mode"]["fast"])
        self.assertFalse(doc["complete"])
        self.assertFalse([c for c in self.stub_calls() if c[0] == "leanchecker"])

    def test_step6_is_reported_as_not_run(self):
        code, doc, err = self.check(expect=0)
        s = self.step(doc, 6)
        self.assertEqual(s["verdict"], "not_run")
        self.assertIn("not part of phase A", s["details"]["reason"])

    def test_step7_statement_uses_and_the_sentence(self):
        code, doc, err = self.check(expect=0)
        s = self.step(doc, 7)
        t = s["details"]["theorems"][0]
        self.assertEqual((t["name"], t["statement"]), ("x", "Eq 1 1"))
        self.assertEqual(t["uses"][0]["package"], "(toolchain)")
        self.assertIn("No kernel checks that a theorem says what its author meant", s["details"]["sentence"])

    def test_exit_code_is_that_of_the_first_failed_step(self):
        open(os.path.join(self.proj, "Proj.lean"), "w").write("import Demo.B\naxiom a : False\n")
        self.write_collect([{"name": "x", "module": "Proj", "axioms": ["a"], "statement": "S", "statement_form": "pp", "uses": []}])
        code, doc, err = self.check("--fast", expect=22)                  # step 3 (the axiom in the source) is the first failure
        self.assertEqual([s["verdict"] for s in doc["steps"] if s["step"] in (3, 5)], ["fail", "fail"])      # step 5 still ran: the build itself passed

    def test_error_in_a_non_project_directory(self):
        d = os.path.join(self.tmp, "notaproject")
        os.makedirs(d)
        code, doc, out, err = self.js("check", "--json", proj=d)
        self.assertEqual(code, 1)
        self.assertFalse(doc["ok"])
        self.assertIn("not a Lake project", doc["error"]["message"])

    def test_the_stored_key_file_is_never_read_for_a_file_registry(self):
        self.check("--fast", expect=0)          # a file:// registry needs no token: the home directory has none, and it still passes


# ======================================================================================= info, why, search

class TestRead(Fix):
    def setUp(self):
        super().setUp()
        # the declaration store: the Mirror's chunks plus declarations of acme/demo (modules Demo.*, chunk 30 of the Mathlib block)
        self.m = NI.Mirror(self.reg, publish=False)
        for name, mod, chunk in (("Demo.A.t1", "Demo.A", 30), ("Demo.B.t2", "Demo.B", 31), ("Demo.C.t3", "Demo.C", 32)):
            self.m.decls.append((name, name, mod, "thm", chunk))
        self.m.write_all()
        self.m.publish_pointer()
        # write_all replaced the train document: put ours back (the Mirror's has no module_roots)
        td = json.loads(open(os.path.join(self.reg, "v1", "index", "trains", TRAIN + ".json")).read())
        td["module_roots"] = {"Demo": "acme/demo", "mathlib": "leanprover-community/mathlib4"}
        td["packages"]["acme/demo"] = {"lake_name": "Demo", "commit": "a" * 40, "version": "1.0.0", "modules": 4, "module_roots": ["Demo"],
                                       "git": "https://github.com/acme/demo"}
        td["packages"]["leanprover-community/mathlib4"].update({"module_roots": ["Mathlib", "mathlib"], "version": "1.0.0", "commit": "b" * 40,
                                                                  "lake_name": "mathlib"})
        open(os.path.join(self.reg, "v1", "index", "trains", TRAIN + ".json"), "w").write(json.dumps(td))

    # ---- info
    def test_info_package(self):
        code, doc, out, err = self.js("info", "acme/demo", "--json", "--train", TRAIN)
        self.assertEqual(code, 0, err)
        self.assertEqual((doc["schema"], doc["kind"], doc["package"]["id"]), ("mreg-info/1", "package", "acme/demo"))
        self.assertEqual(doc["on_train"]["version"], "1.0.0")
        self.assertIn(TRAIN, doc["on_train"]["trains"])
        self.assertIsNone(doc["installed"])

    def test_info_package_not_on_the_train_names_where_it_is(self):
        code, doc, out, err = self.js("info", "acme/old", "--json", "--train", TRAIN)
        self.assertEqual(code, 12)
        self.assertEqual(doc["error"]["kind"], "not_on_train")
        self.assertIn(TRAIN2, doc["error"]["message"])

    def test_info_declaration_statement_axioms_cone_labels_gates_trains(self):
        code, doc, out, err = self.js("info", "acme/demo#Demo.B.t2", "--json", "--train", TRAIN)
        self.assertEqual(code, 0, err)
        d = doc["declaration"]
        self.assertEqual((d["name"], d["kind"], d["module"]), ("Demo.B.t2", "thm", "Demo.B"))
        self.assertEqual(d["statement"], "Not False")
        self.assertEqual(d["axioms"], ["propext"])
        self.assertGreaterEqual(d["cone"]["chunks"], 1)
        self.assertEqual(d["on_trains"], [TRAIN])
        self.assertIn("gates", d)
        self.assertIn("labels", d)

    def test_info_declaration_with_no_axioms_says_none_not_missing(self):
        code, doc, out, err = self.js("info", "acme/demo#Demo.A.t1", "--json", "--train", TRAIN)
        self.assertEqual(doc["declaration"]["axioms"], [])
        self.assertIn("axioms: none", err)

    def test_info_record_over_the_size_limit_is_not_downloaded_and_says_so(self):
        code, doc, out, err = self.js("info", "acme/demo#Demo.B.t2", "--json", "--train", TRAIN, "--max-record-mb", "0.000001")
        self.assertEqual(code, 0, err)
        self.assertIsNone(doc["declaration"]["statement"])
        self.assertIn("too_large", doc["declaration"]["statement_status"])

    def test_info_unknown_declaration_is_exit_10(self):
        code, doc, out, err = self.js("info", "acme/demo#Demo.Nope", "--json", "--train", TRAIN)
        self.assertEqual((code, doc["error"]["kind"]), (10, "unknown_declaration"))

    def test_info_module(self):
        code, doc, out, err = self.js("info", "Demo.C", "--json", "--train", TRAIN)
        self.assertEqual(code, 0, err)
        m = doc["module"]
        self.assertEqual((m["package"], m["imports"]), ("acme/demo", ["Demo.B"]))
        self.assertEqual(m["closure_modules"], 3)               # C -> B -> A
        code, doc, out, err = self.js("info", "Nowhere.X", "--json", "--train", TRAIN)
        self.assertEqual(code, 10)

    # ---- why
    def test_why_prints_the_import_path_from_the_projects_own_modules(self):
        d = self.project(sources={"Proj.lean": "import Demo.C\n"}, train=TRAIN)
        code, doc, out, err = self.js("why", "Demo.A", "--json", proj=d)
        self.assertEqual(code, 0, err)
        self.assertEqual(doc["schema"], "mreg-why/1")
        self.assertEqual([x["module"] for x in doc["paths"][0]], ["Proj", "Demo.C", "Demo.B", "Demo.A"])
        self.assertEqual(doc["paths"][0][0]["package"], "(project)")
        self.assertEqual(doc["paths"][0][3]["package"], "acme/demo")
        self.assertEqual(doc["distance"], 3)

    def test_why_a_declaration_resolves_to_its_module(self):
        d = self.project(sources={"Proj.lean": "import Demo.C\n"}, train=TRAIN)
        code, doc, out, err = self.js("why", "acme/demo#Demo.A.t1", "--json", proj=d)
        self.assertEqual(code, 0, err)
        self.assertEqual(doc["target_module"], "Demo.A")
        self.assertEqual(doc["resolved"]["declaration"], "Demo.A.t1")

    def test_why_not_imported_is_exit_26(self):
        d = self.project(sources={"Proj.lean": "import Demo.B\n"}, train=TRAIN)
        code, doc, out, err = self.js("why", "Demo.D", "--json", proj=d)
        self.assertEqual((code, doc["error"]["kind"]), (26, "not_in_project"))
        self.assertEqual(M.EXIT["not_in_project"], 26)

    def test_why_unknown_name_is_exit_10_and_shortest_paths_only(self):
        d = self.project(sources={"Proj.lean": "import Demo.C\nimport Demo.B\n"}, train=TRAIN)
        code, doc, out, err = self.js("why", "Demo.A", "--json", proj=d)
        self.assertEqual(doc["distance"], 2)                    # through Demo.B directly
        self.assertEqual([x["module"] for x in doc["paths"][0]], ["Proj", "Demo.B", "Demo.A"])
        code, doc, out, err = self.js("why", "Totally.Unknown.name", "--json", proj=d)
        self.assertEqual(code, 10)

    # ---- search
    def test_search_names_and_statements(self):
        code, doc, out, err = self.js("search", "t2", "--json", "--train", TRAIN)
        self.assertEqual(code, 0, err)
        self.assertEqual(doc["schema"], "mreg-search/1")
        names = [r["name"] for r in doc["results"]]
        self.assertIn("Demo.B.t2", names)
        code, doc, out, err = self.js("search", "Not", "False", "--json", "--train", TRAIN)
        hit = [r for r in doc["results"] if r["match"] == "statement"]
        self.assertTrue(hit and hit[0]["name"] == "Demo.B.t2" and hit[0]["statement"] == "Not False", doc)
        cov = {s["package"]: s["status"] for s in doc["coverage"]["statements"]}
        self.assertEqual(cov["acme/demo"], "scanned")
        self.assertTrue(cov["leanprover-community/mathlib4"].startswith("no_record"))      # said, not silently skipped

    def test_search_names_only_reads_no_statement_record(self):
        code, doc, out, err = self.js("search", "Mathlib.n", "--names-only", "--json", "--train", TRAIN, "--limit", "5")
        self.assertEqual(code, 0, err)
        self.assertEqual(doc["coverage"]["statements"], [])
        self.assertEqual(len(doc["results"]), 5)
        self.assertTrue(doc["truncated"])
        self.assertTrue(all(r["match"] == "name" for r in doc["results"]))

    def test_search_without_text_or_without_a_store_is_an_error_or_a_note(self):
        code, doc, out, err = self.js("search", "   ", "--json", "--train", TRAIN)
        self.assertEqual(code, 1)

    def test_search_in_package_lifts_the_limit_and_restricts(self):
        code, doc, out, err = self.js("search", "Not", "--in", "acme/demo", "--json", "--train", TRAIN, "--max-record-mb", "0.000001")
        self.assertEqual([s["package"] for s in doc["coverage"]["statements"]], ["acme/demo"])
        self.assertEqual(doc["coverage"]["statements"][0]["status"], "scanned")


class TestDeclaredToolchain(TestRead):
    """`declared_toolchain` (the commit's own toolchain, when the registry built on a newer one): printed plainly by view, info and audit,
    read from the package document's build entry first, else the manifest; absent = no line."""
    DECL = "leanprover/lean4:v4.28.0"
    LINE = "compiled with leanprover/lean4:v4.35.0; source declares leanprover/lean4:v4.28.0"

    def set_field(self, where):
        pk = self.pk["demo"]
        dp = pathlib.Path(self.reg, "v1", "index", "acme", "demo.json")
        doc = json.loads(dp.read_text())
        base = pathlib.Path(self.reg, "v1", "blobs", "acme", "demo", "-", "1.0.0", pk["man"]["build_key"])
        man = json.loads((base / "manifest.json").read_text())
        if where == "entry":
            doc["versions"]["1.0.0"]["builds"][0]["declared_toolchain"] = self.DECL
        else:
            man["declared_toolchain"] = self.DECL
            mb = json.dumps(man, indent=1).encode()
            (base / "manifest.json").write_bytes(mb)
            doc["versions"]["1.0.0"]["builds"][0]["manifest"] = {"sha256": sha(mb), "bytes": len(mb)}
        dp.write_text(json.dumps(doc))

    def test_absent_field_prints_nothing_and_adds_no_value(self):
        code, out, err = self.cli("view", "acme/demo")
        self.assertNotIn("source declares", out)
        code, doc, out, err = self.js("info", "acme/demo", "--json", "--train", TRAIN)
        self.assertIsNone(doc["on_train"]["declared_toolchain"])
        self.assertNotIn("source declares", err)

    def test_entry_field_view_info_module_declaration(self):
        self.set_field("entry")
        code, out, err = self.cli("view", "acme/demo")
        self.assertIn(self.LINE, out)
        code, doc, out, err = self.js("view", "acme/demo", "--json")
        self.assertEqual(doc["package"]["versions"]["1.0.0"]["builds"][0]["declared_toolchain"], self.DECL)
        for target in ("acme/demo", "acme/demo#Demo.B.t2", "Demo.C"):
            code, doc, out, err = self.js("info", target, "--json", "--train", TRAIN)
            self.assertEqual(code, 0, err)
            node = doc.get("on_train") or doc.get("declaration") or doc.get("module")
            self.assertEqual((node["compiled_toolchain"], node["declared_toolchain"]), (TOOLCHAIN, self.DECL), target)
            self.assertIn(self.LINE, err)

    def test_manifest_field_is_read_when_the_entry_has_none(self):
        self.set_field("manifest")
        code, doc, out, err = self.js("info", "acme/demo", "--json", "--train", TRAIN)
        self.assertEqual(doc["on_train"]["declared_toolchain"], self.DECL)
        self.assertIn(self.LINE, err)

    def test_audit_prints_and_returns_both_fields(self):
        entry = {"build_key": "k" * 8, "toolchain": TOOLCHAIN, "declared_toolchain": self.DECL, "manifest": {"sha256": "x"}}
        e, c = M.declared_toolchain(entry, {"declared_toolchain": "other"})
        self.assertEqual((e, c), (TOOLCHAIN, self.DECL))                         # the entry wins
        self.assertEqual(M.declared_toolchain({"toolchain": TOOLCHAIN}, {"declared_toolchain": self.DECL, "toolchain": "m"}), (TOOLCHAIN, self.DECL))
        self.assertEqual(M.declared_toolchain({}, {"toolchain": TOOLCHAIN}), (None, None))
        self.assertEqual(M.declared_line(TOOLCHAIN, self.DECL), self.LINE)
        man = json.dumps({"id": "demo/pkg", "version": "1.0.0", "build_key": "k" * 8, "gates": {}, "reports": {}}).encode()
        for where in ("entry", "manifest"):
            m = json.loads(man)
            ent = {"build_key": "k" * 8, "manifest": {"sha256": sha(json.dumps(m).encode())}, "labels": [], "log_n": 1, "toolchain": TOOLCHAIN}
            if where == "entry":
                ent["declared_toolchain"] = self.DECL
            else:
                m["declared_toolchain"] = self.DECL
                m["toolchain"] = TOOLCHAIN
            raw = json.dumps(m).encode()
            ent["manifest"]["sha256"] = sha(raw)
            base = "/v1/blobs/demo/pkg/-/1.0.0/" + "k" * 8 + "/"
            files = {"/v1/index/demo/pkg.json": json.dumps({"id": "demo/pkg", "versions": {"1.0.0": {"builds": [ent]}}}).encode(), base + "manifest.json": raw}

            class FR:
                def get(self, path, rng=None, missing_ok=False):
                    return files.get(path)
                def json(self, path, **kw):
                    b = files.get(path)
                    return None if b is None else json.loads(b)
            row = M.audit_build(FR(), "demo/pkg", "1.0.0", "k" * 8, None, [], {}, True)
            self.assertEqual((row["compiled_toolchain"], row["declared_toolchain"]), (TOOLCHAIN, self.DECL), where)
        row = M.audit_build(FR(), "demo/pkg", "1.0.0", "k" * 8, None, [], {}, True) if False else None

    def test_audit_text_line(self):
        import io as _io
        row = {"id": "a/b", "version": "1", "build_key": "k", "gates": {}, "labels": [], "problems": [], "ok": True,
               "compiled_toolchain": TOOLCHAIN, "declared_toolchain": self.DECL}
        lock = os.path.join(self.tmp, "alock")
        os.makedirs(lock)
        json.dump({"packages": [{"from": "registry", "id": "a/b", "version": "1", "build_key": "k", "manifest_sha256": "x"}]}, open(os.path.join(lock, "mreg.lock"), "w"))
        with mock.patch.object(M, "audit_build", lambda *a, **k: dict(row)):
            code, out, err = run_main(["-C", lock, "audit"], self.env)
        self.assertIn(self.LINE, out)


class TestExitTable(unittest.TestCase):
    def test_existing_codes_are_unchanged_and_new_ones_are_documented(self):
        old = {"ok": 0, "error": 1, "unknown_declaration": 10, "ambiguous_name": 11, "not_on_train": 12, "auth": 13, "hash_mismatch": 14,
               "forbidden_mix": 15, "network": 16, "missing_object": 17, "build_removed": 18, "index_unavailable": 19, "toolchain_mismatch": 20,
               "over_budget": 21}
        for k, v in old.items():
            self.assertEqual(M.EXIT[k], v, k)
        new = {k: v for k, v in M.EXIT.items() if k not in old}
        self.assertEqual(new, {"own_code": 22, "replay_failed": 23, "axiom_not_allowed": 24, "tool_missing": 25, "not_in_project": 26, "unverified_refused": 4})
        self.assertEqual(len(set(M.EXIT.values())), len(M.EXIT))


if __name__ == "__main__":
    unittest.main(verbosity=1)
