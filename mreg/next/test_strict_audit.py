#!/usr/bin/env python3
"""S-CLIENT tests for mreg/next/mreg.py (stdlib only, no network, no Lean).

    python -I test_strict_audit.py

1. Any argument beginning `mreg_` (dotted or not, any length) is refused as a credential, without being echoed; the same inside a
   network registry address.
2. `mreg audit` strict by default (owner, 2026-11-12), `--lenient` the old behaviour with a warning, `--strict` explicit.
   Per-build lines name which rule failed; `imported` is shown with its meaning and never as `clean`.
"""
import contextlib, hashlib, importlib.util, io, json, os, shutil, sys, tempfile, unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("mreg_next_strict", os.path.join(HERE, "mreg.py"))
M = importlib.util.module_from_spec(spec)
spec.loader.exec_module(M)

FAKE_UNDOTTED = "mreg_" + "A1b2C3d4E5" * 4          # 45 chars, no dot
FAKE_SHORT = "mreg_abc"
FAKE_DOTTED = "mreg_abcdef123456." + "Zy9" * 14 + "Z"


def sha(b):
    return hashlib.sha256(b).hexdigest()


def run_main(argv, env=None):
    out, err, code = io.StringIO(), io.StringIO(), 0
    with mock.patch.dict(os.environ, env or {}, clear=False), contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        try:
            M.main(argv)
        except SystemExit as x:
            code = x.code if isinstance(x.code, int) else (0 if x.code is None else x.code)
            if isinstance(x.code, str):
                err.write(x.code)
    return code, out.getvalue(), err.getvalue()


class Credentials(unittest.TestCase):
    def refused(self, argv, secret, env=None):
        code, out, err = run_main(argv, env)
        self.assertNotEqual(code, 0, argv)
        self.assertIn("never accepted on the command line", out + err)
        self.assertNotIn(secret, out + err)
        self.assertNotIn(secret[:12], out + err)

    def test_undotted_long_key_as_argument(self):
        for cmd in (["train", FAKE_UNDOTTED], ["view", FAKE_UNDOTTED], ["resolve", FAKE_UNDOTTED]):
            self.refused(cmd, FAKE_UNDOTTED)

    def test_any_length_beginning_mreg_underscore(self):
        for x in (FAKE_SHORT, "mreg_", "mreg_x", FAKE_DOTTED):
            self.refused(["view", x], x)

    def test_after_equals_and_inside_a_word(self):
        self.refused(["train", "--train=" + FAKE_UNDOTTED], FAKE_UNDOTTED)
        self.refused(["train", "x" + FAKE_UNDOTTED], FAKE_UNDOTTED)

    def test_ordinary_arguments_are_not_refused(self):
        for x in ("acme/demo", "mregistry", "Mreg_x", "my_mreg_x"):
            self.assertFalse(M._key_like_arg(x), x)

    def test_registry_address_with_key_prefix(self):
        for base in ("https://example.org/" + FAKE_SHORT, "https://example.org/a/mreg_x/b", "s3://bucket/mreg_x",
                     "s3://bucket/" + FAKE_UNDOTTED, "https://example.org/" + FAKE_UNDOTTED):
            why = M.registry_url_problem(base)
            self.assertEqual(why, "it contains a key", base)
        for base in ("https://mathregistry.com", "s3://example-registry-test", "file:///C:/tmp/mreg_scratch/reg"):
            self.assertIsNone(M.registry_url_problem(base), base)

    def test_registry_env_refused_without_echo(self):
        code, out, err = run_main(["train"], {"MREG_REGISTRY": "https://example.org/" + FAKE_SHORT})
        self.assertNotEqual(code, 0)
        self.assertIn("MREG_REGISTRY is refused", out + err)
        self.assertNotIn(FAKE_SHORT, out + err)


# ---------------------------------------------------------------- audit

class FakeReg:
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


def build(gates, labels, signed=True):
    pid, ver, key = "demo/pkg", "1.0.0", "k" * 8
    verify = json.dumps({"gates": {g: {"status": s} for g, s in gates.items()}}).encode()
    man = json.dumps({"id": pid, "version": ver, "build_key": key, "gates": {g: {"status": s} for g, s in gates.items()},
                      "reports": {"reports/verify.json": sha(verify)}}).encode()
    msha, sigraw = sha(man), b'{"synthetic": true}'
    base = f"/v1/blobs/{pid}/-/{ver}/{key}/"
    doc = {"id": pid, "dist_tags": {"latest": ver},
           "versions": {ver: {"builds": [{"build_key": key, "manifest": {"sha256": msha}, "labels": list(labels), "log_n": 1,
                                          "signed": signed}]}}}
    entry = {"id": pid, "version": ver, "build_key": key, "manifest_sha256": msha, "labels": list(labels), "type": "promote"}
    if signed:
        entry["sig_sha256"] = sha(sigraw)
    files = {f"/v1/index/{pid}.json": json.dumps(doc).encode(), base + "manifest.json": man,
             base + "reports/verify.json": verify, "/v1/log/1.json": json.dumps(entry).encode()}
    if signed:
        files[base + "manifest.json.sig"] = sigraw
    return FakeReg(files), (pid, ver, key, msha)


ALL_PASS = {f"G{i}": "pass" for i in range(1, 11)}
IMPORTED_GATES = dict(ALL_PASS, G1="not run")


def with_gates(**kw):
    g = dict(ALL_PASS)
    g.update(kw)
    return g


class Strict(unittest.TestCase):
    def audit(self, gates, labels, signed=True, strict=True, require=()):
        reg, (pid, ver, key, msha) = build(gates, labels, signed)
        sg = {"labels": list(labels), "promoted_at": "2026-11-12T00:00:00Z"}
        with mock.patch.object(M, "check_signature", lambda *a: (sg, [])), mock.patch.object(M, "chain_problems", lambda *a: []):
            return M.audit_build(reg, pid, ver, key, msha, list(require), {}, strict)

    def strict_lines(self, row):
        return [p for p in row["problems"] if p.startswith("strict: ")]

    def test_clean_all_pass_ok(self):
        row = self.audit(ALL_PASS, ["clean"])
        self.assertTrue(row["ok"], row["problems"])
        self.assertEqual(row["mode"], "strict")

    def test_imported_ok_with_g1_not_run(self):
        row = self.audit(IMPORTED_GATES, ["imported"])
        self.assertTrue(row["ok"], row["problems"])

    def test_imported_with_g1_pass_is_inconsistent(self):
        row = self.audit(ALL_PASS, ["imported"])
        self.assertFalse(row["ok"])
        self.assertTrue(any("G1" in p and "imported" in p for p in self.strict_lines(row)))

    def test_g7_not_run_fails_with_its_own_line(self):
        row = self.audit(with_gates(G7="not run"), ["clean"])
        self.assertFalse(row["ok"])
        self.assertTrue(any("G7" in p and "not run" in p for p in self.strict_lines(row)))

    def test_flag_and_not_run_and_fail_and_missing_each_named(self):
        for st, word in (("flag", "flag"), ("not run", "not run"), ("fail", "fail")):
            row = self.audit(with_gates(G4=st), ["clean"])
            self.assertFalse(row["ok"], st)
            self.assertTrue(any("gate G4 is " + word in p for p in self.strict_lines(row)), (st, row["problems"]))
        g = dict(ALL_PASS)
        del g["G5"]
        row = self.audit(g, ["clean"])
        self.assertTrue(any("gate G5 is missing" in p for p in self.strict_lines(row)))

    def test_g9_not_run_ok_for_clean_label_rules_but_not_for_imported(self):
        # clean needs G1-G8 and G10; a build labelled clean with G9 not run does not occur (promotion would say partial)
        row = self.audit(with_gates(G9="not run"), ["clean"])
        self.assertTrue(row["ok"], row["problems"])
        row = self.audit(dict(IMPORTED_GATES, G9="not run"), ["imported"])
        self.assertFalse(row["ok"])

    def test_labels_partial_flagged_none_and_both_fail(self):
        for labels in (["partial"], ["flagged"], [], ["clean", "imported"]):
            row = self.audit(ALL_PASS, labels)
            self.assertFalse(row["ok"], labels)
            self.assertTrue(self.strict_lines(row), labels)

    def test_unsigned_plain_message(self):
        reg, (pid, ver, key, msha) = build(ALL_PASS, [], signed=False)
        row = M.audit_build(reg, pid, ver, key, msha, [], {}, True)
        self.assertFalse(row["ok"])
        self.assertEqual(row["signature"], "missing")
        self.assertTrue(any(p.startswith("strict: unsigned: no registry gate record") for p in row["problems"]), row["problems"])
        # the gate statuses are not judged one by one for an unsigned build
        self.assertFalse(any("gate G" in p for p in self.strict_lines(row)))

    def test_lenient_keeps_the_old_result(self):
        row = self.audit(with_gates(G7="not run", G8="flag"), ["flagged"], strict=False)
        self.assertTrue(row["ok"], row["problems"])
        self.assertEqual(row["mode"], "lenient")

    def test_require_still_works_in_strict(self):
        row = self.audit(ALL_PASS, ["clean"], require=["G9"])
        self.assertTrue(row["ok"])


class StrictCommand(unittest.TestCase):
    def go(self, gates, labels, flags=(), signed=True):
        reg, (pid, ver, key, msha) = build(gates, labels, signed)
        sg = {"labels": list(labels), "promoted_at": "2026-11-12T00:00:00Z"}
        d = tempfile.mkdtemp(prefix="mreg-audit-")
        self.addCleanup(shutil.rmtree, d, True)
        with mock.patch.object(M, "Registry", lambda token=None: reg), \
                mock.patch.object(M, "check_signature", lambda *a: (sg, [])), mock.patch.object(M, "chain_problems", lambda *a: []):
            return run_main(["-C", d, "audit", pid] + list(flags))

    def test_default_is_strict(self):
        self.assertTrue(M.AUDIT_STRICT_DEFAULT)
        code, out, err = self.go(with_gates(G7="not run"), ["clean"])
        self.assertEqual(code, 1, out)
        self.assertIn("FAIL", out)
        self.assertIn("strict: gate G7", out)
        self.assertIn("audit (strict): 0 of 1", out)
        self.assertNotIn("--lenient is on", err)

    def test_clean_exit_zero(self):
        code, out, err = self.go(ALL_PASS, ["clean"])
        self.assertEqual(code, 0, out)
        self.assertIn("OK", out)
        self.assertNotIn("labels=imported", out)

    def test_imported_shown_with_meaning_and_not_as_clean(self):
        code, out, err = self.go(IMPORTED_GATES, ["imported"])
        self.assertEqual(code, 0, out)
        self.assertIn("labels=imported", out)
        self.assertIn("files compiled elsewhere, gated here", out)
        self.assertIn("not the label clean", out)
        self.assertNotIn("labels=clean", out)

    def test_lenient_flag_warns_and_passes(self):
        code, out, err = self.go(with_gates(G7="not run", G8="flag"), ["flagged"], ["--lenient"])
        self.assertEqual(code, 0, out)
        self.assertIn("--lenient is on", err)
        self.assertIn("1 of 1 builds with consistent signature", out)

    def test_strict_and_lenient_together_refused(self):
        code, out, err = self.go(ALL_PASS, ["clean"], ["--strict", "--lenient"])
        self.assertNotEqual(code, 0)
        self.assertIn("exclude each other", out + err)

    def test_json_carries_labels_and_gates_as_they_are(self):
        code, out, err = self.go(IMPORTED_GATES, ["imported"], ["--json"])
        rows = json.loads(out)
        self.assertEqual(rows[0]["labels"], ["imported"])
        self.assertEqual(rows[0]["gates"]["G1"], "not run")
        self.assertEqual(rows[0]["gates"]["G7"], "pass")
        self.assertEqual(code, 0)

    def test_unsigned_exit_nonzero_plain_line(self):
        reg, (pid, ver, key, msha) = build(ALL_PASS, [], signed=False)
        d = tempfile.mkdtemp(prefix="mreg-audit-")
        self.addCleanup(shutil.rmtree, d, True)
        with mock.patch.object(M, "Registry", lambda token=None: reg), mock.patch.object(M, "chain_problems", lambda *a: []):
            code, out, err = run_main(["-C", d, "audit", pid])
        self.assertEqual(code, 1)
        self.assertIn("unsigned: no registry gate record", out)

    def test_view_shows_labels_and_unsigned(self):
        reg, (pid, ver, key, msha) = build(IMPORTED_GATES, ["imported"])
        doc = reg.json(f"/v1/index/{pid}.json")
        doc.update({"lake_name": "pkg", "license": {"spdx": "Apache-2.0"}, "ownership": "x"})
        e = doc["versions"][ver]
        e.update({"commit": "c" * 40, "committed_at": "t", "version_from": "tag"})
        e["builds"][0].update({"toolchain": "leanprover/lean4:v4.35.0", "modules": 3, "bytes_compressed": 1000, "trains": [],
                               "usable_on": [{"platform": "x"}], "gates": IMPORTED_GATES})
        doc["dist_tags"] = {"latest": ver}
        reg.files[f"/v1/index/{pid}.json"] = json.dumps(doc).encode()
        d = tempfile.mkdtemp(prefix="mreg-view-")
        self.addCleanup(shutil.rmtree, d, True)
        with mock.patch.object(M, "Registry", lambda token=None: reg):
            code, out, err = run_main(["-C", d, "view", pid])
        self.assertEqual(code, 0, err)
        self.assertIn("labels=imported", out)
        self.assertIn("signed", out)
        self.assertIn("not the label clean", out)


if __name__ == "__main__":
    unittest.main(verbosity=1)
