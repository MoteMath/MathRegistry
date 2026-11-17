"""Receipt-aware install, restore, verify and rejection paths with a local signed registry."""
import base64
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[1]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


mreg = load("tested_mreg", ROOT / "mreg/mreg.py")
fixture = load("receipt_fixture", ROOT / "mreg/next/test_admission.py")


class VerifiedSlices(unittest.TestCase):
    def setUp(self):
        tmp = self.enterContext(tempfile.TemporaryDirectory())
        self.root = Path(tmp)
        registry = self.root / "registry"
        self.mirror = fixture.Mirror(registry)
        self.project = self.root / "project"
        self.project.mkdir()
        (self.project / "lean-toolchain").write_text(fixture.TOOLCHAIN)
        self.enterContext(mock.patch.dict(os.environ, {"MREG_REGISTRY": registry.as_uri(),
                          "MREG_STORE": str(self.root / "cache"), "MREG_KEYS": str(self.root / "pins")}))
        self.key_path = self.root / "test.pem"
        subprocess.run(["openssl", "ecparam", "-name", "prime256v1", "-genkey", "-noout",
                        "-out", self.key_path], check=True)
        pub = ["openssl", "pkey", "-in", self.key_path, "-pubout"]
        pem = subprocess.check_output(pub).decode("ascii")
        self.key_id = mreg.sha256(subprocess.check_output(pub + ["-outform", "DER"]))[:16]
        (registry / "v1/index/keys.json").write_text(json.dumps({"keys": [
            {"key_id": self.key_id, "public_key_pem": pem}]}))
        self.entry = fixture.MATHLIB + "#Mathlib.n60_0"
        self.pointer = Path(self.mirror.p("current.json"))
        self.path = Path(self.mirror.p("b1", "checking", "chunk-receipt.json"))
        self.lock = self.project / mreg.CHUNK_LOCK
        self.receipt = {"schema": "mreg-chunk-receipt/1", "capability": "kernel-declarations",
                        "train": fixture.TRAIN, "toolchain": fixture.TOOLCHAIN, "build": "b1", "variant": "checking",
                        "gates": {f"C{i}": "pass" for i in range(7)}, "index_sha256": self.mirror.index_hashes(),
                        "manifest_sha256": self.mirror.index_hashes()["manifest.tsv.gz"], "sources": [],
                        "toolchain_commit": "f" * 40, "files_sha256": "a" * 64, "tools_sha256": {"checker": "c" * 64},
                        "counts": {"chunks": 64, "chunks_read": 64, "constants": 150, "excluded": 0, "source_modules": 3,
                                   "uncovered": 0, "problems": 0},
                        "kernels": {"modules": 64, "declarations": 150, "status": "pass", "second_kernel_checked": 200},
                        "exclusions": {"count": 0, "sha256": "e" * 64}}
        for pid, name, modules in [(fixture.MATHLIB, "mathlib", ["Mathlib.Algebra", "Mathlib.Algebra.More"]),
                                   (fixture.BATTERIES, "batteries", ["Batteries.Data"])]:
            license_text = f"License for {pid}\r\n".encode()
            notice_text = f"Copyright of {pid}\n".encode()
            man = {"toolchain": fixture.TOOLCHAIN, "aux_files": {"shards/index.jsonl": {"sha256": "a" * 64}},
                   "license_sha256": mreg.sha256(license_text), "notice_sha256": mreg.sha256(notice_text)}
            raw = json.dumps(man).encode()
            path = registry / "v1/blobs" / pid / "-/v1/b/manifest.json"
            path.parent.mkdir(parents=True)
            path.write_bytes(raw)
            (path.parent / "LICENSE").write_bytes(license_text)
            (path.parent / "NOTICE").write_bytes(notice_text)
            self.receipt["sources"].append({"id": pid, "version": "v1", "build_key": "b",
                                            "modules": modules, "lake_name": name,
                                            "index_sha256": "a" * 64, "manifest_sha256": mreg.sha256(raw)})
        # Source auditing has its own signed-build integration suite. Isolate that
        # input here and exercise the actual derived-receipt signature and key pin.
        self.audit = self.enterContext(mock.patch.object(mreg, "audit_build", return_value={"ok": True, "views": "pass"}))
        self.publish()

    def publish(self):
        raw = json.dumps(self.receipt).encode()
        self.path.write_bytes(raw)
        digest = mreg.sha256(raw)
        pid, version, build = "mreg/declaration-slices", fixture.TRAIN, "b1-checking"
        labels, now = ["verified-declarations"], "2026-11-16T12:00:00Z"
        signature = subprocess.check_output(["openssl", "dgst", "-sha256", "-sign", self.key_path],
                                            input=mreg.sig_message(pid, version, build, digest, labels, now))
        doc = {"schema": "mreg-sig/1", "alg": "ECDSA_P256_SHA256", "key_id": self.key_id,
               "id": pid, "version": version, "build_key": build, "manifest_sha256": digest,
               "labels": labels, "promoted_at": now, "signature": base64.b64encode(signature).decode()}
        Path(str(self.path) + ".sig").write_text(json.dumps(doc))
        ptr = json.loads(self.pointer.read_bytes())
        ptr["receipt_sha256"] = {"checking": digest}
        self.pointer.write_text(json.dumps(ptr))

    def command(self, *args, expected=0):
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            try:
                mreg.main(["-C", str(self.project), *args, "--json"])
                code = 0
            except SystemExit as e:
                code = e.code
        self.assertEqual(code, expected, out.getvalue() + err.getvalue())
        return json.loads(out.getvalue())

    def test_install_preserves_existing_and_edited_project_source(self):
        path = self.project / "MregChunks.lean"
        source = b"theorem keep_this_source : True := True.intro\n"
        path.write_bytes(source)
        self.install(expected=15)
        self.assertEqual(path.read_bytes(), source)
        self.assertFalse(self.lock.exists())
        entry = self.project / "Generated.lean"
        self.install(0, "--entry", entry.name)
        entry.write_bytes(source)
        lock_before = self.lock.read_bytes()
        self.install(expected=15)
        self.assertEqual(entry.read_bytes(), source)
        self.assertEqual(self.lock.read_bytes(), lock_before)

    def test_install_reuses_locked_paths_and_no_entry_choice(self):
        self.install(0, "--chunk-dir", "build/proofs", "--entry", "Generated.lean")
        old = (self.project / "Generated.lean").read_bytes()
        self.command("install", fixture.MATHLIB + "#Mathlib.n24_0")
        lock = json.loads(self.lock.read_bytes())
        self.assertEqual((lock["chunk_dir"], lock["entry"]), ("build/proofs", "Generated.lean"))
        self.assertNotEqual((self.project / "Generated.lean").read_bytes(), old)
        self.assertFalse((self.project / "MregChunks.lean").exists())
        self.install(0, "--no-entry")
        self.install()
        self.assertIsNone(json.loads(self.lock.read_bytes())["entry"])

    def test_check_revalidates_signed_evidence_and_rejects_changed_receipt(self):
        self.install()
        # Isolate the integrity step from tools that require a Lean installation.
        with mock.patch.object(mreg, "lc_steps_wanted", return_value=[1]):
            result = self.command("check")
            integrity = result["steps"][0]
            self.assertEqual(integrity["verdict"], "pass")
            self.assertTrue(integrity["details"]["chunks"]["admission"]["proof_checked_under_policy"])
            self.assertFalse(any("unverified experimental" in text for text in result["incomplete_reasons"]))
            self.path.write_bytes(self.path.read_bytes() + b" ")
            self.assertEqual(self.command("check", expected=14)["steps"][0]["verdict"], "fail")

    def install(self, expected=0, *extra):
        return self.command("install", self.entry, "--train", fixture.TRAIN, *extra, expected=expected)

    def test_signed_install_ci_verify_and_omitted_dependency(self):
        self.assertTrue(self.install()["admission"]["proof_checked_under_policy"])
        self.assertTrue(self.command("ci", "--chunks-only")["admission"]["proof_checked_under_policy"])
        self.assertTrue(self.command("verify")["admission"]["proof_checked_under_policy"])
        self.assertTrue(self.command("audit", "--strict")[0]["admission"]["proof_checked_under_policy"])
        lock = json.loads(self.lock.read_bytes())
        self.assertGreater(len(lock["chunks"]), 1)
        del lock["chunks"][0]
        self.lock.write_text(json.dumps(lock))
        self.command("ci", "--chunks-only", expected=14)
        self.command("verify", expected=14)

    def test_changed_source_index_pin(self):
        self.receipt["sources"][0]["index_sha256"] = "1" * 64
        self.publish()
        self.install(14)
        self.assertFalse(self.lock.exists())

    def test_licenses_are_source_pinned(self):
        self.install()
        lock = json.loads(self.lock.read_bytes())
        body = (self.project / lock["chunk_dir"] / "THIRD_PARTY_LICENSES.txt").read_bytes()
        for pid in (fixture.MATHLIB, fixture.BATTERIES):
            self.assertIn(f"License for {pid}\r\n".encode(), body)
            self.assertIn(f"Copyright of {pid}\n".encode(), body)
        notice = self.root / "registry/v1/blobs" / fixture.BATTERIES / "-/v1/b/NOTICE"
        notice.write_bytes(b"different attribution")
        self.command("ci", "--chunks-only", expected=14)
        notice.unlink()
        self.command("verify", expected=14)

    def test_revoked_source_and_forged_signature(self):
        self.audit.return_value = {"ok": False}
        self.install(4)
        self.audit.return_value = {"ok": True, "views": "pass"}
        sig = Path(str(self.path) + ".sig")
        obj = json.loads(sig.read_bytes())
        obj["signature"] = "AA=="
        sig.write_text(json.dumps(obj))
        self.install(4, "--allow-unverified")
        self.assertFalse(self.lock.exists())

    def test_supplemental_views_can_cover_historical_missing_evidence(self):
        self.audit.return_value = {"ok": True, "views": None}
        self.install(4)
        for src in self.receipt["sources"]:
            src["supplemental_views"] = {"schema": "mreg-views/1", "status": "pass", "problems": 0,
                "modules": len(src["modules"]), "modules_checked": len(src["modules"]), "lean": "4.35.0",
                "index_sha256": src["index_sha256"], "report_sha256": "a" * 64, "sha256": "a" * 64,
                "checker_sha256": "c" * 64, "files_sha256": "f" * 64}
        self.publish()
        self.install()
        self.audit.return_value = {"ok": True, "views": "fail"}
        self.command("ci", "--chunks-only", expected=4)

    def test_incomplete_replay_and_conflicting_source_versions(self):
        self.receipt["gates"]["C6"] = "not run"
        self.publish()
        self.install(4)
        self.receipt["gates"]["C6"] = "pass"
        self.receipt["sources"].append(dict(self.receipt["sources"][0], version="v2"))
        self.publish()
        self.install(4)

    def test_tampered_cached_index(self):
        self.install()
        cache = self.root / "cache/index" / fixture.TRAIN / "b1"
        (cache / "off.bin").write_bytes(b"corrupt derivative")
        self.command("verify")
        (cache / "chunk_edges.tsv.gz").write_bytes(b"corrupt signed input")
        self.command("ci", "--chunks-only", expected=14)

    def test_search_path_shadowing_and_sidecars_are_preserved_and_rejected(self):
        self.install()
        lock = json.loads(self.lock.read_bytes())
        lib = self.project / lock["chunk_dir"]
        for name in ("Init.olean", "plugin.so", mreg.chunk_rel(lock["chunks"][0]["id"]) + ".private"):
            with self.subTest(name=name):
                p = lib / name
                p.write_bytes(b"foreign Lean artifact")
                self.command("ci", "--chunks-only", expected=15)
                self.command("verify", expected=15)
                self.assertEqual(p.read_bytes(), b"foreign Lean artifact")
                p.unlink()

    def test_ci_recreates_missing_entry_and_rejects_modified_imports(self):
        self.install()
        entry = self.project / "MregChunks.lean"
        canonical = entry.read_bytes()
        entry.unlink()
        self.command("verify", expected=14)
        self.command("ci", "--chunks-only")
        self.assertEqual(entry.read_bytes(), canonical)
        entry.write_bytes(canonical + b"import Unexpected\n")
        self.command("ci", "--chunks-only", expected=14)
        self.command("verify", expected=14)


if __name__ == "__main__":
    unittest.main()
