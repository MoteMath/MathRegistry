#!/usr/bin/env python3
"""Tests of the declaration-level import (`mreg add owner/pkg#Decl.name`, resolve, install, ci, verify, env) in mreg/next/mreg.py.

    python test_named_import.py            # all
    MREG_TEST_SKIP_REAL=1 python test_named_import.py    # without the real 4.34.1 tables (they cost about 90 s)

Stdlib only. No network (a registry is a file:/// directory built here, or a server on 127.0.0.1), no AWS, no Lean: a chunk is a
small dummy payload, loading in Lean is NOT tested. Every test uses a temporary home, store and project.
The real tables (read only): mathlib-graph-20261110/slice/assign/{assignment,chunk_edges}.tsv.gz.
"""
import contextlib, gzip, hashlib, http.server, importlib.util, io, json, os, random, shutil, socket, subprocess, sys, tempfile, threading, time
import unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("mreg_next_ni", os.path.join(HERE, "mreg.py"))
M = importlib.util.module_from_spec(spec)
spec.loader.exec_module(M)
try:
    from compression import zstd as _zstd
except ImportError:      # pragma: no cover
    if shutil.which("zstd"):
        class _ZstdCLI:
            @staticmethod
            def compress(data, level=3):
                return subprocess.run(["zstd", f"-{level}", "-q", "-c"], input=data, capture_output=True, check=True).stdout

            @staticmethod
            def decompress(data):
                return subprocess.run(["zstd", "-d", "-q", "-c"], input=data, capture_output=True, check=True).stdout

        _zstd = _ZstdCLI()
    else:
        _zstd = None
REAL = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(HERE))), "mathlib-graph-20261110", "slice", "assign")
EVID = os.path.join(os.path.dirname(os.path.dirname(HERE)), "evidence", "mreg-next")

TRAIN = "lean-4.35.0"
MATHLIB, BATTERIES = "leanprover-community/mathlib4", "leanprover-community/batteries"


def sha(b):
    return hashlib.sha256(b).hexdigest()


# ---------------------------------------------------------------- a synthetic registry in the FINAL layout

TC_ROOTS = ("Init", "Std", "Lean", "Lake")      # the test's own rule for what the toolchain provides
TOOLCHAIN = "leanprover/lean4:v4.35.0"


class Mirror:
    """A decl store with `n` chunks and a random DAG; chunks 0-5 belong to the toolchain (Std, Lean) and are NOT in the store, the
    assignment (in_toolchain=1, empty chunk) or the edge table; declarations of three packages and Init; the final columns and a
    pointer that pins all three index files."""

    def __init__(self, root, build="b1", seed=7, n=70, edge_style="sorted", publish=True, train=TRAIN, payload_tag=b"",
                 toolchain=TOOLCHAIN):
        self.root, self.build, self.train, self.n, self.toolchain = root, build, train, n, toolchain
        rnd = random.Random(seed)
        self.rnd = rnd
        self.ids = [hashlib.sha256(f"chunk{i}".encode()).hexdigest()[:32] for i in range(n)]
        self.mod = {}
        for i in range(n):
            self.mod[i] = ("Std.Core" if i < 3 else "Lean.Meta" if i < 6 else "Batteries.Data" if i < 24 else "Mathlib.Algebra")
        self.deps = {i: set() for i in range(n)}
        for i in range(1, n):
            for j in range(i):
                ok = (self.mod[i].startswith("Mathlib") or (self.mod[i].startswith("Batteries") and not self.mod[j].startswith("Mathlib"))
                      or (self.mod[i].split(".")[0] in ("Std", "Lean") and self.mod[j].split(".")[0] in ("Std", "Lean")))
                if ok and rnd.random() < 0.07:
                    self.deps[i].add(j)
            if i >= 6 and not self.deps[i]:
                self.deps[i].add(i - 1 if self.mod[i - 1].split(".")[0] != "Mathlib" or self.mod[i].startswith("Mathlib") else 3)
        self.decls = []      # (name, exact, module, kind, chunk index or None for a toolchain declaration of Init)
        for i in range(n):
            for k in range(1 + (i % 3)):
                nm = f"{self.mod[i].split('.')[0]}.n{i}_{k}"
                self.decls.append((nm, nm, self.mod[i], "thm" if k else "def", i))
        self.decls += [("Init.Nat.add", "Init.Nat.add", "Init.Core", "def", None), ("Init.foo", "Init.foo", "Init.Prelude", "thm", None),
                       ("Mathlib.weird.«x y»", "Mathlib.weird.x%20y", "Mathlib.Algebra", "thm", 40),
                       ("Mathlib.amb.x", "Mathlib.amb.x", "Mathlib.Algebra", "thm", 41),
                       ("Mathlib.amb.x", "Mathlib.amb%2Ex", "Mathlib.Algebra", "thm", 42),
                       ("Batteries.Data.dup", "Batteries.Data.dup", "Batteries.Data", "thm", 10),
                       ("Foo.bar.Batteries_in_mathlib", "Foo.bar.Batteries_in_mathlib", "Mathlib.Algebra", "thm", 43),
                       # a later copy of a name an earlier module defines points at the first owner's chunk
                       ("Mathlib.dupcopy.x", "Mathlib.dupcopy.x", "Mathlib.Algebra", "thm", 44),
                       ("Mathlib.dupcopy.x", "Mathlib.dupcopy.x", "Mathlib.Algebra.More", "thm", 44),
                       ("Batteries.Data.later", "Batteries.Data.later", "Batteries.Data", "thm", 12),
                       ("Batteries.Data.later", "Batteries.Data.later", "Mathlib.Algebra", "thm", 12),
                       # the same exact name with two different chunks is NOT a duplicate: ambiguous
                       ("Mathlib.amb2.y", "Mathlib.amb2.y", "Mathlib.Algebra", "thm", 45),
                       ("Mathlib.amb2.y", "Mathlib.amb2.y", "Mathlib.Algebra.More", "thm", 46)]
        self.edge_style = edge_style
        self.tag = payload_tag
        self.raw, self.stored = {}, {}
        for v in ("checking", "full"):
            for i, cid in enumerate(self.ids):
                if self.is_tc(i):
                    continue
                raw = b"MREGTEST" + v.encode() + payload_tag + bytes.fromhex(cid) + bytes(rnd.randrange(256) for _ in range(40 + 7 * i))
                self.raw[(v, cid)] = raw
                self.stored[(v, cid)] = _zstd.compress(raw, 3)
        self.write_all()
        if publish:
            self.publish_pointer()

    def is_tc(self, i):
        return self.mod[i].split(".")[0] in TC_ROOTS

    # ---- paths
    def p(self, *parts):
        return os.path.join(self.root, "x", "decl", self.train, *parts)

    def idx(self, name):
        return self.p(self.build, "index", name)

    def obj(self, variant, cid):
        return self.p(self.build, variant, f"X{cid[:2]}", f"C{cid}.olean.zst")

    def wr(self, path, data):
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "wb") as f:
            f.write(data)

    def write_all(self):
        hdr = ["name", "exact_name", "module", "kind", "in_toolchain", "chunk"]
        lines = ["\t".join(hdr)]
        for nm, ex, mo, kd, ci in self.decls:
            tc = ci is None or self.is_tc(ci)
            lines.append("\t".join([nm, ex, mo, kd, "1" if tc else "0", "" if tc else self.ids[ci]]))
        self.assignment = gzip.compress(("\n".join(lines) + "\n").encode())
        self.wr(self.idx("assignment.tsv.gz"), self.assignment)
        edges = [(self.ids[i], self.ids[j]) for i in range(self.n) if not self.is_tc(i) for j in sorted(self.deps[i]) if not self.is_tc(j)]
        if self.edge_style == "sorted":
            edges.sort()
        else:
            self.rnd.shuffle(edges)
        el = ["chunk\timports_chunk"] + [f"{a}\t{b}" for a, b in edges]
        self.edges = gzip.compress(("\n".join(el) + "\n").encode())
        self.wr(self.idx("chunk_edges.tsv.gz"), self.edges)
        rows = [["variant", "key", "id", "sha256_raw", "bytes_raw", "sha256_stored", "bytes_stored", "n_decls"]]
        for (v, cid), raw in sorted(self.raw.items()):
            st = self.stored[(v, cid)]
            self.wr(self.obj(v, cid), st)
            rows.append([v, f"x/decl/{self.train}/{self.build}/{v}/X{cid[:2]}/C{cid}.olean.zst", cid, sha(raw), str(len(raw)), sha(st),
                         str(len(st)), "1"])
        self.manifest = gzip.compress(("\n".join("\t".join(r) for r in rows) + "\n").encode())
        self.wr(self.idx("manifest.tsv.gz"), self.manifest)
        train_doc = {"train": self.train, "toolchain": self.toolchain, "state": "live", "mathlib": {"rev": "a" * 40},
                     "packages": {MATHLIB: {"lake_name": "mathlib", "module_roots": ["Mathlib"], "version": "1", "commit": "c" * 40,
                                            "git": "https://example.invalid/m", "modules": 1},
                                  BATTERIES: {"lake_name": "batteries", "module_roots": ["Batteries"], "version": "1",
                                              "commit": "d" * 40, "git": "https://example.invalid/b", "modules": 1}}}
        self.wr(os.path.join(self.root, "v1", "index", "trains", f"{self.train}.json"), json.dumps(train_doc).encode())
        self.wr(os.path.join(self.root, "v1", "index", "trains.json"), json.dumps({"trains": [{"train": self.train}]}).encode())

    def index_hashes(self):
        return {"assignment.tsv.gz": sha(self.assignment), "chunk_edges.tsv.gz": sha(self.edges), "manifest.tsv.gz": sha(self.manifest)}

    def publish_pointer(self, build=None, manifest_sha=None, index=None, drop=()):
        build = build or self.build
        ptr = {"schema": "mreg-decl-store/1", "train": self.train, "build": build, "variants": ["checking", "full"],
               "manifest_sha256": manifest_sha or sha(self.manifest),
               "index_sha256": dict(self.index_hashes(), **(index or {})), "published_at": "2026-11-10T20:00:00Z"}
        for k in drop:
            ptr.pop(k, None)
        self.wr(self.p("current.json"), json.dumps(ptr).encode())

    # ---- the independent model
    def cone(self, ci):
        """Sorted chunk ids of the closure of chunk ci over the edges between non-toolchain chunks."""
        seen, stack = set(), [ci]
        while stack:
            c = stack.pop()
            if c in seen or self.is_tc(c):
                continue
            seen.add(c)
            stack.extend(self.deps[c])
        return sorted(self.ids[c] for c in seen)

    def corrupt_stored(self, variant, cid):
        path = self.obj(variant, cid)
        b = bytearray(open(path, "rb").read())
        b[len(b) // 2] ^= 1
        self.wr(path, bytes(b))


class Base(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="mreg-ni-")
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.home = os.path.join(self.tmp, "home")
        os.makedirs(self.home)
        self.store = os.path.join(self.tmp, "store")
        self.reg = os.path.join(self.tmp, "reg")
        self.proj = os.path.join(self.tmp, "proj")
        self.new_proj(self.proj)
        self.env = {"HOME": self.home, "USERPROFILE": self.home, "MREG_STORE": self.store, "MREG_BACKOFF": "0", "MREG_RETRIES": "1",
                    "MREG_REGISTRY": "file:///" + self.reg.replace("\\", "/").lstrip("/")}
        self.env.pop("MREG_TOKEN", None)

    def new_proj(self, path, toolchain=TOOLCHAIN):
        os.makedirs(path, exist_ok=True)
        if toolchain is not None:
            open(os.path.join(path, "lean-toolchain"), "w").write(toolchain + "\n")

    def proj_files(self, proj=None):
        """What is in the project directory besides the lean-toolchain file the tests put there."""
        return sorted(x for x in os.listdir(proj or self.proj) if x != "lean-toolchain")

    def mirror(self, **kw):
        self.m = Mirror(self.reg, **kw)
        return self.m

    def run_cli(self, *args, proj=None, env=None, json_out=True):
        """(exit code, parsed JSON or None, stdout, stderr)"""
        argv = ["-C", proj or self.proj] + list(args)
        if args[0] in ("add", "install", "ci") and "--allow-unverified" not in args and not getattr(self, "no_auto_allow", False):
            argv.append("--allow-unverified")      # declaration chunks are refused by default (admission, 0.5.0); these tests are about the import itself
        if json_out and "--json" not in args and args[0] in ("add", "install", "resolve", "ci", "verify", "env", "index"):
            argv.append("--json")
        out, err, code = io.StringIO(), io.StringIO(), 0
        e = dict(self.env, **(env or {}))
        with mock.patch.dict(os.environ, e, clear=False), contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            if "MREG_TOKEN" not in e:
                os.environ.pop("MREG_TOKEN", None)
            try:
                M.main(argv)
            except SystemExit as x:
                code = x.code if isinstance(x.code, int) else (0 if x.code is None else 1)
        txt = out.getvalue()
        js = None
        if "--json" in argv and txt.strip().startswith("{"):
            js = json.loads(txt)
            validate(js)
        return code, js, txt, err.getvalue()

    def lock(self, proj=None):
        return json.load(open(os.path.join(proj or self.proj, "mreg-chunks.lock.json"), encoding="utf-8"))


# ---------------------------------------------------------------- the documented JSON schema (NAMED_IMPORT.md) and a mini validator

REQ = {"entry": str, "package": str, "name": str, "exact_name": str, "module": str, "kind": str, "in_toolchain": bool,
       "provided_by": str}
SUCCESS = {
    "add": ["schema", "ok", "command", "registry", "train", "build", "variant", "manifest_sha256", "index_sha256", "requested", "cone", "dry_run", "toolchain",
            "budget", "notes", "supports",
            "fetched", "reused", "installed", "already_installed", "bytes_fetched", "requests", "requests_index", "requests_objects",
            "seconds", "lock", "chunk_dir", "entry_file"],
    "ci": ["schema", "ok", "command", "registry", "train", "build", "variant", "manifest_sha256", "index_sha256", "requested", "cone", "dry_run", "toolchain",
           "budget", "notes", "supports",
           "fetched", "reused", "installed", "already_installed", "removed_extra", "bytes_fetched", "requests", "requests_index",
           "requests_objects", "seconds", "lock", "chunk_dir", "lean_path"],
    "verify": ["schema", "ok", "command", "train", "build", "variant", "checked", "mismatched", "missing", "extra", "chunk_dir", "supports"],
    "env": ["schema", "ok", "command", "chunk_dir", "lean_path", "path_separator", "entry_file", "supports"],
    "index": ["schema", "ok", "command", "registry", "train", "build", "variants", "published_at", "manifest_sha256", "index_sha256",
              "index_dir", "fetched", "lookup", "requests", "seconds", "supports"],
}
SUCCESS["install"] = SUCCESS["add"]
SUCCESS["resolve"] = SUCCESS["add"]


def validate(js):
    assert js["schema"] == "mreg-named-import/1", js
    assert isinstance(js["ok"], bool)
    assert js["supports"] == M.SUPPORTS, "every document carries the fixed `supports` text"
    if not js["ok"] and js["command"] != "verify":
        assert set(js) >= {"schema", "ok", "command", "error"}
        er = js["error"]
        assert isinstance(er["kind"], str) and er["kind"] in M.EXIT and er["exit_code"] == M.EXIT[er["kind"]] and isinstance(er["message"], str)
        return
    miss = [k for k in SUCCESS[js["command"]] if k not in js]
    assert not miss, (js["command"], miss)
    if "requested" in js:
        for r in js["requested"]:
            for k, t in REQ.items():
                assert isinstance(r[k], t), (k, r)
            assert r["chunk"] is None or len(r["chunk"]) == 32
            assert (r["chunk"] is None) == r["in_toolchain"] == (r["provided_by"] == "toolchain")
        c = js["cone"]
        assert isinstance(c["chunks"], int) and isinstance(c["bytes_raw"], int) and isinstance(c["bytes_stored"], int)
    for k in ("fetched", "reused", "installed", "already_installed", "requests", "requests_objects", "bytes_fetched"):
        if k in js:
            assert isinstance(js[k], int), k
    if "seconds" in js:
        assert isinstance(js["seconds"], (int, float))


# ---------------------------------------------------------------- tests

@unittest.skipIf(_zstd is None, "needs Python 3.14 compression.zstd to build the test mirror")
class ResolveAndCone(Base):
    def test_cone_equals_independent_closure_for_every_declaration(self):
        m = self.mirror()
        n = 0
        for nm, ex, mo, kd, ci in m.decls:
            if ci is None or m.is_tc(ci) or nm in ("Mathlib.amb.x", "Mathlib.amb2.y") or mo.split(".")[0] not in ("Mathlib", "Batteries"):
                continue
            pkg = MATHLIB if mo.startswith("Mathlib") else BATTERIES
            code, js, out, err = self.run_cli("resolve", f"{pkg}#{ex}")
            self.assertEqual(code, 0, (out, err))
            want = m.cone(ci)
            self.assertEqual(js["cone"]["chunks"], len(want))
            self.assertNotIn("toolchain_chunks_excluded", js["cone"])
            self.assertEqual(js["requested"][0]["chunk"], m.ids[ci])
            self.assertEqual(js["cone"]["bytes_raw"], sum(len(m.raw[("checking", c)]) for c in want))
            n += 1
        self.assertGreater(n, 60)

    def test_edge_orders(self):
        for style in ("sorted", "shuffled"):
            shutil.rmtree(self.reg, True)
            shutil.rmtree(self.store, True)
            m = self.mirror(edge_style=style)
            code, js, out, err = self.run_cli("resolve", f"{MATHLIB}#Mathlib.n60_0")
            self.assertEqual(code, 0, (style, out, err))
            self.assertEqual(js["cone"]["chunks"], len(m.cone(60)))
            meta = json.load(open(os.path.join(self.store, "index", TRAIN, "b1", "READY.json")))["lookup"]
            self.assertEqual(meta["edges_sorted_by_source"], style == "sorted")
            self.assertNotIn("chunk_column", meta)

    def test_exact_and_display_names_ambiguity_unknown_and_package(self):
        m = self.mirror()
        c, js, o, e = self.run_cli("resolve", f"{MATHLIB}#Mathlib.weird.x%20y")        # exact form
        self.assertEqual(c, 0)
        self.assertEqual(js["requested"][0]["exact_name"], "Mathlib.weird.x%20y")
        c, js, o, e = self.run_cli("resolve", f"{MATHLIB}#Mathlib.weird.«x y»")        # a space cannot be in an entry: use the exact form
        self.assertEqual((c, js["error"]["kind"]), (1, "error"))
        c, js, o, e = self.run_cli("resolve", f"{MATHLIB}#Mathlib.amb.x")
        self.assertEqual((c, js["error"]["kind"]), (11, "ambiguous_name"))
        self.assertEqual(len(js["error"]["candidates"]), 2)
        c, js, o, e = self.run_cli("resolve", f"{MATHLIB}#Mathlib.amb%2Ex")
        self.assertEqual(c, 0)
        c, js, o, e = self.run_cli("resolve", f"{MATHLIB}#Mathlib.nope_0")
        self.assertEqual((c, js["error"]["kind"]), (10, "unknown_declaration"))
        c, js, o, e = self.run_cli("resolve", f"{MATHLIB}#Batteries.Data.dup")           # right name, wrong package
        self.assertEqual((c, js["error"]["kind"]), (10, "unknown_declaration"))
        self.assertIn(f"{BATTERIES}#Batteries.Data.dup", js["error"]["message"])
        c, js, o, e = self.run_cli("resolve", "nobody/else#Mathlib.n60_0")               # package not on the train
        self.assertEqual((c, js["error"]["kind"]), (12, "not_on_train"))
        c, js, o, e = self.run_cli("resolve", f"{MATHLIB}#Mathlib.amb2.y")                # same exact name, two chunks: not a duplicate
        self.assertEqual((c, js["error"]["kind"]), (11, "ambiguous_name"))
        self.assertEqual({x["chunk"] for x in js["error"]["candidates"]}, {m.ids[45], m.ids[46]})

    def test_toolchain_declaration_has_its_own_result_and_exit_0(self):
        """in_toolchain=1: 'provided by the toolchain; nothing to fetch', exit 0, no chunk, empty cone, no object request."""
        m = self.mirror()
        for ent in (f"{MATHLIB}#Init.Nat.add", f"{BATTERIES}#Init.foo", f"{MATHLIB}#Std.n1_0", f"{MATHLIB}#Lean.n4_1"):
            c, js, o, e = self.run_cli("resolve", ent)
            self.assertEqual(c, 0, (ent, o, e))
            r = js["requested"][0]
            self.assertEqual((r["in_toolchain"], r["provided_by"], r["chunk"]), (True, "toolchain", None))
            self.assertEqual(js["cone"]["chunks"], 0)
            self.assertEqual(js["would_fetch"], 0)
        c, js, o, e = self.run_cli("resolve", f"{MATHLIB}#Init.Nat.add", json_out=False)
        self.assertEqual(c, 0)
        self.assertIn("provided by the toolchain; nothing to fetch", o)
        c, js, o, e = self.run_cli("resolve", "nobody/else#Init.Nat.add")                  # the package must still be on the train
        self.assertEqual((c, js["error"]["kind"]), (12, "not_on_train"))
        # add: nothing fetched, a lock without chunks, an entry file that says so, exit 0
        c, js, o, e = self.run_cli("add", f"{MATHLIB}#Init.Nat.add")
        self.assertEqual(c, 0, (o, e))
        self.assertEqual((js["fetched"], js["requests_objects"], js["cone"]["chunks"]), (0, 0, 0))
        self.assertEqual(self.lock()["chunks"], [])
        self.assertIn("provided by the toolchain", open(os.path.join(self.proj, "MregChunks.lean")).read())
        self.assertFalse([x for x in os.listdir(os.path.join(self.store, "objects"))] if os.path.isdir(os.path.join(self.store, "objects")) else [])

    def test_duplicate_name_rows(self):
        """Later copies of a name point at the first owner's chunk: one declaration, a note, the first owner's cone. The same exact
        name with different chunks is ambiguous (see above)."""
        m = self.mirror()
        c, js, o, e = self.run_cli("resolve", f"{MATHLIB}#Mathlib.dupcopy.x")
        self.assertEqual(c, 0, (o, e))
        self.assertEqual(js["requested"][0]["chunk"], m.ids[44])
        self.assertEqual(js["cone"]["chunks"], len(m.cone(44)))
        self.assertTrue(any("appears in 2 modules" in n for n in js["notes"]), js["notes"])
        # a Mathlib-module copy of a Batteries declaration, asked through Mathlib, resolves to Batteries' chunk
        c, js, o, e = self.run_cli("resolve", f"{MATHLIB}#Batteries.Data.later")
        self.assertEqual(c, 0, (o, e))
        self.assertEqual(js["requested"][0]["chunk"], m.ids[12])
        c, js, o, e = self.run_cli("resolve", f"{BATTERIES}#Batteries.Data.later")
        self.assertEqual((c, js["requested"][0]["chunk"]), (0, m.ids[12]))

    def test_cold_then_warm_index(self):
        self.mirror()
        c1, j1, _, _ = self.run_cli("resolve", f"{MATHLIB}#Mathlib.n60_0", "--train", TRAIN)
        c2, j2, _, _ = self.run_cli("resolve", f"{MATHLIB}#Mathlib.n60_0", "--train", TRAIN)
        self.assertEqual((j1["requests_index"], j2["requests_index"]), (3, 0))
        # pointer + train doc + 3 index files, then pointer + train doc only
        self.assertEqual((j1["requests"], j2["requests"]), (5, 2))
        self.assertTrue(os.path.isdir(os.path.join(self.store, "index", TRAIN, "b1")))      # keyed by (train, build)


@unittest.skipIf(_zstd is None, "needs Python 3.14 compression.zstd")
class AddFetchInstall(Base):
    ENTRY = f"{MATHLIB}#Mathlib.n60_0"

    def test_add_installs_exact_cone_lock_entry_and_reuse(self):
        m = self.mirror()
        c, js, out, err = self.run_cli("add", self.ENTRY, "--train", TRAIN)
        self.assertEqual(c, 0, (out, err))
        want = m.cone(60)
        self.assertEqual(js["fetched"], len(want))
        self.assertEqual(js["requests_objects"], len(want))
        self.assertEqual(js["requests"], 5 + len(want))
        cd = os.path.join(self.proj, ".lake", "mreg-chunks", TRAIN)
        got = M.installed_chunk_files(cd)
        self.assertEqual(sorted(got), want)
        lic = os.path.join(cd, "THIRD_PARTY_LICENSES.txt")
        self.assertTrue(os.path.isfile(lic))
        self.assertIn("Apache License", open(lic, encoding="utf-8").read())
        for cid in want:
            self.assertEqual(open(got[cid], "rb").read(), m.raw[("checking", cid)])
            self.assertTrue(got[cid].endswith(os.path.join("Mreg", f"X{cid[:2]}", f"C{cid}.olean")))
        lk = self.lock()
        self.assertEqual((lk["schema"], lk["train"], lk["build"], lk["variant"]), ("mreg-chunks-lock/1", TRAIN, "b1", "checking"))
        self.assertEqual([x["id"] for x in lk["chunks"]], want)
        self.assertEqual(lk["counts"], {"declarations": 1, "chunks": len(want)})
        self.assertEqual(lk["manifest_sha256"], sha(m.manifest))
        self.assertEqual(lk["chunks"][0]["sha256_stored"], sha(m.stored[("checking", want[0])]))
        self.assertEqual(sorted(lk["covers_packages"]), ["batteries", "mathlib"])
        cfg = json.load(open(os.path.join(self.proj, "mreg.json")))
        self.assertEqual(cfg["chunks"]["declarations"], [self.ENTRY])
        ent = open(os.path.join(self.proj, "MregChunks.lean")).read()
        self.assertIn(f"import Mreg.X{m.ids[60][:2]}.C{m.ids[60]}", ent)
        # no [[require]] and no lake files: the forbidden mix cannot arise from add itself
        self.assertFalse(os.path.exists(os.path.join(self.proj, "lakefile.toml")))
        # second project, same store: nothing fetched
        p2 = os.path.join(self.tmp, "proj2")
        self.new_proj(p2)
        c, j2, out, err = self.run_cli("add", self.ENTRY, proj=p2)
        self.assertEqual(c, 0, err)
        self.assertEqual((j2["fetched"], j2["reused"], j2["requests_objects"]), (0, len(want), 0))
        self.assertEqual(sorted(M.installed_chunk_files(os.path.join(p2, ".lake", "mreg-chunks", TRAIN))), want)
        # same declaration again in the first project: idempotent, files already there
        c, j3, _, _ = self.run_cli("add", self.ENTRY)
        self.assertEqual((j3["installed"], j3["already_installed"]), (0, len(want)))
        self.assertEqual(len(self.lock()["declarations"]), 1)

    def test_second_declaration_grows_the_lock(self):
        m = self.mirror()
        self.run_cli("add", self.ENTRY)
        c, js, out, err = self.run_cli("add", f"{MATHLIB}#Mathlib.n50_1")
        self.assertEqual(c, 0, err)
        want = sorted(set(m.cone(60)) | set(m.cone(50)))
        self.assertEqual([x["id"] for x in self.lock()["chunks"]], want)
        self.assertEqual(len(self.lock()["declarations"]), 2)
        self.assertEqual(json.load(open(os.path.join(self.proj, "mreg.json")))["chunks"]["declarations"],
                         [self.ENTRY, f"{MATHLIB}#Mathlib.n50_1"])

    def test_failed_add_edits_nothing(self):
        self.mirror()
        c, js, out, err = self.run_cli("add", self.ENTRY, f"{MATHLIB}#Mathlib.nope")
        self.assertEqual(c, 10)
        self.assertEqual(self.proj_files(), [])

    def test_variant_full(self):
        m = self.mirror()
        c, js, out, err = self.run_cli("add", self.ENTRY, "--variant", "full")
        self.assertEqual(c, 0, err)
        cid = m.cone(60)[0]
        self.assertEqual(open(M.installed_chunk_files(os.path.join(self.proj, ".lake", "mreg-chunks", TRAIN))[cid], "rb").read(),
                         m.raw[("full", cid)])

    def test_dry_run_and_env_and_human_output(self):
        self.mirror()
        c, js, out, err = self.run_cli("add", self.ENTRY, "--dry-run")
        self.assertEqual(c, 0)
        self.assertTrue(js["dry_run"])
        self.assertEqual(js["would_fetch"], js["cone"]["chunks"])
        self.assertEqual(self.proj_files(), [])
        c, js, out, err = self.run_cli("add", self.ENTRY, json_out=False)
        self.assertEqual(c, 0)
        self.assertIn("cone ", out)
        self.assertIn("LEAN_PATH", out)
        c, js, out, err = self.run_cli("env")
        self.assertEqual(c, 0)
        self.assertTrue(js["chunk_dir"].endswith(TRAIN))
        self.assertTrue(js["entry_file"].endswith("MregChunks.lean"))

    def test_stored_object_flipped_byte_refused_and_nothing_written(self):
        m = self.mirror()
        want = m.cone(60)
        bad = want[len(want) // 2]
        m.corrupt_stored("checking", bad)
        c, js, out, err = self.run_cli("add", self.ENTRY, "--jobs", "1")
        self.assertEqual((c, js["error"]["kind"]), (14, "hash_mismatch"))
        self.assertEqual(js["error"]["chunk"], bad)
        self.assertFalse(os.path.exists(self.store_obj(m, "checking", bad)))     # nothing of that object
        self.assertFalse(os.path.exists(os.path.join(self.proj, "mreg-chunks.lock.json")))
        self.assertFalse(os.path.exists(os.path.join(self.proj, ".lake")))        # and nothing installed

    def store_obj(self, m, v, cid):
        return M.Store(self.store).obj(sha(m.stored[(v, cid)]))

    def test_decompressed_payload_mismatch_refused(self):
        m = self.mirror()
        want = m.cone(60)
        bad = want[0]
        other = _zstd.compress(m.raw[("checking", bad)][:-1] + b"X", 3)       # valid frame, stored hash will match, raw will not
        m.stored[("checking", bad)] = other
        m.write_all()
        m.publish_pointer()
        # the manifest now records the substituted stored hash, but the raw hash is of the genuine payload
        c, js, out, err = self.run_cli("add", self.ENTRY, "--jobs", "1")
        self.assertEqual((c, js["error"]["kind"]), (14, "hash_mismatch"))
        self.assertIn("decompressed", js["error"]["message"])
        self.assertFalse(os.path.exists(M.Store(self.store).obj(sha(other))))

    def test_missing_object(self):
        m = self.mirror()
        want = m.cone(60)
        os.unlink(m.obj("checking", want[3]))
        c, js, out, err = self.run_cli("add", self.ENTRY, "--jobs", "1")
        self.assertEqual((c, js["error"]["kind"]), (17, "missing_object"))
        self.assertEqual(js["error"]["chunk"], want[3])

    def test_interrupted_fetch_resumes(self):
        m = self.mirror()
        want = m.cone(60)
        real = M.Fetcher.get
        calls = {"n": 0}

        def flaky(self_, path):
            if "/checking/" in path:
                calls["n"] += 1
                if calls["n"] > 5:
                    raise M.NIError("network", "connection reset (test)")
            return real(self_, path)
        with mock.patch.object(M.Fetcher, "get", flaky):
            c, js, out, err = self.run_cli("add", self.ENTRY, "--jobs", "1")
        self.assertEqual((c, js["error"]["kind"]), (16, "network"))
        self.assertFalse(os.path.exists(os.path.join(self.proj, "mreg-chunks.lock.json")))
        have = [os.path.join(r, f) for r, _, fs in os.walk(os.path.join(self.store, "objects")) for f in fs]
        self.assertEqual(len(have), 5)
        self.assertFalse([h for h in have if ".part-" in h])
        c, js, out, err = self.run_cli("add", self.ENTRY, "--jobs", "1")
        self.assertEqual(c, 0, err)
        self.assertEqual((js["reused"], js["fetched"], js["requests_objects"]), (5, len(want) - 5, len(want) - 5))

    def test_keyboard_interrupt_exit_130(self):
        self.mirror()
        with mock.patch.object(M, "fetch_chunks", side_effect=KeyboardInterrupt):
            c, js, out, err = self.run_cli("add", self.ENTRY)
        self.assertEqual(c, 130)


@unittest.skipIf(_zstd is None, "needs Python 3.14 compression.zstd")
class LockCiVerify(Base):
    ENTRY = f"{MATHLIB}#Mathlib.n60_0"

    def test_ci_restores_exactly_the_locked_chunks_and_verify_rehashes(self):
        m = self.mirror()
        self.run_cli("add", self.ENTRY)
        want = m.cone(60)
        cd = os.path.join(self.proj, ".lake", "mreg-chunks", TRAIN)
        c, js, o, e = self.run_cli("verify")
        self.assertEqual((c, js["checked"], js["mismatched"]), (0, len(want), []))
        # wipe the project chunks AND the store; plant an extra chunk
        shutil.rmtree(cd)
        shutil.rmtree(self.store)
        extra = os.path.join(cd, "Mreg", "Xff")
        os.makedirs(extra)
        open(os.path.join(extra, "C" + "f" * 32 + ".olean"), "wb").write(b"junk")
        # another project's marker rules: the marker is absent here, so ci may use the directory
        c, js, o, e = self.run_cli("ci")
        self.assertEqual(c, 0, (o, e))
        self.assertEqual((js["fetched"], js["requests"], js["removed_extra"]), (len(want), len(want), 1))
        self.assertEqual(sorted(M.installed_chunk_files(cd)), want)
        lic = os.path.join(cd, "THIRD_PARTY_LICENSES.txt")
        self.assertTrue(os.path.isfile(lic))
        self.assertIn("Apache License", open(lic, encoding="utf-8").read())
        c, js, o, e = self.run_cli("ci")
        self.assertEqual((c, js["fetched"], js["requests"], js["already_installed"]), (0, 0, 0, len(want)))
        # a changed installed chunk: verify fails with 14, ci repairs it
        victim = M.installed_chunk_files(cd)[want[2]]
        b = bytearray(open(victim, "rb").read())
        b[-1] ^= 1
        open(victim, "wb").write(bytes(b))
        c, js, o, e = self.run_cli("verify")
        self.assertEqual((c, js["ok"], js["mismatched"]), (14, False, [want[2]]))
        c, js, o, e = self.run_cli("ci")
        self.assertEqual((c, js["installed"]), (0, 1))
        c, js, o, e = self.run_cli("verify")
        self.assertEqual(c, 0)

    def test_lock_is_deterministic_and_sorted(self):
        self.mirror()
        self.run_cli("add", self.ENTRY)
        a = open(os.path.join(self.proj, "mreg-chunks.lock.json"), "rb").read()
        self.run_cli("add", self.ENTRY)
        self.assertEqual(a, open(os.path.join(self.proj, "mreg-chunks.lock.json"), "rb").read())
        ids = [c["id"] for c in json.loads(a)["chunks"]]
        self.assertEqual(ids, sorted(ids))

    def test_ci_refuses_a_tampered_lock_hash(self):
        self.mirror()
        self.run_cli("add", self.ENTRY)
        lp = os.path.join(self.proj, "mreg-chunks.lock.json")
        lk = json.load(open(lp))
        lk["chunks"][0]["sha256_stored"] = "0" * 64
        json.dump(lk, open(lp, "w"))
        shutil.rmtree(self.store)
        c, js, o, e = self.run_cli("ci")
        self.assertEqual((c, js["error"]["kind"]), (14, "hash_mismatch"))


@unittest.skipIf(_zstd is None, "needs Python 3.14 compression.zstd")
class Builds(Base):
    ENTRY = f"{MATHLIB}#Mathlib.n60_0"

    def test_pointer_missing(self):
        m = self.mirror(publish=False)
        c, js, o, e = self.run_cli("add", self.ENTRY, "--chunks")
        self.assertEqual((c, js["error"]["kind"]), (12, "not_on_train"))
        self.assertIn("current.json", js["error"]["message"])
        with mock.patch.dict(os.environ, self.env):
            self.assertFalse(M.ni_probe(mock.Mock(spec=["dir", "train"], dir=self.proj, train=TRAIN)))

    def test_pointer_manifest_hash_mismatch_caches_nothing(self):
        m = self.mirror(publish=False)
        m.publish_pointer(manifest_sha="1" * 64, index={"manifest.tsv.gz": "1" * 64})
        c, js, o, e = self.run_cli("add", self.ENTRY)
        self.assertEqual((c, js["error"]["kind"]), (14, "hash_mismatch"))
        self.assertFalse(os.path.exists(os.path.join(self.store, "index", TRAIN, "b1")))
        self.assertEqual(self.proj_files(), [])
        # a pointer that is not a pointer: the index cannot be verified, which is an error (19), never an answer
        m.wr(m.p("current.json"), b'{"schema": "other"}')
        c, js, o, e = self.run_cli("add", self.ENTRY)
        self.assertEqual((c, js["error"]["kind"]), (19, "index_unavailable"))

    def new_build(self, m, name="b2"):
        """A second, different build of the same train next to b1, immutable b1 untouched."""
        m2 = Mirror(self.reg, build=name, seed=11, publish=False, payload_tag=b"-" + name.encode())
        m2.publish_pointer()
        return m2

    def test_lock_on_b1_pointer_on_b2(self):
        m1 = self.mirror()
        self.run_cli("add", self.ENTRY)
        lock1 = self.lock()
        m2 = self.new_build(m1)
        self.assertNotEqual(sha(m1.manifest), sha(m2.manifest))
        # ci restores the LOCKED build although the pointer moved on
        shutil.rmtree(os.path.join(self.proj, ".lake"))
        shutil.rmtree(self.store)
        c, js, o, e = self.run_cli("ci")
        self.assertEqual((c, js["build"]), (0, "b1"), (o, e))
        want = m1.cone(60)
        self.assertEqual(js["fetched"], len(want))
        for cid, p in M.installed_chunk_files(os.path.join(self.proj, ".lake", "mreg-chunks", TRAIN)).items():
            self.assertEqual(open(p, "rb").read(), m1.raw[("checking", cid)])        # b1 bytes, not b2 bytes
        self.assertEqual(self.lock(), lock1)
        # add stays on b1 and says so; an explicit other build is a forbidden mix
        c, js, o, e = self.run_cli("add", f"{MATHLIB}#Mathlib.n50_1")
        self.assertEqual((c, js["build"]), (0, "b1"), (o, e))
        self.assertTrue(any("current build is b2" in n for n in js["notes"]))
        c, js, o, e = self.run_cli("add", f"{MATHLIB}#Mathlib.n50_1", "--build", "b2")
        self.assertEqual((c, js["error"]["kind"]), (15, "forbidden_mix"))
        self.assertIn("two builds", js["error"]["message"])
        # moving the project is explicit and replaces every chunk
        c, js, o, e = self.run_cli("install", "--upgrade-build")
        self.assertEqual((c, js["build"]), (0, "b2"), (o, e))
        self.assertEqual(self.lock()["build"], "b2")
        self.assertEqual(len(self.lock()["declarations"]), 2)
        for cid, p in M.installed_chunk_files(os.path.join(self.proj, ".lake", "mreg-chunks", TRAIN)).items():
            self.assertEqual(open(p, "rb").read(), m2.raw[("checking", cid)])

    def test_locked_build_removed_fails_clearly(self):
        m1 = self.mirror()
        self.run_cli("add", self.ENTRY)
        self.new_build(m1)
        shutil.rmtree(m1.p("b1"))
        shutil.rmtree(os.path.join(self.proj, ".lake"))
        shutil.rmtree(self.store)
        c, js, o, e = self.run_cli("ci")
        self.assertEqual((c, js["error"]["kind"]), (18, "build_removed"))
        self.assertIn("b1", js["error"]["message"])
        # and with the objects cached locally the same ci succeeds without the registry's b1
        m1b = Mirror(self.reg, build="b1", publish=False)      # restore, fill the store, remove again
        self.run_cli("ci")
        shutil.rmtree(m1b.p("b1"))
        shutil.rmtree(os.path.join(self.proj, ".lake"))
        c, js, o, e = self.run_cli("ci")
        self.assertEqual((c, js["fetched"], js["requests"]), (0, 0, 0))


@unittest.skipIf(_zstd is None, "needs Python 3.14 compression.zstd")
class Mixes(Base):
    ENTRY = f"{MATHLIB}#Mathlib.n60_0"

    def test_module_files_of_a_covered_package_forbid_chunks(self):
        self.mirror()
        json.dump({"packages": [{"name": "mathlib", "rev": "x"}]}, open(os.path.join(self.proj, "lake-manifest.json"), "w"))
        c, js, o, e = self.run_cli("add", self.ENTRY)
        self.assertEqual((c, js["error"]["kind"]), (15, "forbidden_mix"))
        self.assertIn("mathlib (from lake-manifest.json)", js["error"]["message"])
        self.assertEqual(self.proj_files(), ["lake-manifest.json"])
        os.unlink(os.path.join(self.proj, "lake-manifest.json"))
        open(os.path.join(self.proj, "lakefile.toml"), "w").write('name = "P"\n\n[[require]]\nname = "batteries"\ngit = "x"\nrev = "y"\n')
        c, js, o, e = self.run_cli("add", self.ENTRY)
        self.assertEqual(c, 15)
        self.assertIn("batteries (from lakefile.toml [[require]])", js["error"]["message"])
        os.unlink(os.path.join(self.proj, "lakefile.toml"))
        os.makedirs(os.path.join(self.proj, ".lake"))
        json.dump({"packages": {"mathlib": {"modules": []}}}, open(os.path.join(self.proj, ".lake", "mreg-state.json"), "w"))
        c, js, o, e = self.run_cli("add", self.ENTRY)
        self.assertEqual(c, 15)
        os.unlink(os.path.join(self.proj, ".lake", "mreg-state.json"))
        json.dump({"schema": "mreg-lock/0", "packages": [{"lake_name": "mathlib", "from": "registry"}]}, open(os.path.join(self.proj, "mreg.lock"), "w"))
        c, js, o, e = self.run_cli("add", self.ENTRY)
        self.assertEqual(c, 15)
        os.unlink(os.path.join(self.proj, "mreg.lock"))
        c, js, o, e = self.run_cli("add", self.ENTRY)
        self.assertEqual(c, 0)

    def test_ci_refuses_when_module_files_appear(self):
        self.mirror()
        self.run_cli("add", self.ENTRY)
        json.dump({"packages": [{"name": "mathlib"}]}, open(os.path.join(self.proj, "lake-manifest.json"), "w"))
        c, js, o, e = self.run_cli("ci")
        self.assertEqual((c, js["error"]["kind"]), (15, "forbidden_mix"))

    def test_checking_and_full_not_mixed(self):
        self.mirror()
        self.run_cli("add", self.ENTRY)
        c, js, o, e = self.run_cli("add", f"{MATHLIB}#Mathlib.n50_1", "--variant", "full")
        self.assertEqual((c, js["error"]["kind"]), (15, "forbidden_mix"))
        self.assertIn("checking and full", js["error"]["message"])
        self.assertEqual(self.lock()["variant"], "checking")

    def test_two_trains_not_mixed(self):
        self.mirror()
        self.run_cli("add", self.ENTRY)
        c, js, o, e = self.run_cli("add", f"{MATHLIB}#Mathlib.n50_1", "--train", "lean-4.99.0")
        self.assertEqual((c, js["error"]["kind"]), (15, "forbidden_mix"))
        self.assertIn("two trains", js["error"]["message"])

    def test_module_level_add_of_a_covered_package_refused(self):
        self.mirror()
        self.run_cli("add", self.ENTRY)
        lf = os.path.join(self.proj, "lakefile.toml")
        open(lf, "w").write('name = "P"\n')
        c, js, o, e = self.run_cli("add", MATHLIB, "--no-lake-update", "--train", TRAIN, json_out=False)
        self.assertEqual(c, 15, (o, e))
        self.assertIn("forbidden_mix", e)
        self.assertEqual(open(lf).read(), 'name = "P"\n')


class _Srv(http.server.ThreadingHTTPServer):
    daemon_threads = True


def serve(root, token="tok", fail=()):
    log = []

    class H(http.server.BaseHTTPRequestHandler):
        def log_message(self, *a):
            pass

        def do_GET(self):
            log.append(self.path)
            if self.headers.get("x-mreg-token") != token:
                self.send_response(403); self.end_headers(); return
            if any(f in self.path for f in fail):
                self.send_response(500); self.end_headers(); return
            p = os.path.join(root, *self.path.split("/"))
            if not os.path.isfile(p):
                self.send_response(404); self.end_headers(); return
            b = open(p, "rb").read()
            self.send_response(200)
            self.send_header("Content-Length", str(len(b)))
            self.end_headers()
            self.wfile.write(b)
    srv = _Srv(("127.0.0.1", 0), H)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    return srv, log


@unittest.skipIf(_zstd is None, "needs Python 3.14 compression.zstd")
class Http(Base):
    ENTRY = f"{MATHLIB}#Mathlib.n60_0"

    def test_token_auth_and_network_exit_codes(self):
        m = self.mirror()
        srv, log = serve(self.reg)
        self.addCleanup(srv.shutdown)
        base = f"http://127.0.0.1:{srv.server_address[1]}"
        c, js, o, e = self.run_cli("add", self.ENTRY, env={"MREG_REGISTRY": base, "MREG_TOKEN": "tok"})
        self.assertEqual(c, 0, (o, e))
        self.assertEqual(js["fetched"], len(m.cone(60)))
        n = len(log)
        # no token at all: auth error, no request made
        shutil.rmtree(self.proj)
        self.new_proj(self.proj)
        c, js, o, e = self.run_cli("add", self.ENTRY, env={"MREG_REGISTRY": base})
        self.assertEqual((c, js["error"]["kind"]), (13, "auth"))
        self.assertEqual(len(log), n)
        # wrong token: the registry's 403 is an authentication error
        c, js, o, e = self.run_cli("add", self.ENTRY, env={"MREG_REGISTRY": base, "MREG_TOKEN": "nope"})
        self.assertEqual((c, js["error"]["kind"]), (13, "auth"))
        self.assertIn("403", js["error"]["message"])
        self.assertNotIn("nope", js["error"]["message"])
        # nothing listening: network
        s = socket.socket(); s.bind(("127.0.0.1", 0)); port = s.getsockname()[1]; s.close()
        c, js, o, e = self.run_cli("add", self.ENTRY, env={"MREG_REGISTRY": f"http://127.0.0.1:{port}", "MREG_TOKEN": "tok"})
        self.assertEqual((c, js["error"]["kind"]), (16, "network"))

    def test_server_error_on_one_object_is_network_and_resumes(self):
        m = self.mirror()
        want = m.cone(60)
        srv, log = serve(self.reg, fail=(f"C{want[4]}",))
        self.addCleanup(srv.shutdown)
        base = f"http://127.0.0.1:{srv.server_address[1]}"
        env = {"MREG_REGISTRY": base, "MREG_TOKEN": "tok"}
        c, js, o, e = self.run_cli("add", self.ENTRY, env=env, )
        self.assertEqual((c, js["error"]["kind"]), (16, "network"))
        srv2, log2 = serve(self.reg)
        self.addCleanup(srv2.shutdown)
        env["MREG_REGISTRY"] = f"http://127.0.0.1:{srv2.server_address[1]}"
        c, js, o, e = self.run_cli("add", self.ENTRY, env=env)
        self.assertEqual(c, 0)
        objs = [p for p in log2 if p.endswith(".olean.zst")]
        self.assertEqual(len(objs), js["fetched"])
        self.assertLessEqual(js["fetched"], len(want))
        self.assertEqual(js["fetched"] + js["reused"], len(want))


@unittest.skipIf(_zstd is None, "needs Python 3.14 compression.zstd")
class Schema(Base):
    def test_every_command_validates_and_documents_exit_codes(self):
        self.mirror()
        for args in (("resolve", f"{MATHLIB}#Mathlib.n60_0"), ("add", f"{MATHLIB}#Mathlib.n60_0"), ("verify",), ("ci",), ("env",),
                     ("install", "--dry-run"), ("resolve", f"{MATHLIB}#zzz"), ("resolve", "bad entry")):
            c, js, o, e = self.run_cli(*args)
            self.assertIsNotNone(js, (args, o, e))      # run_cli validated it
        doc = open(os.path.join(HERE, "NAMED_IMPORT.md"), encoding="utf-8").read()
        for kind, code in M.EXIT.items():
            self.assertIn(f"| {code} | `{kind}`", doc)
        for k in set(sum(SUCCESS.values(), [])):
            self.assertIn(f"`{k}`", doc, k)


@unittest.skipIf(_zstd is None, "needs Python 3.14 compression.zstd")
class FailClosed(Base):
    """Plan A.7: an 'unknown declaration' answer names the train, the build and the index hashes it was computed from; if the pointer,
    an index file or its hash check is unavailable the answer is an error with its own exit code, never 'not found'."""
    UNKNOWN = f"{MATHLIB}#Mathlib.nope_0"

    def test_unknown_declaration_names_train_build_and_index_hashes(self):
        m = self.mirror()
        c, js, o, e = self.run_cli("resolve", self.UNKNOWN)
        self.assertEqual((c, js["error"]["kind"]), (10, "unknown_declaration"))
        af = js["error"]["answered_from"]
        self.assertEqual((af["train"], af["build"], af["manifest_sha256"]), (TRAIN, "b1", sha(m.manifest)))
        self.assertEqual(af["index_sha256"], m.index_hashes())
        self.assertIn(TRAIN, js["error"]["message"])
        self.assertIn("build b1", js["error"]["message"])
        self.assertIn(sha(m.assignment), js["error"]["message"])
        # the human form says the same; the wrong-package form (also exit 10) too
        c, js, o, e = self.run_cli("resolve", self.UNKNOWN, json_out=False)
        self.assertEqual(c, 10)
        self.assertIn("build b1", e)
        c, js, o, e = self.run_cli("resolve", f"{MATHLIB}#Batteries.Data.dup")
        self.assertEqual(c, 10)
        self.assertEqual(js["error"]["answered_from"]["index_sha256"], m.index_hashes()) if "answered_from" in js["error"] else None

    def test_unknown_from_a_locked_build_names_that_build(self):
        m = self.mirror()
        self.run_cli("add", f"{MATHLIB}#Mathlib.n60_0")
        c, js, o, e = self.run_cli("resolve", self.UNKNOWN)
        self.assertEqual((c, js["error"]["answered_from"]["build"]), (10, "b1"))

    def test_pointer_without_index_hashes_is_an_error_never_an_answer(self):
        m = self.mirror(publish=False)
        for drop in (("index_sha256",), ):
            m.publish_pointer(drop=drop)
            for ent in (self.UNKNOWN, f"{MATHLIB}#Mathlib.n60_0"):
                c, js, o, e = self.run_cli("resolve", ent)
                self.assertEqual((c, js["error"]["kind"]), (19, "index_unavailable"), ent)
                self.assertIn("not a 'not found'", js["error"]["message"])
        # a hash missing, a hash that is not hex, the manifest hash disagreeing with the pointer's own
        for bad in ({"assignment.tsv.gz": "zz"}, {"chunk_edges.tsv.gz": ""}, {"manifest.tsv.gz": "2" * 64}):
            m.publish_pointer(index=bad)
            c, js, o, e = self.run_cli("resolve", self.UNKNOWN)
            self.assertEqual((c, js["error"]["kind"]), (19, "index_unavailable"), bad)
        ptr = json.load(open(m.p("current.json")))
        del ptr["index_sha256"]["chunk_edges.tsv.gz"]
        m.wr(m.p("current.json"), json.dumps(ptr).encode())
        c, js, o, e = self.run_cli("resolve", self.UNKNOWN)
        self.assertEqual((c, js["error"]["kind"]), (19, "index_unavailable"))
        self.assertFalse(os.path.exists(os.path.join(self.store, "index")))      # nothing was fetched or cached

    def test_pointer_missing_or_not_json_is_never_unknown(self):
        m = self.mirror(publish=False)
        c, js, o, e = self.run_cli("resolve", self.UNKNOWN)
        self.assertEqual((c, js["error"]["kind"]), (12, "not_on_train"))
        m.wr(m.p("current.json"), b"<html>not json")
        c, js, o, e = self.run_cli("resolve", self.UNKNOWN)
        self.assertEqual((c, js["error"]["kind"]), (19, "index_unavailable"))

    def test_index_file_missing_tampered_or_unreadable_is_an_error(self):
        m = self.mirror()
        good = {n: open(m.idx(n), "rb").read() for n in M.INDEX_FILES}
        for n in M.INDEX_FILES:
            os.unlink(m.idx(n))                                             # absent
            c, js, o, e = self.run_cli("resolve", self.UNKNOWN)
            self.assertEqual((c, js["error"]["kind"]), (18, "build_removed"), n)
            self.assertIn("no answer can be computed", js["error"]["message"])
            bad = bytearray(good[n])
            bad[len(bad) // 2] ^= 1                                          # a flipped byte
            m.wr(m.idx(n), bytes(bad))
            c, js, o, e = self.run_cli("resolve", self.UNKNOWN)
            self.assertEqual((c, js["error"]["kind"]), (14, "hash_mismatch"), n)
            m.wr(m.idx(n), good[n])
            self.assertFalse(os.path.exists(os.path.join(self.store, "index", TRAIN, "b1")))
        c, js, o, e = self.run_cli("resolve", self.UNKNOWN)               # all restored: now the honest "unknown" answer
        self.assertEqual(c, 10)

    def test_index_with_wrong_columns_or_rows_is_unusable_not_unknown(self):
        for what in ("columns", "tc_with_chunk", "chunk_without_tc", "bad_flag", "edge_unknown_chunk", "short_row"):
            shutil.rmtree(self.reg, True)
            shutil.rmtree(self.store, True)
            m = self.mirror(publish=False)
            if what == "columns":     # the pre-final column names
                txt = gzip.decompress(m.assignment).decode().replace("in_toolchain\tchunk", "in_init\tmerged_chunk")
            elif what == "tc_with_chunk":
                txt = gzip.decompress(m.assignment).decode().replace("Init.Nat.add\tInit.Nat.add\tInit.Core\tdef\t1\t", "Init.Nat.add\tInit.Nat.add\tInit.Core\tdef\t1\t" + "a" * 32)
            elif what == "chunk_without_tc":
                txt = gzip.decompress(m.assignment).decode().replace("Init.Nat.add\tInit.Nat.add\tInit.Core\tdef\t1\t", "Init.Nat.add\tInit.Nat.add\tInit.Core\tdef\t0\t")
            elif what == "bad_flag":
                txt = gzip.decompress(m.assignment).decode().replace("Init.Nat.add\tInit.Nat.add\tInit.Core\tdef\t1\t", "Init.Nat.add\tInit.Nat.add\tInit.Core\tdef\t2\t")
            elif what == "short_row":
                txt = gzip.decompress(m.assignment).decode() + "x\ty\n"
            else:
                txt = None
            if txt is not None:
                m.assignment = gzip.compress(txt.encode())
                m.wr(m.idx("assignment.tsv.gz"), m.assignment)
            else:
                m.edges = gzip.compress(gzip.decompress(m.edges) + ("f" * 32 + "\t" + "e" * 32 + "\n").encode())
                m.wr(m.idx("chunk_edges.tsv.gz"), m.edges)
            m.publish_pointer()
            c, js, o, e = self.run_cli("resolve", self.UNKNOWN)
            self.assertEqual((c, js["error"]["kind"]), (19, "index_unavailable"), (what, js))
            self.assertFalse(os.path.exists(os.path.join(self.store, "index", TRAIN, "b1")), what)

    def test_network_failure_for_the_pointer_is_not_unknown(self):
        self.mirror()
        s = socket.socket(); s.bind(("127.0.0.1", 0)); port = s.getsockname()[1]; s.close()
        c, js, o, e = self.run_cli("resolve", self.UNKNOWN, env={"MREG_REGISTRY": f"http://127.0.0.1:{port}", "MREG_TOKEN": "tok"})
        self.assertEqual((c, js["error"]["kind"]), (16, "network"))

    def test_locked_project_with_pointer_rewritten_for_the_same_build_is_refused(self):
        m = self.mirror()
        self.run_cli("add", f"{MATHLIB}#Mathlib.n60_0")
        m.publish_pointer(index={"assignment.tsv.gz": "3" * 64})            # same build name, different hash: builds are immutable
        c, js, o, e = self.run_cli("resolve", self.UNKNOWN)
        self.assertEqual((c, js["error"]["kind"]), (14, "hash_mismatch"))

    def test_module_level_fallback_unknown_names_the_build(self):
        """The module-level path's 'no declaration' answer also says which build's graph it is from (and that it says nothing more)."""
        src = open(os.path.join(HERE, "mreg.py"), encoding="utf-8").read()
        self.assertIn("another build, version or train", src)
        self.assertIn("(build {b.key}, manifest sha256 {b.manifest_sha256})", src)


@unittest.skipIf(_zstd is None, "needs Python 3.14 compression.zstd")
class ToolchainGate(Base):
    ENTRY = f"{MATHLIB}#Mathlib.n60_0"

    def test_mismatch_missing_and_equivalent_forms(self):
        m = self.mirror()
        for tc in ("leanprover/lean4:v4.34.1", "leanprover/lean4:v4.35.0-rc1", "leanprover/lean4:nightly-2026-11-01", "v4.35"):
            open(os.path.join(self.proj, "lean-toolchain"), "w").write(tc + "\n")
            for cmd in ("add", "install"):
                c, js, o, e = self.run_cli(cmd, self.ENTRY)
                self.assertEqual((c, js["error"]["kind"]), (20, "toolchain_mismatch"), (tc, cmd))
                self.assertEqual(js["error"]["toolchain"], {"project": tc, "train": TOOLCHAIN, "match": False})
            self.assertEqual(self.proj_files(), [])
            self.assertFalse(os.path.isdir(os.path.join(self.store, "objects")))      # nothing fetched, no index either
            self.assertFalse(os.path.isdir(os.path.join(self.store, "index")))
        os.unlink(os.path.join(self.proj, "lean-toolchain"))
        c, js, o, e = self.run_cli("add", self.ENTRY)
        self.assertEqual((c, js["error"]["kind"]), (20, "toolchain_mismatch"))
        self.assertIn("no lean-toolchain", js["error"]["message"])
        # the short form v4.35.0 means leanprover/lean4:v4.35.0
        open(os.path.join(self.proj, "lean-toolchain"), "w").write("v4.35.0\n")
        c, js, o, e = self.run_cli("add", self.ENTRY)
        self.assertEqual((c, js["toolchain"]["match"]), (0, True), (o, e))

    def test_resolve_reports_the_mismatch_without_refusing(self):
        self.mirror()
        open(os.path.join(self.proj, "lean-toolchain"), "w").write("leanprover/lean4:v4.34.1\n")
        c, js, o, e = self.run_cli("resolve", self.ENTRY)
        self.assertEqual(c, 0)
        self.assertEqual(js["toolchain"], {"project": "leanprover/lean4:v4.34.1", "train": TOOLCHAIN, "match": False})
        self.assertTrue(any("would be refused" in n for n in js["notes"]))
        c, js, o, e = self.run_cli("add", self.ENTRY, "--dry-run")
        self.assertEqual((c, js["toolchain"]["match"]), (0, False))

    def test_ci_checks_the_locked_toolchain(self):
        self.mirror()
        self.run_cli("add", self.ENTRY)
        self.assertEqual(self.lock()["toolchain"], TOOLCHAIN)
        shutil.rmtree(self.store)
        open(os.path.join(self.proj, "lean-toolchain"), "w").write("leanprover/lean4:v4.34.1\n")
        c, js, o, e = self.run_cli("ci")
        self.assertEqual((c, js["error"]["kind"]), (20, "toolchain_mismatch"))
        self.assertFalse(os.path.isdir(os.path.join(self.store, "objects")))
        open(os.path.join(self.proj, "lean-toolchain"), "w").write(TOOLCHAIN + "\n")
        c, js, o, e = self.run_cli("ci")
        self.assertEqual(c, 0, (o, e))

    def test_train_document_without_toolchain_refuses(self):
        m = self.mirror()
        doc = json.load(open(os.path.join(self.reg, "v1", "index", "trains", f"{TRAIN}.json")))
        del doc["toolchain"]
        m.wr(os.path.join(self.reg, "v1", "index", "trains", f"{TRAIN}.json"), json.dumps(doc).encode())
        c, js, o, e = self.run_cli("add", self.ENTRY)
        self.assertEqual((c, js["error"]["kind"]), (1, "error"))


@unittest.skipIf(_zstd is None, "needs Python 3.14 compression.zstd")
class RequestBudget(Base):
    ENTRY = f"{MATHLIB}#Mathlib.n60_0"

    def test_over_budget_is_refused_before_any_chunk_is_fetched(self):
        m = self.mirror()
        want = m.cone(60)
        self.assertGreater(len(want), 5)
        c, js, o, e = self.run_cli("add", self.ENTRY, "--max-requests", "3")
        self.assertEqual((c, js["error"]["kind"]), (21, "over_budget"))
        er = js["error"]
        self.assertEqual((er["cone_chunks"], er["requests_needed"], er["max_requests"]), (len(want), len(want), 3))
        self.assertEqual(er["bytes_raw"], sum(len(m.raw[("checking", x)]) for x in want))
        self.assertEqual(er["bytes_stored"], sum(len(m.stored[("checking", x)]) for x in want))
        self.assertIn("--allow-over-budget", er["message"])
        self.assertFalse(os.path.isdir(os.path.join(self.store, "objects")))
        self.assertEqual(self.proj_files(), [])
        c, js, o, e = self.run_cli("install", self.ENTRY, "--max-requests", "3")
        self.assertEqual(c, 21)
        # the explicit flag proceeds
        c, js, o, e = self.run_cli("add", self.ENTRY, "--max-requests", "3", "--allow-over-budget")
        self.assertEqual((c, js["fetched"]), (0, len(want)), (o, e))
        self.assertEqual((js["budget"]["over_budget"], js["budget"]["allowed"]), (True, True))
        # at exactly the budget it proceeds without the flag; warm needs 0 requests so even 0 is enough
        shutil.rmtree(os.path.join(self.proj, ".lake"))
        c, js, o, e = self.run_cli("add", self.ENTRY, "--max-requests", "0")
        self.assertEqual((c, js["fetched"], js["budget"]["requests_needed"]), (0, 0, 0))

    def test_default_is_2000_and_exact_boundary(self):
        self.assertEqual(M.DEFAULT_MAX_REQUESTS, 2000)
        m = self.mirror()
        n = len(m.cone(60))
        c, js, o, e = self.run_cli("add", self.ENTRY)
        self.assertEqual(js["budget"]["max_requests"], 2000)
        shutil.rmtree(self.store)
        shutil.rmtree(os.path.join(self.proj, ".lake"))
        c, js, o, e = self.run_cli("add", self.ENTRY, "--max-requests", str(n))
        self.assertEqual(c, 0)
        shutil.rmtree(self.store)
        shutil.rmtree(os.path.join(self.proj, ".lake"))
        c, js, o, e = self.run_cli("add", self.ENTRY, "--max-requests", str(n - 1))
        self.assertEqual(c, 21)

    def test_dry_run_and_resolve_report_the_budget_and_never_refuse(self):
        m = self.mirror()
        n = len(m.cone(60))
        for args in (("resolve", self.ENTRY), ("add", self.ENTRY, "--dry-run"), ("install", self.ENTRY, "--dry-run")):
            c, js, o, e = self.run_cli(*args, "--max-requests", "3")
            self.assertEqual(c, 0, args)
            self.assertEqual(js["budget"], {"max_requests": 3, "requests_needed": n, "over_budget": True, "allowed": False})
            self.assertEqual((js["would_fetch"], js["cone"]["chunks"], js["fetched"]), (n, n, 0))
            self.assertTrue(any("over budget" in x for x in js["notes"]))
        c, js, o, e = self.run_cli("resolve", self.ENTRY, "--max-requests", "3", json_out=False)
        self.assertIn("--max-requests 3", o)
        self.assertFalse(os.path.isdir(os.path.join(self.store, "objects")))
        self.assertEqual(self.proj_files(), [])

    def test_ci_has_the_same_budget(self):
        m = self.mirror()
        self.run_cli("add", self.ENTRY)
        shutil.rmtree(self.store)
        shutil.rmtree(os.path.join(self.proj, ".lake"))
        c, js, o, e = self.run_cli("ci", "--max-requests", "3")
        self.assertEqual((c, js["error"]["kind"]), (21, "over_budget"))
        self.assertFalse(os.path.isdir(os.path.join(self.store, "objects")))
        c, js, o, e = self.run_cli("ci", "--max-requests", "3", "--allow-over-budget")
        self.assertEqual((c, js["fetched"]), (0, len(m.cone(60))))


@unittest.skipIf(_zstd is None, "needs Python 3.14 compression.zstd")
class SupportsAndIndex(Base):
    ENTRY = f"{MATHLIB}#Mathlib.n60_0"

    def test_supports_is_one_fixed_field_in_every_document_and_line(self):
        self.mirror()
        seen = set()
        for args in (("resolve", self.ENTRY), ("add", self.ENTRY), ("install", self.ENTRY), ("verify",), ("ci",), ("env",), ("index",),
                     ("resolve", f"{MATHLIB}#zzz"), ("resolve", "bad entry"), ("resolve", f"{MATHLIB}#Init.Nat.add"),
                     ("add", self.ENTRY, "--max-requests", "0", "--variant", "full")):
            c, js, o, e = self.run_cli(*args)
            self.assertIsNotNone(js, (args, o, e))
            seen.add(js["supports"])
        self.assertEqual(seen, {M.SUPPORTS})
        for word in ("kernel checking", "by name", "instances", "simp sets", "notation", "tactics", "not a base for writing new proofs"):
            self.assertIn(word, M.SUPPORTS)
        self.assertNotIn("write proofs against", M.SUPPORTS.replace("not a base for writing new proofs", ""))
        # human output: the last line, identical text
        for args in (("resolve", self.ENTRY), ("add", self.ENTRY), ("verify",), ("env",)):
            c, js, o, e = self.run_cli(*args, json_out=False)
            self.assertEqual(o.rstrip("\n").splitlines()[-1], "supports: " + M.SUPPORTS, args)
        # the generated entry file repeats it
        self.assertIn(M.SUPPORTS, open(os.path.join(self.proj, "MregChunks.lean"), encoding="utf-8").read())

    def test_index_command_verifies_and_reports_where(self):
        m = self.mirror()
        c, js, o, e = self.run_cli("index", "--train", TRAIN)
        self.assertEqual(c, 0, (o, e))
        self.assertEqual((js["train"], js["build"], js["fetched"], js["requests"]), (TRAIN, "b1", True, 4))   # pointer + 3 files
        self.assertEqual(js["index_sha256"], m.index_hashes())
        self.assertTrue(os.path.isfile(os.path.join(js["index_dir"], "assignment.tsv.gz")))
        self.assertEqual(sha(open(os.path.join(js["index_dir"], "assignment.tsv.gz"), "rb").read()), sha(m.assignment))
        c, js, o, e = self.run_cli("index", "--train", TRAIN)
        self.assertEqual((js["fetched"], js["requests"]), (False, 1))
        m.publish_pointer(drop=("index_sha256",))
        c, js, o, e = self.run_cli("index", "--train", TRAIN)
        self.assertEqual((c, js["error"]["kind"]), (19, "index_unavailable"))

    def test_exit_code_table_in_the_docs_and_codes(self):
        self.assertEqual((M.EXIT["index_unavailable"], M.EXIT["toolchain_mismatch"], M.EXIT["over_budget"]), (19, 20, 21))


def convert_old_tables(src, dst):
    """The measurement tables of the old 4.34.1 store -> the final layout (the client reads only the final one). Old columns:
    name, exact_name, module, kind, type_hash, in_init, kernel_block, merged_chunk, n_deps; the edges join merged chunks. A row whose
    module root is Init/Std/Lean/Lake gets in_toolchain=1 and an empty chunk; the edge table keeps only edges between chunks that
    are not toolchain chunks. Returns counts."""
    tcchunks, keep, ndecl, ntc = set(), set(), 0, 0
    with gzip.open(os.path.join(src, "assignment.tsv.gz"), "rt", encoding="utf-8", newline="") as f, \
            gzip.open(os.path.join(dst, "assignment.tsv.gz"), "wt", encoding="utf-8", newline="", compresslevel=1) as g:
        hdr = f.readline().rstrip("\n").split("\t")
        iname, iex, imod, ikind, ich = (hdr.index(c) for c in ("name", "exact_name", "module", "kind", "merged_chunk"))
        g.write("name\texact_name\tmodule\tkind\tin_toolchain\tchunk\n")
        for line in f:
            p = line.rstrip("\n").split("\t")
            ch = p[ich]
            tc = p[imod].split(".")[0] in TC_ROOTS
            if tc:
                ntc += 1
                if ch != "-":
                    tcchunks.add(ch)
            else:
                assert ch != "-", p
                keep.add(ch)
            g.write("\t".join([p[iname], p[iex], p[imod], p[ikind], "1" if tc else "0", "" if tc else ch]) + "\n")
            ndecl += 1
    nedge = 0
    with gzip.open(os.path.join(src, "chunk_edges.tsv.gz"), "rt", encoding="utf-8", newline="") as f, \
            gzip.open(os.path.join(dst, "chunk_edges.tsv.gz"), "wt", encoding="utf-8", newline="", compresslevel=1) as g:
        f.readline()
        g.write("chunk\timports_chunk\n")
        for line in f:
            a, b = line.rstrip("\n").split("\t")
            if a in keep and b in keep:
                g.write(f"{a}\t{b}\n")
                nedge += 1
    return {"declarations": ndecl, "toolchain_declarations": ntc, "chunks": len(keep), "edges": nedge}


@unittest.skipUnless(os.path.exists(os.path.join(REAL, "assignment.tsv.gz")) and not os.environ.get("MREG_TEST_SKIP_REAL"),
                     "real 4.34.1 tables absent or MREG_TEST_SKIP_REAL set")
class RealTables(unittest.TestCase):
    """The real Lean 4.34.1 tables (assignment.tsv.gz, chunk_edges.tsv.gz), their column names mapped to the final layout HERE (not in
    the client): resolution time and cones against a closure computed separately from the ORIGINAL old tables (plain dicts, with
    the test's own toolchain rule: the old edges join merged chunks and include toolchain chunks)."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.mkdtemp(prefix="mreg-real-")
        t = time.time()
        cls.conv = convert_old_tables(REAL, cls.tmp)
        cls.convert_seconds = time.time() - t
        t = time.time()
        cls.meta = M.build_lookup(cls.tmp)
        cls.cold = time.time() - t
        # independent model, from the ORIGINAL tables
        cls.adj, cls.rows = {}, []
        with gzip.open(os.path.join(REAL, "assignment.tsv.gz"), "rt", encoding="utf-8") as f:
            hdr = f.readline().rstrip("\n").split("\t")
            iname, imod, ich = hdr.index("name"), hdr.index("module"), hdr.index("merged_chunk")
            cls.tcchunk = set()
            for line in f:
                p = line.rstrip("\n").split("\t")
                if p[ich] != "-":
                    cls.rows.append((p[iname], p[imod], p[ich]))
                    if p[imod].split(".")[0] in TC_ROOTS:
                        cls.tcchunk.add(p[ich])
        intern = {}
        with gzip.open(os.path.join(REAL, "chunk_edges.tsv.gz"), "rt", encoding="utf-8") as f:
            f.readline()
            for line in f:
                a, b = line.rstrip("\n").split("\t")
                a = intern.setdefault(a, a)
                b = intern.setdefault(b, b)
                cls.adj.setdefault(a, []).append(b)

    @classmethod
    def tearDownClass(cls):
        cls.adj.clear()
        cls.rows.clear()
        cls.tcchunk.clear()
        shutil.rmtree(cls.tmp, True)

    def closure(self, start):
        seen, stack = set(), [start]
        while stack:
            c = stack.pop()
            if c in seen or c in self.tcchunk:
                continue
            seen.add(c)
            stack.extend(self.adj.get(c, ()))
        return sorted(seen)

    def test_counts(self):
        self.assertEqual(self.meta["declarations"], 783435)
        self.assertEqual(self.meta["chunks"], 373080)      # 447,233 less the 74,153 toolchain chunks (NAMED_IMPORT.md)
        for k in ("declarations", "toolchain_declarations", "chunks", "edges"):
            self.assertEqual(self.meta[k], self.conv[k], k)

    def test_200_random_cones_equal_independent_closure_and_stats(self):
        rnd = random.Random(20261110)
        cand = [r for r in self.rows if r[1].split(".")[0] not in TC_ROOTS]
        sample = rnd.sample(cand, 200)
        lk = M.Lookup(self.tmp)
        sizes, warm = [], []
        try:
            for name, mod, ch in sample:
                t = time.time()
                rows = [r for r in lk.find(name) if r["chunk"] == ch]
                self.assertTrue(rows, name)
                cone = lk.cone([rows[0]["chunk_index"]])
                warm.append(time.time() - t)
                got = [lk.chunk_hex(i) for i in cone]
                self.assertEqual(got, self.closure(ch), name)
                sizes.append(len(got))
        finally:
            lk.close()
        s = sorted(sizes)
        stats = {"n": 200, "seed": 20261110, "cone_chunks": {"median": s[100], "p90": s[180], "max": s[-1], "min": s[0]},
                 "cold_requests_median": 5 + s[100], "cold_requests_p90": 5 + s[180], "cold_requests_max": 5 + s[-1],
                 "share_over_default_budget_2000": round(sum(1 for x in sizes if x > 2000) / len(sizes), 3),
                 "lookup_build_seconds_cold": round(self.cold, 1), "convert_seconds": round(self.convert_seconds, 1),
                 "warm_per_declaration_seconds_median": round(sorted(warm)[100], 4), "tables_carry_sizes": False,
                 "columns": "old 4.34.1 columns mapped to the final layout in the test"}
        print("\nREAL TABLES", json.dumps(stats))
        try:
            json.dump(stats, open(os.path.join(EVID, "real-tables-test-stats.json"), "w"), indent=1)
        except OSError:
            pass
        self.assertGreater(s[100], 1)

    def test_warm_resolution_time(self):
        t = time.time()
        lk = M.Lookup(self.tmp)
        r = lk.find("Nat.add_comm")
        c = lk.cone([r[0]["chunk_index"]]) if r and r[0]["chunk_index"] is not None else []
        lk.close()
        self.assertLess(time.time() - t, 5)


if __name__ == "__main__":
    unittest.main(verbosity=1)
