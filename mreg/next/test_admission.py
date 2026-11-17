#!/usr/bin/env python3
"""Tests of the admission patch for mreg (0.5.0): strict audit before install, --allow-unverified, four statuses, chunks refused.

    python -I test_admission.py

Stdlib only. No network (file:/// registries built here), no AWS, no Lean (--no-lake-check, or lake_check replaced), a temporary home,
store and project for every test. Loads mreg.py from THIS folder (the copy under test), never mreg/next/mreg.py. The registry builders
below are copied from test_next.py (build_package, make_project) and test_named_import.py (Mirror, the synthetic declaration store);
check_signature and chain_problems are replaced where a registry key or a hash chain would be needed.
"""
import contextlib, gzip, hashlib, importlib.util, io, json, os, pathlib, random, shutil, subprocess, sys, tarfile, tempfile, unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("mreg_admission_under_test", os.path.join(HERE, "mreg.py"))
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
PLAT = M.platform_triple()

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




# ==================================================================================== admission: signing and gates on a local registry
# A real signature needs the registry's key. These tests keep the registry's files real (manifest, reports, log entry, a signature
# file) and replace only the two functions that need keys or the whole hash chain: check_signature and chain_problems. Everything
# else, the strict audit included, is the client's own code.

GATES_OK = {f"G{i}": "pass" for i in range(1, 11)}


def finalize(root, p, gates, labels, signed=True, log_n=1):
    """Make the build written by build_package carry what a promoted build carries: reports/verify.json with the gates, the manifest
    that lists it, the package document's labels/signed flag, a log entry, and (when signed) a signature file."""
    pid, ver, bk = p["id"], p["version"], p["man"]["build_key"]
    base = pathlib.Path(root, "v1", "blobs", *pid.split("/"), "-", ver, bk)
    man = json.loads((base / "manifest.json").read_text())
    verify = json.dumps({"gates": {g: {"status": s} for g, s in gates.items()}}).encode()
    (base / "reports" / "verify.json").write_bytes(verify)
    man["reports"]["reports/verify.json"] = sha(verify)
    man["gates"] = {g: {"status": s} for g, s in gates.items()}
    mbytes = json.dumps(man, indent=1).encode()
    (base / "manifest.json").write_bytes(mbytes)
    msha = sha(mbytes)
    sigraw = b'{"synthetic": true}'
    if signed:
        (base / "manifest.json.sig").write_bytes(sigraw)
    dp = pathlib.Path(root, "v1", "index", *pid.split("/"))
    dp = pathlib.Path(str(dp) + ".json")
    doc = json.loads(dp.read_text(encoding="utf-8"))
    ent = doc["versions"][ver]["builds"][0]
    ent.update({"manifest": {"sha256": msha, "bytes": len(mbytes)}, "signed": signed, "labels": list(labels), "gates": dict(gates),
                "log_n": log_n})
    dp.write_text(json.dumps(doc), encoding="utf-8")
    entry = {"id": pid, "version": ver, "build_key": bk, "manifest_sha256": msha, "type": "promote"}
    if signed:
        entry.update({"sig_sha256": sha(sigraw), "labels": list(labels)})
    lp = pathlib.Path(root, "v1", "log", f"{log_n}.json")
    lp.parent.mkdir(parents=True, exist_ok=True)
    lp.write_text(json.dumps(entry), encoding="utf-8")
    return msha


def one_registry(root, gates=None, labels=("clean",), signed=True):
    """A registry with the one package acme/demo (and the train), finalized as asked. Returns the package record."""
    pk = build_package(root, "acme/demo", "Demo", "a" * 40, demo_decls())
    pk_idx = pathlib.Path(root, "v1", "index", "trains")
    pk_idx.mkdir(parents=True, exist_ok=True)
    (pk_idx / (TRAIN + ".json")).write_text(json.dumps({"train": TRAIN, "toolchain": TOOLCHAIN, "state": "open", "mathlib": {"rev": "0" * 40},
                                                         "pins": {}, "module_roots": {}, "packages": {
        pk["id"]: {"lake_name": "Demo", "commit": pk["commit"], "version": pk["version"], "modules": 4, "module_roots": ["Demo"],
                   "git": "https://github.com/acme/demo"}}}))
    (pk_idx.parent / "trains.json").write_text(json.dumps({"trains": [{"train": TRAIN}]}))
    finalize(root, pk, GATES_OK if gates is None else gates, labels, signed)
    return pk


class Adm(unittest.TestCase):
    """Runs the client in this process against a file:/// registry, with check_signature and chain_problems replaced (see above)."""

    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="mra")
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.reg = os.path.join(self.tmp, "reg")
        self.home = os.path.join(self.tmp, "home")
        os.makedirs(self.home)
        self.labels = ["clean"]

    def registry(self, **kw):
        self.labels = list(kw.get("labels", ("clean",)))
        self.pk = one_registry(self.reg, **kw)
        return self.pk

    def project(self, name="proj", **kw):
        d = os.path.join(self.tmp, name)
        make_project(d, **kw)
        return d

    def env(self):
        e = {"MREG_REGISTRY": pathlib.Path(self.reg).as_uri(), "MREG_KEYS": os.path.join(self.tmp, "pins.json"), "HOME": self.home,
             "USERPROFILE": self.home, "MREG_STORE": os.path.join(self.tmp, "store"), "MREG_BACKOFF": "0", "MREG_RETRIES": "1"}
        return e

    def mreg(self, *args, proj=None):
        """(exit code, stdout, stderr)"""
        sg = {"labels": list(self.labels), "promoted_at": "2026-11-12T00:00:00Z"}
        out, err, code = io.StringIO(), io.StringIO(), 0
        with mock.patch.dict(os.environ, self.env(), clear=False), mock.patch.object(M, "check_signature", lambda *a: (sg, [])), \
                mock.patch.object(M, "chain_problems", lambda *a: []), contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            os.environ.pop("MREG_TOKEN", None)
            try:
                M.main(["-C", proj] + list(args))
            except SystemExit as x:
                code = x.code if isinstance(x.code, int) else (0 if x.code is None else 1)
                if isinstance(x.code, str):
                    err.write(x.code)
        return code, out.getvalue(), err.getvalue()

    def lock(self, proj):
        with open(os.path.join(proj, "mreg.lock"), encoding="utf-8") as f:
            return json.load(f)

    def olean(self, proj, mod, pkg="Demo"):
        return os.path.join(proj, ".lake", "packages", pkg, ".lake", "build", "lib", "lean", *mod.split(".")) + ".olean"

    def nothing_written(self, proj):
        self.assertFalse(os.path.exists(os.path.join(proj, "mreg.lock")))
        self.assertFalse(os.path.exists(os.path.join(proj, ".lake", "mreg-state.json")))
        self.assertFalse(os.path.exists(self.olean(proj, "Demo.A")))
        self.assertFalse(os.path.exists(os.path.join(proj, ".lake", "mreg-cache")))

    ARGS = ("--no-lake-check",)


class AdmissionInstall(Adm):
    def test_a_signed_clean_build_installs_and_the_lock_says_proof_checked(self):
        self.registry()
        proj = self.project()
        code, out, err = self.mreg("install", *self.ARGS, proj=proj)
        self.assertEqual(code, 0, out + err)
        self.assertNotIn("UNVERIFIED", out + err)
        adm = self.lock(proj)["packages"][-1]["admission"]
        self.assertTrue(adm["proof_checked_under_policy"])
        self.assertEqual(adm["policy"], "strict")
        self.assertFalse(adm["allowed_unverified"])
        self.assertEqual(adm["problems"], [])
        self.assertTrue(os.path.exists(self.olean(proj, "Demo.B")))
        self.assertIn("proof_checked_under_policy=yes", out)

    def test_b_an_unsigned_build_is_refused_by_default_and_nothing_is_written(self):
        self.registry(signed=False, labels=())
        proj = self.project()
        for extra in ((), ("--dry-run",), ("--all",), ("--check",)):
            code, out, err = self.mreg("install", *self.ARGS, *extra, proj=proj)
            self.assertEqual(code, M.REFUSED_EXIT, (extra, out, err))
            self.assertEqual(code, 4)
            self.assertIn("acme/demo 1.0.0", err)
            self.assertIn("UNSIGNED", err + out)
            self.assertIn("nothing was installed", err)
            self.assertIn("--allow-unverified", err)
            self.nothing_written(proj)

    def test_c_allow_unverified_installs_with_a_banner_and_the_lock_says_false(self):
        self.registry(signed=False, labels=())
        proj = self.project()
        code, out, err = self.mreg("install", "--allow-unverified", *self.ARGS, proj=proj)
        self.assertEqual(code, 0, out + err)
        self.assertIn("UNVERIFIED: acme/demo 1.0.0 is installed without passing the registry's proof policy", out + err)
        self.assertTrue(os.path.exists(self.olean(proj, "Demo.B")))
        adm = self.lock(proj)["packages"][-1]["admission"]
        self.assertFalse(adm["proof_checked_under_policy"])
        self.assertTrue(adm["allowed_unverified"])
        self.assertTrue(adm["problems"] and len(adm["problems"]) <= 5)
        self.assertIn("proof_checked_under_policy=no", out)
        # the audit keeps showing it as unverified (and fails)
        code, out, err = self.mreg("audit", proj=proj)
        self.assertEqual(code, 1)
        self.assertIn("UNVERIFIED: mreg.lock records this build", out)
        self.assertIn("FAIL", out)

    def test_d_a_signed_build_failing_the_gates_or_the_label_is_refused(self):
        for gates, labels, word in ((dict(GATES_OK, G7="not run"), ["clean"], "G7"), (dict(GATES_OK, G6="fail"), ["clean"], "G6"),
                                    (GATES_OK, ["partial"], "label partial")):
            shutil.rmtree(self.reg, ignore_errors=True)
            self.registry(gates=gates, labels=labels)
            proj = self.project(name="p_" + word.replace(" ", "_"))
            code, out, err = self.mreg("install", *self.ARGS, proj=proj)
            self.assertEqual(code, 4, (word, out, err))
            self.assertIn(word, err)
            self.nothing_written(proj)
            code, out, err = self.mreg("install", "--allow-unverified", *self.ARGS, proj=proj)
            self.assertEqual(code, 0, (word, out, err))
            self.assertFalse(self.lock(proj)["packages"][-1]["admission"]["proof_checked_under_policy"])

    def test_the_imported_label_is_admitted_with_g1_not_run(self):
        self.registry(gates=dict(GATES_OK, G1="not run"), labels=["imported"])
        proj = self.project()
        code, out, err = self.mreg("install", *self.ARGS, proj=proj)
        self.assertEqual(code, 0, out + err)
        self.assertTrue(self.lock(proj)["packages"][-1]["admission"]["proof_checked_under_policy"])


class AdmissionViews(Adm):
    def add_views(self, block):
        p = self.pk
        base = pathlib.Path(self.reg, "v1", "blobs", *p["id"].split("/"), "-", p["version"], p["man"]["build_key"])
        v = json.loads((base / "reports" / "verify.json").read_text())
        if block is not None:
            v["views"] = block
        vb = json.dumps(v).encode()
        (base / "reports" / "verify.json").write_bytes(vb)
        man = json.loads((base / "manifest.json").read_text())
        man["reports"]["reports/verify.json"] = sha(vb)
        mb = json.dumps(man, indent=1).encode()
        (base / "manifest.json").write_bytes(mb)
        dp = pathlib.Path(self.reg, "v1", "index", "acme", "demo.json")
        doc = json.loads(dp.read_text())
        doc["versions"][p["version"]]["builds"][0]["manifest"] = {"sha256": sha(mb), "bytes": len(mb)}
        dp.write_text(json.dumps(doc))
        lp = pathlib.Path(self.reg, "v1", "log", "1.json")
        e = json.loads(lp.read_text()); e["manifest_sha256"] = sha(mb); lp.write_text(json.dumps(e))

    def test_views_required_when_the_constant_is_true(self):
        self.registry()
        proj = self.project()
        with mock.patch.object(M, "ADMISSION_REQUIRES_VIEWS", True):
            code, out, err = self.mreg("install", *self.ARGS, proj=proj)
            self.assertEqual(code, 4, out + err)
            self.assertIn("views check (contract 1.2.0) not passed", err)
            self.nothing_written(proj)
            self.add_views({"status": "fail"})
            self.assertEqual(self.mreg("install", *self.ARGS, proj=proj)[0], 4)
            self.add_views({"status": "pass"})
            code, out, err = self.mreg("install", *self.ARGS, proj=proj)
            self.assertEqual(code, 0, out + err)
            self.assertTrue(self.lock(proj)["packages"][-1]["admission"]["proof_checked_under_policy"])

    def test_views_not_required_by_default(self):
        self.assertFalse(M.ADMISSION_REQUIRES_VIEWS)
        self.registry()
        self.assertEqual(self.mreg("install", *self.ARGS, proj=self.project())[0], 0)

    def test_views_required_by_flag_and_env_on_install_ci_and_audit(self):
        self.registry()
        proj = self.project()
        code, out, err = self.mreg("install", "--require-views", *self.ARGS, proj=proj)
        self.assertEqual(code, 4, out + err)
        self.assertIn("views check (contract 1.2.0) not passed", err)
        self.nothing_written(proj)

        with mock.patch.dict(os.environ, {"MREG_REQUIRE_VIEWS": "1"}):
            code, out, err = self.mreg("install", *self.ARGS, proj=proj)
            self.assertEqual(code, 4, out + err)
            code, out, err = self.mreg("audit", "acme/demo@1.0.0", proj=proj)
            self.assertEqual(code, 1, out + err)
            self.assertIn("views check (contract 1.2.0) not passed", out)

        code, out, err = self.mreg("audit", "--require-views", "acme/demo@1.0.0", proj=proj)
        self.assertEqual(code, 1, out + err)
        self.assertIn("views check (contract 1.2.0) not passed", out)

        self.assertEqual(self.mreg("install", *self.ARGS, proj=proj)[0], 0)
        self.assertEqual(self.mreg("ci", "--require-views", *self.ARGS, proj=proj)[0], 4)

        self.add_views({"status": "pass"})
        proj2 = self.project(name="proj_views_ok")
        self.assertEqual(self.mreg("audit", "--require-views", "acme/demo@1.0.0", proj=proj2)[0], 0)
        self.assertEqual(self.mreg("install", "--require-views", *self.ARGS, proj=proj2)[0], 0)
        self.assertEqual(self.mreg("ci", "--require-views", *self.ARGS, proj=proj2)[0], 0)


class AdmissionCi(Adm):
    def test_e_ci_on_a_lock_with_an_unverified_package_is_refused_without_the_flag(self):
        self.registry(signed=False, labels=())
        proj = self.project()
        self.assertEqual(self.mreg("install", "--allow-unverified", *self.ARGS, proj=proj)[0], 0)
        os.remove(self.olean(proj, "Demo.A"))
        os.remove(os.path.join(proj, ".lake", "mreg-state.json"))
        code, out, err = self.mreg("ci", *self.ARGS, proj=proj)
        self.assertEqual(code, 4, out + err)
        self.assertIn("nothing was installed", err)
        self.assertFalse(os.path.exists(self.olean(proj, "Demo.A")), "ci wrote nothing")
        code, out, err = self.mreg("ci", "--allow-unverified", *self.ARGS, proj=proj)
        self.assertEqual(code, 0, out + err)
        self.assertIn("UNVERIFIED", out + err)
        self.assertTrue(os.path.exists(self.olean(proj, "Demo.A")))
        self.assertTrue(self.lock(proj)["packages"][-1]["admission"]["allowed_unverified"])

    def test_ci_runs_admission_again_whatever_the_lock_claims(self):
        self.registry(signed=False, labels=())
        proj = self.project()
        self.assertEqual(self.mreg("install", "--allow-unverified", *self.ARGS, proj=proj)[0], 0)
        lock = self.lock(proj)
        lock["packages"][-1]["admission"] = {"policy": "strict", "proof_checked_under_policy": True, "problems": [], "allowed_unverified": False}
        with open(os.path.join(proj, "mreg.lock"), "w") as f:
            json.dump(lock, f)
        code, out, err = self.mreg("ci", *self.ARGS, proj=proj)
        self.assertEqual(code, 4, "a lock that claims to be checked does not skip the audit")

    def test_f_an_old_lock_without_the_admission_field_is_read_and_admission_re_run(self):
        self.registry()
        proj = self.project()
        self.assertEqual(self.mreg("install", *self.ARGS, proj=proj)[0], 0)
        lock = self.lock(proj)
        for e in lock["packages"]:
            e.pop("admission", None)
        self.assertEqual(lock["schema"], "mreg-lock/0")
        with open(os.path.join(proj, "mreg.lock"), "w") as f:
            json.dump(lock, f)
        os.remove(self.olean(proj, "Demo.A"))
        os.remove(os.path.join(proj, ".lake", "mreg-state.json"))
        code, out, err = self.mreg("ci", *self.ARGS, proj=proj)
        self.assertEqual(code, 0, out + err)
        self.assertTrue(os.path.exists(self.olean(proj, "Demo.A")))
        lock = self.lock(proj)
        self.assertEqual(lock["schema"], "mreg-lock/0", "the schema names are unchanged; the field is additive")
        self.assertTrue(lock["packages"][-1]["admission"]["proof_checked_under_policy"], "admission was run again and written")
        # the same old lock, with the build now failing the policy (registry changed under it): refused
        shutil.rmtree(self.reg)
        self.registry(gates=dict(GATES_OK, G7="not run"))
        lock = self.lock(proj)
        for e in lock["packages"]:
            e.pop("admission", None)
            if e.get("manifest_sha256"):
                e["manifest_sha256"] = self.locked_msha()
        with open(os.path.join(proj, "mreg.lock"), "w") as f:
            json.dump(lock, f)
        code, out, err = self.mreg("ci", *self.ARGS, proj=proj)
        self.assertEqual(code, 4, out + err)

    def locked_msha(self):
        p = self.pk
        base = pathlib.Path(self.reg, "v1", "blobs", *p["id"].split("/"), "-", p["version"], p["man"]["build_key"])
        return sha((base / "manifest.json").read_bytes())


class AdmissionStatuses(Adm):
    def test_h_the_four_statuses_are_distinct_in_the_lock(self):
        self.registry()
        proj = self.project()
        code, out, err = self.mreg("install", *self.ARGS, proj=proj)     # Lake did not run
        self.assertEqual(code, 0, out + err)
        adm = self.lock(proj)["packages"][-1]["admission"]
        self.assertEqual(adm["downloaded"], True)
        self.assertEqual(adm["hash_matched"], True)
        self.assertEqual(adm["compatible"], "not checked")
        self.assertEqual(adm["proof_checked_under_policy"], True)
        self.assertEqual(len({"downloaded", "hash_matched", "compatible", "proof_checked_under_policy"} & set(adm)), 4)
        self.assertIn("compatible=not checked", out)
        # Lake "passed" / "failed" are recorded as such, and are not the proof status
        for rc, word in ((0, "passed"), (1, "failed")):
            proj2 = self.project(name=f"lake{rc}")
            with mock.patch.object(M, "lake_check", lambda *a, _rc=rc, **k: _rc):
                code, out, err = self.mreg("install", "--check", proj=proj2)
            self.assertEqual(code, rc, out + err)
            adm = self.lock(proj2)["packages"][-1]["admission"]
            self.assertEqual(adm["compatible"], word)
            self.assertTrue(adm["proof_checked_under_policy"])
            self.assertIn(f"compatible={word}", out)

    def test_hash_matched_is_not_proof_checked(self):
        """An unsigned build that was downloaded and hash-matched is still not proof checked: the statuses do not imply each other."""
        self.registry(signed=False, labels=())
        proj = self.project()
        code, out, err = self.mreg("install", "--allow-unverified", *self.ARGS, proj=proj)
        adm = self.lock(proj)["packages"][-1]["admission"]
        self.assertEqual((adm["downloaded"], adm["hash_matched"], adm["proof_checked_under_policy"]), (True, True, False))

    def test_json_document_carries_the_admission(self):
        self.registry()
        proj = self.project()
        code, out, err = self.mreg("install", "--json", *self.ARGS, proj=proj)
        self.assertEqual(code, 0, out + err)
        js = json.loads(out)
        self.assertTrue(js["admission"]["acme/demo"]["proof_checked_under_policy"])


class AdmissionChunks(Adm):
    """Declaration chunks: a synthetic decl store (the Mirror of test_named_import) next to the registry."""
    ENTRY = f"{MATHLIB}#Mathlib.n60_0"

    def setUp(self):
        super().setUp()
        self.proj = os.path.join(self.tmp, "cproj")
        os.makedirs(self.proj)
        open(os.path.join(self.proj, "lean-toolchain"), "w").write(TOOLCHAIN + "\n")
        self.m = Mirror(self.reg)

    def test_g_named_declaration_install_is_refused_by_default(self):
        for cmd in ("add", "install"):
            code, out, err = self.mreg(cmd, self.ENTRY, "--train", TRAIN, proj=self.proj)
            self.assertEqual(code, 4, (cmd, out, err))
            self.assertIn("declaration chunks are experimental and unverified", out + err)
            self.assertIn("--module-level", out + err)
            self.assertIn("--allow-unverified", out + err)
            self.assertFalse(os.path.exists(os.path.join(self.proj, "mreg-chunks.lock.json")))
            self.assertFalse(os.path.exists(os.path.join(self.proj, ".lake")))
        # resolve (no download) is still allowed
        code, out, err = self.mreg("resolve", self.ENTRY, "--train", TRAIN, proj=self.proj)
        self.assertEqual(code, 0, out + err)

    def test_g_with_the_flag_it_installs_banner_and_the_chunk_lock_records_experimental(self):
        code, out, err = self.mreg("install", self.ENTRY, "--train", TRAIN, "--allow-unverified", proj=self.proj)
        self.assertEqual(code, 0, out + err)
        self.assertIn("UNVERIFIED: declaration chunks", out + err)
        with open(os.path.join(self.proj, "mreg-chunks.lock.json"), encoding="utf-8") as f:
            lk = json.load(f)
        adm = lk["admission"]
        self.assertTrue(adm["experimental_chunks"])
        self.assertFalse(adm["proof_checked_under_policy"])
        self.assertTrue(adm["allowed_unverified"])
        self.assertEqual((adm["downloaded"], adm["hash_matched"], adm["compatible"]), (True, True, "not checked"))
        # ci on the chunk lock: refused without the flag, restored with it
        code, out, err = self.mreg("ci", proj=self.proj)
        self.assertEqual(code, 4, out + err)
        self.assertIn("declaration chunks are experimental and unverified", out + err)
        code, out, err = self.mreg("ci", "--allow-unverified", proj=self.proj)
        self.assertEqual(code, 0, out + err)
        # verify says it is a hash check, not a check of proofs
        code, out, err = self.mreg("verify", proj=self.proj)
        self.assertEqual(code, 0, out + err)
        self.assertIn("not a check of proofs", out)
        self.assertIn("experimental and unverified", out)

    def test_module_level_is_not_refused_for_a_checked_build(self):
        pk = one_registry(os.path.join(self.tmp, "reg2"))
        self.reg = os.path.join(self.tmp, "reg2")
        self.labels = ["clean"]
        proj = self.project()
        code, out, err = self.mreg("install", "acme/demo#Demo.B.t2", "--module-level", *self.ARGS, proj=proj)
        self.assertEqual(code, 0, out + err)
        self.assertTrue(self.lock(proj)["packages"][-1]["admission"]["proof_checked_under_policy"])
        self.assertFalse(os.path.exists(os.path.join(proj, "mreg-chunks.lock.json")))


class VersionAndHelp(unittest.TestCase):
    def test_version_and_flags(self):
        self.assertEqual(M.VERSION, "0.6.6")
        for cmd in ("install", "ci", "add"):
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                with self.assertRaises(SystemExit):
                    M.main([cmd, "--help"])
            self.assertIn("--allow-unverified", out.getvalue(), cmd)
            if cmd in ("install", "ci"):
                self.assertIn("--require-views", out.getvalue(), cmd)
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            with self.assertRaises(SystemExit):
                M.main(["audit", "--help"])
        self.assertIn("--require-views", out.getvalue())

    def test_docstring_says_hash_matched_not_verified(self):
        self.assertNotRegex(M.__doc__, r"(?i)\bverified\b(?! install)")


if __name__ == "__main__":
    unittest.main(verbosity=2)
