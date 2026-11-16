"""Shared format and reader of the static mathregistry tool-server index (stdlib only).

Written by build_index.py, read by server.py. Every file is JSON or JSON lines, UTF-8, so a function (or an object store
plus a function) can read it without a database. The reader counts files and bytes read per call so the bound on reads is
measured, not claimed.

Layout under the index root:

    manifest.json                    parameters, totals, builds, duplicate statements, warnings
    decl/<k hex digits>.jsonl        declaration records, sharded by sha256(declaration_id)
    stmt/<k hex digits>.jsonl        exact statement index, sharded by statement sha256: {sha, stmt, ids}
    th/<k hex digits>.jsonl          64-bit type-hash candidate index, sharded by the hash: {th, ids}
    pkg/<k hex digits>.json          package records (versions, builds, trust), sharded by sha256(package id)
    cone/<k hex digits>.jsonl        precomputed cones (delta-encoded node numbers), sharded by sha256(declaration_id)
    rev/<chunk>.jsonl                reverse edges ("used by"), chunk = node number // rev_chunk
    nodes/<chunk>.jsonl              node table: [declaration_id, kind, th, helper], chunk = node number // node_chunk
    ext/<chunk>.jsonl                external references: [name, module], chunk = ext number // node_chunk

A declaration id is `<package id>@<version>#<declaration name>`. One build per (package id, version) is indexed.
"""
import hashlib
import json
import os

SCHEMA = "mreg-mcp-index/1"
CONTRACT_VERSION = "mreg-checker-contract/1.1.0"


def sha256_hex(s):
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def canon(o):
    return json.dumps(o, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def shard_name(prefix_hex, k):
    return prefix_hex[:k] if k > 0 else "_"


def delta_enc(sorted_ints):
    out, prev = [], 0
    for x in sorted_ints:
        out.append(x - prev)
        prev = x
    return out


def delta_dec(deltas):
    out, acc = [], 0
    for d in deltas:
        acc += d
        out.append(acc)
    return out


def split_decl_id(did):
    """'<pkg>@<version>#<name>' -> (pkg, version, name) or None. The name is everything after the first '#'."""
    if not isinstance(did, str) or "#" not in did:
        return None
    head, name = did.split("#", 1)
    if "@" not in head or not name:
        return None
    pkg, ver = head.rsplit("@", 1)
    if not pkg or not ver:
        return None
    return pkg, ver, name


class DirReader:
    """Reads index files from a directory and counts what it reads. Replace with an object-store reader in a deployment."""

    def __init__(self, root):
        self.root = root
        self.files = 0
        self.bytes = 0
        self.log = []

    def reset(self):
        self.files = 0
        self.bytes = 0
        self.log = []

    def read(self, rel):
        p = os.path.join(self.root, rel)
        try:
            with open(p, "rb") as f:
                b = f.read()
        except FileNotFoundError:
            return None
        self.files += 1
        self.bytes += len(b)
        self.log.append((rel, len(b)))
        return b


class MemoReader:
    """Per-request wrapper: a file read twice inside one request is fetched once."""

    def __init__(self, base):
        self.base, self.memo = base, {}

    def read(self, rel):
        if rel not in self.memo:
            self.memo[rel] = self.base.read(rel)
        return self.memo[rel]


class Index:
    """Lookups over the static files. Each method states how many files it reads."""

    def fork(self):
        """A copy whose reads are memoised for the life of one request (same manifest, no extra reads)."""
        c = Index.__new__(Index)
        c.r, c.manifest, c.p = MemoReader(self.r), self.manifest, self.p
        return c

    def __init__(self, reader):
        self.r = reader
        b = reader.read("manifest.json")
        if b is None:
            raise FileNotFoundError("manifest.json missing: not an index directory")
        self.manifest = json.loads(b)
        if self.manifest.get("schema") != SCHEMA:
            raise ValueError("unknown index schema %r" % self.manifest.get("schema"))
        self.p = self.manifest["params"]

    # -- shard helpers ------------------------------------------------------------------------------------------
    def _jsonl_shard(self, family, key_hex, k):
        b = self.r.read("%s/%s.jsonl" % (family, shard_name(key_hex, k)))
        if b is None:
            return []
        return [json.loads(l) for l in b.decode("utf-8").split("\n") if l]

    # -- lookups ------------------------------------------------------------------------------------------------
    def decl(self, did):
        """1 file."""
        for rec in self._jsonl_shard("decl", sha256_hex(did), self.p["decl_k"]):
            if rec["id"] == did:
                return rec
        return None

    def package(self, pkg_id):
        """1 file."""
        b = self.r.read("pkg/%s.json" % shard_name(sha256_hex(pkg_id), self.p["pkg_k"]))
        if b is None:
            return None
        return json.loads(b).get(pkg_id)

    def stmt(self, sha):
        """1 file. Returns the stored row {sha, stmt, ids} or None."""
        for row in self._jsonl_shard("stmt", sha, self.p["stmt_k"]):
            if row["sha"] == sha:
                return row
        return None

    def th_candidates(self, th):
        """1 file. Ids whose 64-bit type hash equals th: CANDIDATES, to be confirmed against statement text."""
        for row in self._jsonl_shard("th", th, self.p["th_k"]):
            if row["th"] == th:
                return row["ids"]
        return []

    def cone(self, did):
        """1 file. Returns the raw cone record or None."""
        for rec in self._jsonl_shard("cone", sha256_hex(did), self.p["cone_k"]):
            if rec["id"] == did:
                return rec
        return None

    def rev(self, n):
        """1 file. Returns {n, c, top, by(delta)} or None."""
        ch = n // self.p["rev_chunk"]
        b = self.r.read("rev/%d.jsonl" % ch)
        if b is None:
            return None
        for l in b.decode("utf-8").split("\n"):
            if l:
                rec = json.loads(l)
                if rec["n"] == n:
                    return rec
        return None

    def nodes(self, ns):
        """One file per distinct chunk touched. Returns {n: [declaration_id, kind, th, helper]}."""
        out, by_chunk = {}, {}
        for n in ns:
            by_chunk.setdefault(n // self.p["node_chunk"], []).append(n)
        for ch, want in sorted(by_chunk.items()):
            b = self.r.read("nodes/%d.jsonl" % ch)
            rows = [json.loads(l) for l in b.decode("utf-8").split("\n") if l]
            base = ch * self.p["node_chunk"]
            for n in want:
                out[n] = rows[n - base]
        return out

    def externals(self, xs):
        """One file per distinct chunk touched. Returns {x: [name, module]}."""
        out, by_chunk = {}, {}
        for x in xs:
            by_chunk.setdefault(x // self.p["node_chunk"], []).append(x)
        for ch, want in sorted(by_chunk.items()):
            b = self.r.read("ext/%d.jsonl" % ch)
            rows = [json.loads(l) for l in b.decode("utf-8").split("\n") if l]
            base = ch * self.p["node_chunk"]
            for x in want:
                out[x] = rows[x - base]
        return out

    # -- exact statement search with confirmation ---------------------------------------------------------------
    def present(self, statement_text, th64=None):
        """Is this statement already in the index? Returns {"by_sha": [ids], "by_th64_confirmed": [ids],
        "by_th64_unconfirmed": [ids]}.

        The SHA-256 of the text is a collision-resistant key; the stored text is still compared. The 64-bit type hash is
        only a candidate key: each candidate's stored statement text is fetched and compared with statement_text before
        it is reported as confirmed; candidates whose text differs are reported as unconfirmed (hash collisions or
        statements that print differently)."""
        out = {"by_sha": [], "by_th64_confirmed": [], "by_th64_unconfirmed": []}
        sha = sha256_hex(statement_text)
        row = self.stmt(sha)
        if row is not None and row["stmt"] == statement_text:
            out["by_sha"] = list(row["ids"])
        if th64:
            for did in self.th_candidates(th64):
                if did in out["by_sha"]:
                    continue
                rec = self.decl(did)
                if rec is not None and rec.get("stmt") == statement_text:
                    out["by_th64_confirmed"].append(did)
                else:
                    out["by_th64_unconfirmed"].append(did)
        return out
