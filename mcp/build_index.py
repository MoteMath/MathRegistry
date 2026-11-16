#!/usr/bin/env python3
"""Build the static tool-server index (plan items A.2 exact part, A.3 list form, C.1 reverse edges) from build report files.

    build_index.py build --builds DIR --out DIR [--decl-target 65536] [--cone-target 262144]
    build_index.py check-new --index DIR --build DIR        # which statements of a new build are already present

DIR/builds holds one sub-directory per build. Per build (names as in PHASE2_CONTRACTS.md sections 2 and 9):

    graph.jsonl.zst or graph.jsonl   required: header, module and decl records of mreg-graph/1
    statements.jsonl                 {name, module, kind, statement, sha256} per theorem (G9)
    verify.json                      gate results (section 2); a verify.summary.json is not enough
    axioms.json, sorry.json          optional per-declaration reports (G4, G8)
    docstrings.jsonl                 optional {name, doc}: package-supplied text, served only in an untrusted field
    build.json                       identity and trust metadata that verify.json does not hold: id, version, train,
                                     signed, key_id, manifest_sha256, log_n, labels, plus optional package fields
                                     (lake_name, license, hosted, ownership, dist_tags, description, readme_excerpt)

Cone definitions (both exclude the declaration itself):
  full       every declaration reachable by "uses" edges over the type edges (tu) and the value edges (vu).
  interface  the same walk, except that a theorem reached from the root is listed as an ASSUMPTION and only its
             statement (tu) is followed, never its proof (vu). The root's own edges are all followed. Non-theorems
             reached are followed through tu and vu.
An edge to a constant that no indexed build defines is an EXTERNAL reference [name, defining module]; it is kept in the
cone as an external entry (never dropped) and is a leaf. An edge into another indexed build resolves to that build's node.
"""
import argparse
import json
import os
import shutil
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mregindex as M  # noqa: E402

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NODE_CHUNK = 128
REV_CHUNK = 128
TOP_USERS = 10
BYTE_BITS = [[i for i in range(8) if (b >> i) & 1] for b in range(256)]


# ---------------------------------------------------------------------------------------------------------------------
def read_bytes_maybe_zst(path):
    with open(path, "rb") as f:
        raw = f.read()
    if path.endswith(".zst"):
        try:
            from compression import zstd
            return zstd.decompress(raw), raw
        except ImportError:
            import subprocess
            p = subprocess.run(["zstd", "-dc", path], capture_output=True, check=True)
            return p.stdout, raw
    return raw, raw


def read_jsonl(path):
    out = []
    for l in open(path, encoding="utf-8"):
        l = l.strip()
        if l:
            out.append(json.loads(l))
    return out


def bits_to_list(x):
    """Sorted positions of the set bits of a non-negative int."""
    if x == 0:
        return []
    b = x.to_bytes((x.bit_length() + 7) // 8, "little")
    out = []
    for i, v in enumerate(b):
        if v:
            base = i * 8
            for j in BYTE_BITS[v]:
                out.append(base + j)
    return out


def scc_closure(n, adj, ext_adj, n_ext):
    """For each node x: (bitset of nodes reachable from x including x, bitset of externals reachable from x). Tarjan
    (iterative), then one OR per edge over the condensation."""
    index = [-1] * n
    low = [0] * n
    on = [False] * n
    comp = [-1] * n
    stack, comps, counter = [], [], 0
    for s in range(n):
        if index[s] != -1:
            continue
        work = [(s, 0)]
        index[s] = low[s] = counter
        counter += 1
        stack.append(s)
        on[s] = True
        while work:
            v, i = work[-1]
            if i < len(adj[v]):
                work[-1] = (v, i + 1)
                w = adj[v][i]
                if index[w] == -1:
                    index[w] = low[w] = counter
                    counter += 1
                    stack.append(w)
                    on[w] = True
                    work.append((w, 0))
                elif on[w]:
                    if index[w] < low[v]:
                        low[v] = index[w]
            else:
                work.pop()
                if work:
                    u = work[-1][0]
                    if low[v] < low[u]:
                        low[u] = low[v]
                if low[v] == index[v]:
                    members = []
                    while True:
                        w = stack.pop()
                        on[w] = False
                        comp[w] = len(comps)
                        members.append(w)
                        if w == v:
                            break
                    comps.append(members)
    cn, cx = [0] * len(comps), [0] * len(comps)
    for ci, members in enumerate(comps):  # emitted sinks first, so successors are done
        nb, xb = 0, 0
        for v in members:
            nb |= 1 << v
            for e in ext_adj[v]:
                xb |= 1 << e
            for w in adj[v]:
                cj = comp[w]
                if cj != ci:
                    nb |= cn[cj]
                    xb |= cx[cj]
        cn[ci], cx[ci] = nb, xb
    return [cn[comp[v]] for v in range(n)], [cx[comp[v]] for v in range(n)]


# ---------------------------------------------------------------------------------------------------------------------
def load_build(bdir, warnings):
    gp = None
    for cand in ("graph.jsonl.zst", "graph.jsonl"):
        if os.path.exists(os.path.join(bdir, cand)):
            gp = os.path.join(bdir, cand)
            break
    if gp is None:
        raise SystemExit("%s: no graph.jsonl(.zst)" % bdir)
    data, raw = read_bytes_maybe_zst(gp)
    recs = [json.loads(l) for l in data.decode("utf-8").split("\n") if l.strip()]
    if not recs or recs[0].get("t") != "header" or recs[0].get("schema") != "mreg-graph/1":
        raise SystemExit("%s: first record is not an mreg-graph/1 header" % gp)
    decls = [r for r in recs if r["t"] == "decl"]
    modules = [r for r in recs if r["t"] == "module"]
    verify = json.load(open(os.path.join(bdir, "verify.json"), encoding="utf-8")) if os.path.exists(os.path.join(bdir, "verify.json")) else {}
    meta = json.load(open(os.path.join(bdir, "build.json"), encoding="utf-8")) if os.path.exists(os.path.join(bdir, "build.json")) else {}
    pid = meta.get("id") or verify.get("id")
    ver = meta.get("version") or verify.get("version")
    if not pid or not ver:
        raise SystemExit("%s: no package id/version in build.json or verify.json" % bdir)
    b = {"dir": bdir, "id": pid, "version": ver, "verify": verify, "meta": meta, "decls": decls, "modules": modules,
         "header": recs[0]}
    # coverage of the graph against what verify.json says about it
    g = verify.get("graph") or {}
    chk = {"declared_declarations": g.get("declarations"), "actual_declarations": len(decls),
           "declared_modules": g.get("modules"), "actual_modules": len(modules),
           "declared_sha256": g.get("sha256"), "file_sha256": M.hashlib.sha256(raw).hexdigest(),
           "file": os.path.basename(gp)}
    chk["sha256_matches"] = (g.get("sha256") == chk["file_sha256"]) if g.get("sha256") else None
    if g.get("declarations") is not None and g["declarations"] != len(decls):
        warnings.append("%s@%s: verify.json declares %s graph declarations, file has %d" % (pid, ver, g["declarations"], len(decls)))
    if g.get("sha256") and not chk["sha256_matches"]:
        warnings.append("%s@%s: graph file sha256 differs from verify.json graph.sha256 (expected if the file was decompressed or "
                        "recompressed, or verify.json is from another run)" % (pid, ver))
    b["graph_check"] = chk
    # statements
    stm = {}
    sp = os.path.join(bdir, "statements.jsonl")
    if os.path.exists(sp):
        for r in read_jsonl(sp):
            if M.sha256_hex(r["statement"]) != r["sha256"]:
                raise SystemExit("%s: statements.jsonl row %r: sha256 does not match the statement text" % (bdir, r["name"]))
            stm[r["name"]] = r
        g9 = (verify.get("gates") or {}).get("G9") or {}
        if g9.get("theorems") is not None and g9["theorems"] != len(stm):
            warnings.append("%s@%s: G9 says %s theorems, statements.jsonl has %d" % (pid, ver, g9["theorems"], len(stm)))
    else:
        warnings.append("%s@%s: no statements.jsonl; no statement text or exact-index entries" % (pid, ver))
    b["statements"] = stm
    names = {d["name"] for d in decls}
    b["orphan_statements"] = sorted(n for n in stm if n not in names)
    if b["orphan_statements"]:
        warnings.append("%s@%s: %d statements name no graph declaration" % (pid, ver, len(b["orphan_statements"])))
    # axioms
    b["axioms"] = None
    ap = os.path.join(bdir, "axioms.json")
    if os.path.exists(ap):
        a = json.load(open(ap, encoding="utf-8"))
        sets = a["axiom_sets"]
        b["axioms"] = {row[0]: sets[row[3]] for row in a["rows"]}
    # sorry
    gates = verify.get("gates") or {}
    g8 = gates.get("G8") or {}
    b["sorry"] = None
    sop = os.path.join(bdir, "sorry.json")
    if os.path.exists(sop):
        b["sorry"] = {r["name"] for r in json.load(open(sop, encoding="utf-8"))["declarations"]}
        b["sorry_known"] = True
    elif g8.get("status") in ("pass", "flag") and g8.get("declarations_with_sorry") == len(g8.get("first", [])):
        b["sorry"] = set(g8.get("first", []))
        b["sorry_known"] = True
    else:
        b["sorry"] = set(g8.get("first", []))
        b["sorry_known"] = False
    b["axioms_known"] = b["axioms"] is not None
    dp = os.path.join(bdir, "docstrings.jsonl")
    b["docs"] = {r["name"]: r["doc"] for r in read_jsonl(dp)} if os.path.exists(dp) else {}
    return b


def build_trust(b):
    v, meta = b["verify"], b["meta"]
    gates = {}
    for k in ["G%d" % i for i in range(1, 11)]:
        gates[k] = ((v.get("gates") or {}).get(k) or {}).get("status", "not run")
        if gates[k] not in ("pass", "flag", "fail", "not run"):
            gates[k] = "not run"
    g4 = (v.get("gates") or {}).get("G4") or {}
    label = None
    if meta.get("labels"):
        label = meta["labels"][0]
    if label is None:
        st = set(gates.values())
        label = "unverified" if "fail" in st else "flagged" if "flag" in st else "clean" if st == {"pass"} else "partial"
    g8 = (v.get("gates") or {}).get("G8") or {}
    return {"contract_version": M.CONTRACT_VERSION, "label": label, "gates": gates,
            "axioms": sorted(g4.get("extra_axioms", [])), "uses_sorry": bool(g8.get("declarations_with_sorry", 0)),
            "signed": bool(meta.get("signed", False)), "key_id": meta.get("key_id"),
            "manifest_sha256": meta.get("manifest_sha256"), "log_n": meta.get("log_n")}


# ---------------------------------------------------------------------------------------------------------------------
class Family:
    """Collects (shard key hex, key for ordering, line) and writes shards with the smallest k whose largest file fits."""

    def __init__(self, name, ext="jsonl"):
        self.name, self.ext, self.items = name, ext, []

    def add(self, key_hex, line):
        self.items.append((key_hex, line))

    def write(self, root, target, kmax=4):
        k = 0
        while k < kmax:
            sizes = {}
            for kh, line in self.items:
                s = M.shard_name(kh, k)
                sizes[s] = sizes.get(s, 0) + len(line.encode("utf-8")) + 1
            if not sizes or max(sizes.values()) <= target:
                break
            k += 1
        shards = {}
        for kh, line in self.items:
            shards.setdefault(M.shard_name(kh, k), []).append((kh, line))
        d = os.path.join(root, self.name)
        os.makedirs(d, exist_ok=True)
        total, mx = 0, 0
        for s, lst in shards.items():
            lst.sort(key=lambda t: t[0])
            body = ("\n".join(l for _, l in lst) + "\n").encode("utf-8")
            with open(os.path.join(d, "%s.%s" % (s, self.ext)), "wb") as f:
                f.write(body)
            total += len(body)
            mx = max(mx, len(body))
        return k, {"files": len(shards), "bytes": total, "max_file_bytes": mx, "records": len(self.items)}


def write_chunks(root, name, rows, chunk):
    d = os.path.join(root, name)
    os.makedirs(d, exist_ok=True)
    total, mx, files = 0, 0, 0
    for c in range(0, len(rows), chunk):
        body = ("\n".join(M.canon(r) for r in rows[c:c + chunk]) + "\n").encode("utf-8")
        with open(os.path.join(d, "%d.jsonl" % (c // chunk)), "wb") as f:
            f.write(body)
        total += len(body)
        mx = max(mx, len(body))
        files += 1
    return {"files": files, "bytes": total, "max_file_bytes": mx, "records": len(rows)}


def build(builds_dir, out_dir, decl_target=16384, cone_target=131072):
    t0 = time.time()
    warnings = []
    bdirs = sorted(os.path.join(builds_dir, d) for d in os.listdir(builds_dir) if os.path.isdir(os.path.join(builds_dir, d)))
    builds = [load_build(d, warnings) for d in bdirs]
    seen = set()
    for b in builds:
        key = (b["id"], b["version"])
        if key in seen:
            raise SystemExit("two builds for %s@%s: one build per (package, version) is indexed" % key)
        seen.add(key)
    builds.sort(key=lambda b: (b["id"], b["version"]))

    # number the nodes: by build, then (module, name)
    nodes = []  # dicts
    n2n = {}    # (build index, name) -> node number
    mod2builds = {}
    for bi, b in enumerate(builds):
        b["bi"] = bi
        for m in b["modules"]:
            mod2builds.setdefault(m["module"], []).append(bi)
        for d in sorted(b["decls"], key=lambda d: (d["module"], d["name"])):
            if (bi, d["name"]) in n2n:
                raise SystemExit("%s@%s: declaration %r appears twice in the graph" % (b["id"], b["version"], d["name"]))
            n2n[(bi, d["name"])] = len(nodes)
            nodes.append({"bi": bi, "d": d})
    N = len(nodes)

    # resolve edges; collect externals
    ext_keys = {}
    pending = []  # per node: (tu_int, vu_int, tu_ext_keys, vu_ext_keys)

    def resolve(bi, ref):
        name, mod = ref[0], ref[1]
        n = n2n.get((bi, name))
        if n is not None:
            return n, None
        cands = [n2n[(bb, name)] for bb in mod2builds.get(mod, []) if (bb, name) in n2n] if mod is not None else []
        if len(cands) == 1:
            return cands[0], None
        k = (mod if mod is not None else "", name)
        return None, k

    for nd in nodes:
        d, bi = nd["d"], nd["bi"]
        tu_i, vu_i, tu_x, vu_x = set(), set(), set(), set()
        for ref in d.get("tu", []):
            n, k = resolve(bi, ref)
            (tu_i.add(n) if k is None else tu_x.add(k))
        for ref in d.get("vu", []):
            n, k = resolve(bi, ref)
            (vu_i.add(n) if k is None else vu_x.add(k))
        pending.append((tu_i, vu_i, tu_x, vu_x))
        for k in tu_x | vu_x:
            ext_keys[k] = 1
    ext_sorted = sorted(ext_keys)
    ext_id = {k: i for i, k in enumerate(ext_sorted)}
    E = len(ext_sorted)

    adj_all = [sorted(t | v) for t, v, _, _ in pending]
    adj_f = adj_all
    adj_i = []
    ext_all = [sorted(ext_id[k] for k in (tx | vx)) for _, _, tx, vx in pending]
    ext_f = ext_all
    ext_i = []
    is_thm = [nd["d"]["kind"] == "theorem" for nd in nodes]
    for x, (t, v, tx, vx) in enumerate(pending):
        if is_thm[x]:
            adj_i.append(sorted(t))
            ext_i.append(sorted(ext_id[k] for k in tx))
        else:
            adj_i.append(adj_all[x])
            ext_i.append(ext_all[x])
    Rf_n, Rf_x = scc_closure(N, adj_f, ext_f, E)
    Ri_n, Ri_x = scc_closure(N, adj_i, ext_i, E)
    thm_mask = 0
    for x in range(N):
        if is_thm[x]:
            thm_mask |= 1 << x

    # per-build records
    pkgs = {}
    fam_decl, fam_cone, fam_stmt_rows, fam_th_rows = Family("decl"), Family("cone"), {}, {}
    node_rows, users = [], [[] for _ in range(N)]
    totals = {"cone_full_members": 0, "cone_interface_members": 0, "cone_full_external": 0, "cone_interface_external": 0,
              "max_cone_full": 0, "max_cone_interface": 0}
    for bi, b in enumerate(builds):
        tr = build_trust(b)
        b["trust"] = tr
        meta = b["meta"]
        entry = pkgs.setdefault(b["id"], {"id": b["id"], "lake_name": meta.get("lake_name") or b["verify"].get("package") or b["id"].split("/")[-1],
                                          "license": meta.get("license", "unknown"), "hosted": meta.get("hosted", True),
                                          "ownership": meta.get("ownership", "imported"), "dist_tags": meta.get("dist_tags", {}),
                                          "description": meta.get("description"), "readme_excerpt": meta.get("readme_excerpt"),
                                          "versions": []})
        entry["versions"].append({"version": b["version"], "commit": meta.get("commit") or b["verify"].get("commit") or "0" * 40,
                                  "yanked": bool(meta.get("yanked", False)),
                                  "builds": [{"build_key": meta.get("build_key") or b["verify"].get("build_key") or "0" * 16,
                                              "trains": [meta.get("train", "lean-4.35.0")], "trust": tr}],
                                  "indexed_declarations": len(b["decls"])})
    for p in pkgs.values():
        if not p["dist_tags"]:
            p["dist_tags"] = {"latest": sorted(v["version"] for v in p["versions"])[-1]}

    for x, nd in enumerate(nodes):
        d, bi = nd["d"], nd["bi"]
        b = builds[bi]
        did = "%s@%s#%s" % (b["id"], b["version"], d["name"])
        nd["id"] = did
        s = b["statements"].get(d["name"])
        ax = b["axioms"].get(d["name"]) if b["axioms"] is not None else None
        sorry = (d["name"] in b["sorry"]) if b["sorry_known"] else (True if d["name"] in b["sorry"] else None)
        rec = {"id": did, "n": x, "name": d["name"], "module": d["module"], "pkg": b["id"], "ver": b["version"],
               "bk": b["trust"] and (b["meta"].get("build_key") or b["verify"].get("build_key") or "0" * 16),
               "tr": b["meta"].get("train", "lean-4.35.0"), "kind": d["kind"], "th": d["th"],
               "stmt": s["statement"] if s else None, "sha": s["sha256"] if s else None,
               "ax": ax, "sorry": sorry, "unsafe": bool(d.get("unsafe", False)), "helper": bool(d.get("helper", False)),
               "doc": b["docs"].get(d["name"])}
        if "vh" in d:
            rec["vh"] = d["vh"]
        if d.get("helper_why"):
            rec["hw"] = d["helper_why"]
        fam_decl.add(M.sha256_hex(did), M.canon(rec))
        node_rows.append([did, d["kind"], d["th"], bool(d.get("helper", False))])
        if s:
            row = fam_stmt_rows.setdefault(s["sha256"], {"sha": s["sha256"], "stmt": s["statement"], "ids": []})
            row["ids"].append(did)
            fam_th_rows.setdefault(d["th"], {"th": d["th"], "ids": []})["ids"].append(did)
        # cone of x
        for form, adj_x, Rn, Rx, extx in (("f", adj_all, Rf_n, Rf_x, ext_all), ("i", adj_all, Ri_n, Ri_x, ext_all)):
            nb, xb = 0, 0
            for c in adj_x[x]:
                nb |= Rn[c]
                xb |= Rx[c]
            for e in extx[x]:
                xb |= 1 << e
            nb &= ~(1 << x)
            if form == "f":
                f_n, f_x = bits_to_list(nb), bits_to_list(xb)
            else:
                i_n, i_x = bits_to_list(nb), bits_to_list(xb)
                assumed = bin(nb & thm_mask).count("1")
        crec = {"id": did, "n": x, "f": M.delta_enc(f_n), "fx": M.delta_enc(f_x), "i": M.delta_enc(i_n), "ix": M.delta_enc(i_x), "a": assumed}
        fam_cone.add(M.sha256_hex(did), M.canon(crec))
        totals["cone_full_members"] += len(f_n)
        totals["cone_interface_members"] += len(i_n)
        totals["cone_full_external"] += len(f_x)
        totals["cone_interface_external"] += len(i_x)
        totals["max_cone_full"] = max(totals["max_cone_full"], len(f_n))
        totals["max_cone_interface"] = max(totals["max_cone_interface"], len(i_n))
        for c in adj_all[x]:
            users[c].append(x)

    # write
    if os.path.isdir(out_dir):
        shutil.rmtree(out_dir)
    os.makedirs(out_dir)
    params, files = {"node_chunk": NODE_CHUNK, "rev_chunk": REV_CHUNK}, {}
    params["decl_k"], files["decl"] = fam_decl.write(out_dir, decl_target)
    params["cone_k"], files["cone"] = fam_cone.write(out_dir, cone_target)
    fs, ft = Family("stmt"), Family("th")
    dups = []
    for sha, row in fam_stmt_rows.items():
        row["ids"].sort()
        fs.add(sha, M.canon(row))
        if len(row["ids"]) > 1:
            dups.append({"sha256": sha, "ids": row["ids"]})
    for th, row in fam_th_rows.items():
        row["ids"].sort()
        ft.add(th, M.canon(row))
    params["stmt_k"], files["stmt"] = fs.write(out_dir, decl_target)
    params["th_k"], files["th"] = ft.write(out_dir, decl_target)
    fp = Family("pkg", "json")
    pk_shards = {}
    for pid, p in pkgs.items():
        p["versions"].sort(key=lambda v: v["version"])
        pk_shards.setdefault(M.sha256_hex(pid), {})[pid] = p
    # pkg files hold several packages as one JSON object: shard by k chosen on size
    k = 0
    while k < 4:
        sz = {}
        for kh, _ in pk_shards.items():
            pass
        groups = {}
        for kh, d in pk_shards.items():
            groups.setdefault(M.shard_name(kh, k), {}).update(d)
        if max(len(M.canon(g).encode("utf-8")) for g in groups.values()) <= decl_target:
            break
        k += 1
    groups = {}
    for kh, d in pk_shards.items():
        groups.setdefault(M.shard_name(kh, k), {}).update(d)
    os.makedirs(os.path.join(out_dir, "pkg"))
    pbytes, pmax = 0, 0
    for s, g in groups.items():
        body = M.canon(g).encode("utf-8")
        with open(os.path.join(out_dir, "pkg", s + ".json"), "wb") as f:
            f.write(body)
        pbytes += len(body)
        pmax = max(pmax, len(body))
    params["pkg_k"] = k
    files["pkg"] = {"files": len(groups), "bytes": pbytes, "max_file_bytes": pmax, "records": len(pkgs)}
    files["nodes"] = write_chunks(out_dir, "nodes", node_rows, NODE_CHUNK)
    files["ext"] = write_chunks(out_dir, "ext", [[nm, (md if md != "" else None)] for md, nm in ext_sorted], NODE_CHUNK)
    rev_rows = []
    for x in range(N):
        u = sorted(set(users[x]))
        rev_rows.append({"n": x, "c": len(u), "top": [nodes[y]["id"] for y in u[:TOP_USERS]], "by": M.delta_enc(u)})
    files["rev"] = write_chunks(out_dir, "rev", rev_rows, REV_CHUNK)

    n_edges = sum(len(a) for a in adj_all)
    n_ext_edges = sum(len(a) for a in ext_all)
    thm_stmt = sum(1 for nd in nodes if builds[nd["bi"]]["statements"].get(nd["d"]["name"]))
    bound = ("Per call: get_declaration reads 3 files (decl shard, package shard, reverse chunk); search_statements exact reads "
             "1 statement shard plus 2 files per result (decl shard, package shard; package shards repeat per distinct package) ; "
             "get_package reads 1 file; get_cone reads 2 files (decl shard for the root, cone shard) plus 1 package shard plus one "
             "node chunk per %d consecutive node numbers touched by the page and one external chunk likewise, so at most "
             "2 + 1 + ceil(limit-bounded distinct chunks) and never more than the chunk counts. Every file except a cone "
             "shard holding one very large cone is at most the target size given in params (see files.*.max_file_bytes)." % NODE_CHUNK)
    manifest = {"schema": M.SCHEMA, "built_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "params": params,
                "targets": {"decl_target": decl_target, "cone_target": cone_target},
                "totals": {"builds": len(builds), "packages": len(pkgs), "declarations": N, "helpers": sum(1 for nd in nodes if nd["d"].get("helper")),
                           "theorems_with_statement": thm_stmt, "distinct_statements": len(fam_stmt_rows),
                           "internal_edges": n_edges, "external_references": E, "external_edges": n_ext_edges, **totals},
                "files": files, "duplicate_statements": dups[:1000], "duplicate_statement_count": len(dups),
                "builds": [{"id": b["id"], "version": b["version"], "dir": os.path.basename(b["dir"]), "declarations": len(b["decls"]),
                            "modules": len(b["modules"]), "statements": len(b["statements"]), "orphan_statements": b["orphan_statements"][:20],
                            "axioms_known": b["axioms_known"], "sorry_known": b["sorry_known"], "graph_check": b["graph_check"],
                            "trust": b["trust"]} for b in builds],
                "warnings": warnings, "read_bound": bound, "build_seconds": round(time.time() - t0, 2)}
    with open(os.path.join(out_dir, "manifest.json"), "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=1, sort_keys=True)
    return manifest


def check_new(index_dir, build_dir):
    """Publish-time check: which theorem statements of a new build are already in the index."""
    idx = M.Index(M.DirReader(index_dir))
    recs = [json.loads(l) for l in read_bytes_maybe_zst(os.path.join(build_dir, "graph.jsonl.zst" if os.path.exists(os.path.join(build_dir, "graph.jsonl.zst")) else "graph.jsonl"))[0].decode("utf-8").split("\n") if l.strip()]
    th = {r["name"]: r["th"] for r in recs if r["t"] == "decl"}
    out = []
    for r in read_jsonl(os.path.join(build_dir, "statements.jsonl")):
        p = idx.present(r["statement"], th.get(r["name"]))
        if p["by_sha"] or p["by_th64_confirmed"] or p["by_th64_unconfirmed"]:
            out.append({"name": r["name"], "already_present_as": p["by_sha"] + p["by_th64_confirmed"], "th64_unconfirmed_candidates": p["by_th64_unconfirmed"]})
    return out


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    b = sub.add_parser("build")
    b.add_argument("--builds", required=True)
    b.add_argument("--out", required=True)
    b.add_argument("--decl-target", type=int, default=16384)
    b.add_argument("--cone-target", type=int, default=131072)
    c = sub.add_parser("check-new")
    c.add_argument("--index", required=True)
    c.add_argument("--build", required=True)
    a = ap.parse_args()
    if a.cmd == "build":
        m = build(a.builds, a.out, a.decl_target, a.cone_target)
        print(json.dumps({k: m[k] for k in ("totals", "params", "duplicate_statement_count", "warnings", "build_seconds")}, indent=1))
    else:
        print(json.dumps(check_new(a.index, a.build), indent=1))


if __name__ == "__main__":
    main()
