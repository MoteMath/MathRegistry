#!/usr/bin/env python3
"""Ranged archive layer of the declaration store (variant `checking` or `full`).

Reads the index tables of one build (manifest.tsv.gz, chunk_edges.tsv.gz), computes the layout `dfs.deepfirst/v1`
deterministically, verifies every chunk file against the manifest (size and sha256_stored), and writes

    A<4 digits>.bin     concatenated stored chunk frames, cut at chunk boundaries (target 256 MiB)
    layout.tsv.gz       chunk, archive, offset, length, sha256_stored   (one row per chunk, in layout order)
    archives.tsv        name, bytes, sha256
    packed.json         schema mreg-decl-packed/1

Layout `dfs.deepfirst/v1` (PACKING.md): chunk ids sorted ascending give the node numbers; an edge `chunk imports_chunk` is a
dependency; DFS post-order over the dependencies (a chunk's imports visited in edge-table order, so a chunk comes right after
everything it needs), DFS roots taken by descending dependency level (longest import path down to a chunk with no imports),
ties by chunk id. Nothing depends on a sample, a clock or a random number, and every gzip is written with mtime 0, so two runs
over the same inputs give identical bytes.

Usage: build_archives.py --chunks DIR --index DIR --out DIR [--variant checking] [--train T --build B] [--hash-only]
Python 3 + numpy (numpy only for the graph arrays).
"""
import argparse, concurrent.futures as cf, gzip, hashlib, io, json, os, sys, time
import numpy as np

SCHEMA = "mreg-decl-packed/1"
LAYOUT_NAME = "dfs.deepfirst"
ALGO_VERSION = 1
ARCHIVE_TARGET = 256 << 20
POLICY = {"gap_floor": 16384, "max_requests": 100}


def below_normal():
    if os.name == "nt":
        try:
            import ctypes
            ctypes.windll.kernel32.SetPriorityClass(ctypes.windll.kernel32.GetCurrentProcess(), 0x4000)
        except Exception:
            pass


# ---- the order -----------------------------------------------------------------------------------------------------

def dependency_levels(n, src, dst):
    """level[v] = 0 when v imports nothing, else 1 + max level of what it imports. Raises on a cycle."""
    cnt = np.bincount(src, minlength=n).astype(np.int64)           # imports of each chunk, with multiplicity
    o = np.argsort(dst, kind="stable")
    rsrc = src[o]                                                  # importers, grouped by imported chunk
    rptr = np.zeros(n + 1, dtype=np.int64)
    rptr[1:] = np.cumsum(np.bincount(dst, minlength=n))
    level = np.full(n, -1, dtype=np.int32)
    remaining = cnt.copy()
    front = np.nonzero(remaining == 0)[0]
    L = 0
    while len(front):
        level[front] = L
        starts, ends = rptr[front], rptr[front + 1]
        lens = ends - starts
        tot = int(lens.sum())
        if tot == 0:
            break
        idx = np.repeat(starts - np.concatenate(([0], np.cumsum(lens)[:-1])), lens) + np.arange(tot)
        imp = rsrc[idx]
        remaining -= np.bincount(imp, minlength=n)
        cand = np.unique(imp)
        front = cand[remaining[cand] == 0]
        L += 1
    if (level < 0).any():
        raise ValueError("the import graph has a cycle")
    return level


def deepfirst_order(n, src, dst):
    """Chunk numbers 0..n-1 in layout order. `src imports dst`; edges in table order give the visiting order of imports."""
    src = np.asarray(src, dtype=np.int64)
    dst = np.asarray(dst, dtype=np.int64)
    level = dependency_levels(n, src, dst)
    o = np.argsort(src, kind="stable")
    adj = dst[o].tolist()
    ptr = np.zeros(n + 1, dtype=np.int64)
    ptr[1:] = np.cumsum(np.bincount(src, minlength=n))
    ptr = ptr.tolist()
    roots = np.lexsort((np.arange(n), -level.astype(np.int64))).tolist()
    seen = bytearray(n)
    out = []
    for r in roots:
        if seen[r]:
            continue
        seen[r] = 1
        stack = [(r, ptr[r])]
        while stack:
            v, i = stack.pop()
            e = ptr[v + 1]
            while i < e:
                w = adj[i]
                i += 1
                if not seen[w]:
                    seen[w] = 1
                    stack.append((v, i))
                    stack.append((w, ptr[w]))
                    break
            else:
                out.append(v)
    assert len(out) == n
    return np.array(out, dtype=np.int64), level


def cut_archives(lengths_in_order, target=ARCHIVE_TARGET):
    """(archive number, offset) per position: a new archive starts when the next chunk would pass `target` (a chunk is never split;
    a chunk bigger than the target gets an archive of its own)."""
    arch, off, a, cur = [], [], 0, 0
    for ln in lengths_in_order:
        if cur and cur + ln > target:
            a += 1
            cur = 0
        arch.append(a)
        off.append(cur)
        cur += ln
    return arch, off


# ---- tables --------------------------------------------------------------------------------------------------------

def read_manifest(path, variant):
    """ids sorted ascending (bytes, hex), stored bytes, sha256_stored (hex str)."""
    ids, sizes, shas = [], [], []
    with gzip.open(path, "rb") as f:
        hdr = f.readline().rstrip(b"\r\n").split(b"\t")
        ci = {h: i for i, h in enumerate(hdr)}
        for need in (b"variant", b"id", b"sha256_stored", b"bytes_stored"):
            if need not in ci:
                raise SystemExit(f"manifest has no column {need.decode()}")
        for line in f:
            p = line.rstrip(b"\r\n").split(b"\t")
            if p[ci[b"variant"]].decode() != variant:
                continue
            ids.append(p[ci[b"id"]])
            sizes.append(int(p[ci[b"bytes_stored"]]))
            shas.append(p[ci[b"sha256_stored"]].decode())
    o = sorted(range(len(ids)), key=ids.__getitem__)
    ids = [ids[i] for i in o]
    if len(set(ids)) != len(ids):
        raise SystemExit("duplicate chunk ids in the manifest")
    return ids, np.array([sizes[i] for i in o], dtype=np.int64), [shas[i] for i in o]


def read_edges(path, ids):
    pos = {c: i for i, c in enumerate(ids)}
    src, dst = [], []
    with gzip.open(path, "rb") as f:
        f.readline()
        for line in f:
            a, b = line.split()
            src.append(pos[a])
            dst.append(pos[b])
    return np.array(src, dtype=np.int64), np.array(dst, dtype=np.int64)


def gz_bytes(data):
    buf = io.BytesIO()
    with gzip.GzipFile(filename="", mode="wb", fileobj=buf, mtime=0, compresslevel=6) as g:
        g.write(data)
    return buf.getvalue()


def sha256b(b):
    return hashlib.sha256(b).hexdigest()


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()


# ---- build ---------------------------------------------------------------------------------------------------------

def chunk_path(chunks_dir, cid):
    return os.path.join(chunks_dir, "X" + cid[:2], "C" + cid + ".olean.zst")


APACHE_2_0_TEXT = """Apache License
Version 2.0, January 2004
http://www.apache.org/licenses/

TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

1. Definitions.

"License" shall mean the terms and conditions for use, reproduction,
and distribution as defined by Sections 1 through 9 of this document.

"Licensor" shall mean the copyright owner or entity authorized by
the copyright owner that is granting the License.

"Legal Entity" shall mean the union of the acting entity and all
other entities that control, are controlled by, or are under common
control with that entity. For the purposes of this definition,
"control" means (i) the power, direct or indirect, to cause the
direction or management of such entity, whether by contract or
otherwise, or (ii) ownership of fifty percent (50%) or more of the
outstanding shares, or (iii) beneficial ownership of such entity.

"You" (or "Your") shall mean an individual or Legal Entity
exercising permissions granted by this License.

"Source" form shall mean the preferred form for making modifications,
including but not limited to software source code, documentation
source, and configuration files.

"Object" form shall mean any form resulting from mechanical
transformation or translation of a Source form, including but
not limited to compiled object code, generated documentation,
and conversions to other media types.

"Work" shall mean the work of authorship, whether in Source or
Object form, made available under the License, as indicated by a
copyright notice that is included in or attached to the work
(an example is provided in the Appendix below).

"Derivative Works" shall mean any work, whether in Source or Object
form, that is based on (or derived from) the Work and for which the
editorial revisions, annotations, elaborations, or other modifications
represent, as a whole, an original work of authorship. For the purposes
of this License, Derivative Works shall not include works that remain
separable from, or merely link (or bind by name) to the interfaces of,
the Work and Derivative Works thereof.

"Contribution" shall mean any work of authorship, including
the original version of the Work and any modifications or additions
to that Work or Derivative Works thereof, that is intentionally
submitted to Licensor for inclusion in the Work by the copyright owner
or by an individual or Legal Entity authorized to submit on behalf of
the copyright owner. For the purposes of this definition, "submitted"
means any form of electronic, verbal, or written communication sent
to the Licensor or its representatives, including but not limited to
communication on electronic mailing lists, source code control systems,
and issue tracking systems that are managed by, or on behalf of, the
Licensor for the purpose of discussing and improving the Work, but
excluding communication that is conspicuously marked or otherwise
designated in writing by the copyright owner as "Not a Contribution."

"Contributor" shall mean Licensor and any individual or Legal Entity
on behalf of whom a Contribution has been received by Licensor and
subsequently incorporated within the Work.

2. Grant of Copyright License. Subject to the terms and conditions of
this License, each Contributor hereby grants to You a perpetual,
worldwide, non-exclusive, no-charge, royalty-free, irrevocable
copyright license to reproduce, prepare Derivative Works of,
publicly display, publicly perform, sublicense, and distribute the
Work and such Derivative Works in Source or Object form.

3. Grant of Patent License. Subject to the terms and conditions of
this License, each Contributor hereby grants to You a perpetual,
worldwide, non-exclusive, no-charge, royalty-free, irrevocable
(except as stated in this section) patent license to make, have made,
use, offer to sell, sell, import, and otherwise transfer the Work,
where such license applies only to those patent claims licensable
by such Contributor that are necessarily infringed by their
Contribution(s) alone or by combination of their Contribution(s)
with the Work to which such Contribution(s) was submitted. If You
institute patent litigation against any entity (including a
cross-claim or counterclaim in a lawsuit) alleging that the Work
or a Contribution incorporated within the Work constitutes direct
or contributory patent infringement, then any patent licenses
granted to You under this License shall terminate as of the date
such litigation is filed.

4. Redistribution. You may reproduce and distribute copies of the
Work or Derivative Works thereof in any medium, with or without
modifications, and in Source or Object form, provided that You
meet the following conditions:

(a) You must give any other recipients of the Work or
Derivative Works a copy of this License; and

(b) You must cause any modified files to carry prominent notices
stating that You changed the files; and

(c) You must retain, in the Source form of any Derivative Works
that You distribute, all copyright, patent, trademark, and
attribution notices from the Source form of the Work,
excluding those notices that do not pertain to any part of
the Derivative Works; and

(d) If the Work includes a "NOTICE" text file as part of its
distribution, then any Derivative Works that You distribute must
include a readable copy of the attribution notices contained
within such NOTICE file, excluding those notices that do not
pertain to any part of the Derivative Works, in at least one
of the following places: within a NOTICE text file distributed
as part of the Derivative Works; within the Source form or
documentation, if provided along with the Derivative Works; or,
within a display displayed by the Derivative Works, if and
wherever such third-party notices normally appear. The contents
of the NOTICE file are for informational purposes only and
do not modify the License. You may add Your own attribution
notices within Derivative Works that You distribute, alongside
or as an addendum to the NOTICE text from the Work, provided
that such additional attribution notices cannot be construed
as modifying the License.

You may add Your own copyright notice to Your modifications and
may provide additional or different license terms and conditions
for use, reproduction, or distribution of Your modifications, or
for any such Derivative Works as a whole, provided Your use,
reproduction, and distribution of the Work otherwise complies with
the conditions stated in this License.

5. Submission of Contributions. Unless You explicitly state otherwise,
any Contribution intentionally submitted for inclusion in the Work
by You to the Licensor shall be under the terms and conditions of
this License, without any additional terms or conditions.
Notwithstanding the above, nothing herein shall supersede or modify
the terms of any separate license agreement you may have executed
with Licensor regarding such Contributions.

6. Trademarks. This License does not grant permission to use the trade
names, trademarks, service marks, or product names of the Licensor,
except as required for reasonable and customary use in describing the
origin of the Work and reproducing the copyright notice of the Work.

7. Disclaimer of Warranty. Unless required by applicable law or
agreed to in writing, Licensor provides the Work (and each
Contributor provides its Contributions) on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
implied, including, but not limited to, any warranties or conditions
of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
PARTICULAR PURPOSE. You are solely responsible for determining the
appropriateness of using or redistributing the Work and assume any
risks associated with Your exercise of permissions under this License.

8. Limitation of Liability. In no event and under no legal theory,
whether in tort (including negligence), contract, or otherwise,
unless required by applicable law (such as deliberate acts) or agreed
to in writing, shall any Contributor be liable to You for damages,
including any direct, indirect, special, incidental, or consequential
damages of any character arising as a result of this License or out
of the use or inability to use the Work (including but not limited to
damages for loss of goodwill, work stoppage, computer failure or
malfunction, or any and all other commercial damages or losses), even
if such Contributor has been advised of the possibility of such
damages.

9. Accepting Warranty or Additional Liability. While redistributing
the Work or Derivative Works thereof, You may choose to offer,
and charge a fee for, acceptance of support, warranty, indemnity,
or other liability obligations and/or rights consistent with this
License. However, in accepting such obligations, You may act only
on Your own behalf and on Your sole responsibility, not on behalf
of any other Contributor, and only if You agree to indemnify,
defend, and hold each Contributor harmless for any liability
incurred by, or claims asserted against, any such Contributor by reason
of your accepting any such warranty or additional liability.

END OF TERMS AND CONDITIONS
"""


def third_party_licenses_text(train, buildname, variant):
    """Deterministic attribution and Apache License 2.0 text for declaration-chunk outputs."""
    return (
        "# Third-Party Licences and Notices for Declaration Chunks\n\n"
        f"Train: {train}\n"
        f"Build: {buildname}\n"
        f"Variant: {variant}\n\n"
        "These compiled Lean 4 declaration chunks are repackaged builds of upstream\n"
        "packages on the stated train (including leanprover-community/mathlib4 and\n"
        "its pinned dependencies: batteries, aesop, quote4, ProofWidgets4, plausible,\n"
        "import-graph, and LeanSearchClient). Each package record under\n"
        "`/v1/index/<owner>/<repo>.json` gives the exact repository URL, commit hash,\n"
        "and SPDX licence identifier (`Apache-2.0`).\n\n"
        "mathregistry is unofficial and unaffiliated with the upstream authors.\n"
        "Please cite the upstream authors' repositories and commits, not mathregistry.\n\n"
        + APACHE_2_0_TEXT
    )


def build(chunks_dir, index_dir, out_dir, variant="checking", train="lean-4.35.0", buildname="b1", target=ARCHIVE_TARGET,
          hash_only=False, threads=8, log=print):
    t0 = time.time()
    man_path = os.path.join(index_dir, "manifest.tsv.gz")
    ids_b, sizes, shas = read_manifest(man_path, variant)
    ids = [c.decode() for c in ids_b]
    n = len(ids)
    log(f"manifest: {n} {variant} chunks, {int(sizes.sum())} stored bytes ({time.time()-t0:.0f} s)")
    src, dst = read_edges(os.path.join(index_dir, "chunk_edges.tsv.gz"), ids_b)
    log(f"edges: {len(src)} ({time.time()-t0:.0f} s)")
    order, level = deepfirst_order(n, src, dst)
    log(f"order: {n} chunks, {int(level.max())+1 if n else 0} levels ({time.time()-t0:.0f} s)")
    lens = [int(sizes[i]) for i in order]
    arch, off = cut_archives(lens, target)
    na = arch[-1] + 1 if n else 0
    os.makedirs(out_dir, exist_ok=True)
    names = [f"A{a:04d}.bin" for a in range(na)]
    # Where each chunk goes, by chunk number (= sorted id order = the directory order on disk, so the files are read in that order:
    # reading in layout order is a random walk over 600,000 small files and was measured at 15 files/s on the HDD).
    where = [None] * n
    for pos in range(n):
        where[int(order[pos])] = pos
    sizes_a = [0] * na
    for pos in range(n):
        sizes_a[arch[pos]] = max(sizes_a[arch[pos]], off[pos] + lens[pos])
    bufs = [bytearray(sz) for sz in sizes_a]           # the archives are assembled in memory (about the store's size) and written once
    problems = []

    def read_one(i):
        pos = where[i]
        try:
            with open(chunk_path(chunks_dir, ids[i]), "rb") as f:
                b = f.read()
        except OSError as e:
            return i, None, f"unreadable: {e}"
        if len(b) != lens[pos]:
            return i, None, f"size {len(b)} != manifest {lens[pos]}"
        if sha256b(b) != shas[i]:
            return i, None, "sha256 differs from the manifest"
        return i, b, None

    batch = 4000
    with cf.ThreadPoolExecutor(threads) as ex:
        for s0 in range(0, n, batch):
            for i, b, why in ex.map(read_one, range(s0, min(n, s0 + batch))):
                if why:
                    problems.append((ids[i], why))
                    continue
                pos = where[i]
                bufs[arch[pos]][off[pos]:off[pos] + len(b)] = b
            if (s0 // batch) % 25 == 0:
                log(f"  read {min(n, s0+batch)}/{n} chunks ({time.time()-t0:.0f} s)")
    if problems:
        raise SystemExit(f"{len(problems)} chunk files are missing or do not match the manifest; first: {problems[:3]}")
    abytes = [len(x) for x in bufs]
    hashers = []
    for a in range(na):
        hashers.append(hashlib.sha256(bufs[a]))
        if not hash_only:
            with open(os.path.join(out_dir, names[a]), "wb") as g:
                g.write(bufs[a])
        bufs[a] = None
    log(f"archives assembled ({time.time()-t0:.0f} s)")
    lay = io.StringIO()
    lay.write("chunk\tarchive\toffset\tlength\tsha256_stored\n")
    for pos in range(n):
        i = int(order[pos])
        lay.write(f"{ids[i]}\t{arch[pos]}\t{off[pos]}\t{lens[pos]}\t{shas[i]}\n")
    layout_gz = gz_bytes(lay.getvalue().encode())
    arc_b = ("name\tbytes\tsha256\n" + "".join(f"{names[a]}\t{abytes[a]}\t{hashers[a].hexdigest()}\n" for a in range(na))).encode()
    packed = {"schema": SCHEMA, "train": train, "build": buildname, "variant": variant, "layout": LAYOUT_NAME,
              "algorithm_version": ALGO_VERSION, "archive_count": na, "archive_target_bytes": target,
              "chunk_count": n, "manifest_sha256": sha256_file(man_path),
              "layout_sha256": sha256b(layout_gz), "archives_sha256": sha256b(arc_b),
              "policy": dict(POLICY)}
    pj = (json.dumps(packed, indent=1, sort_keys=True) + "\n").encode()
    lic_b = third_party_licenses_text(train, buildname, variant).encode("utf-8")
    for nm, b in (("layout.tsv.gz", layout_gz), ("archives.tsv", arc_b), ("packed.json", pj), ("THIRD_PARTY_LICENSES.txt", lic_b)):
        with open(os.path.join(out_dir, nm), "wb") as g:
            g.write(b)
    log(f"done: {na} archives, {sum(abytes)} bytes, layout {len(layout_gz)} B gz, packed.json sha256 {sha256b(pj)} ({time.time()-t0:.0f} s)")
    return {"archives": na, "bytes": sum(abytes), "packed_sha256": sha256b(pj), "layout_sha256": sha256b(layout_gz),
            "archives_sha256": sha256b(arc_b), "licenses_sha256": sha256b(lic_b),
            "archive_hashes": {names[a]: hashers[a].hexdigest() for a in range(na)}}


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--chunks", required=True, help="directory holding X<2hex>/C<id>.olean.zst")
    ap.add_argument("--index", required=True, help="directory holding manifest.tsv.gz and chunk_edges.tsv.gz")
    ap.add_argument("--out", required=True)
    ap.add_argument("--variant", default="checking")
    ap.add_argument("--train", default="lean-4.35.0")
    ap.add_argument("--build", default="b1")
    ap.add_argument("--target", type=int, default=ARCHIVE_TARGET)
    ap.add_argument("--hash-only", action="store_true", help="compute every hash and table but write no archive file")
    ap.add_argument("--threads", type=int, default=8)
    a = ap.parse_args(argv)
    below_normal()
    r = build(a.chunks, a.index, a.out, a.variant, a.train, a.build, a.target, a.hash_only, a.threads,
              log=lambda s: print(s, flush=True))
    with open(os.path.join(a.out, "hashes.json"), "w") as g:
        json.dump(r, g, indent=1, sort_keys=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
