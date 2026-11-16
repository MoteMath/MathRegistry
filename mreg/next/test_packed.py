#!/usr/bin/env python3
"""Tests of the ranged-archive ("packed") fetch path of mreg/next/mreg.py. Stdlib + numpy (the archive builder); no AWS, no Lean.

    python test_packed.py

A synthetic registry (the Mirror of test_named_import.py) gets archives built by decl-chunks/archives/build_archives.py with a tiny
target size, and is served over HTTP on 127.0.0.1 by a server that honours single ranges and can be told to misbehave: answer 200 to a
range, cut a range body short, flip a byte inside an archive, lose an archive.
"""
import contextlib, gzip, hashlib, http.server, importlib.util, io, json, os, re, shutil, sys, tempfile, threading, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import test_named_import as T
M = T.M
ARCH = os.path.join(os.path.dirname(os.path.dirname(HERE)), "decl-chunks", "archives", "build_archives.py")
spec = importlib.util.spec_from_file_location("build_archives", ARCH)
BA = importlib.util.module_from_spec(spec)
spec.loader.exec_module(BA)

ENTRY = f"{T.MATHLIB}#Mathlib.n60_0"


def sha(b):
    return hashlib.sha256(b).hexdigest()


def add_packed(m, target=1500, variant="checking"):
    """Build archives for the mirror's `variant`, put them under <build>/packed/<variant>/, and add the pointer entry."""
    out = m.p(m.build, "packed", variant)
    r = BA.build(m.p(m.build, variant), m.p(m.build, "index"), out, variant=variant, train=m.train, buildname=m.build, target=target,
                 log=lambda s: None)
    ptr = json.load(open(m.p("current.json")))
    ptr.setdefault("packed", {})[variant] = {"path": f"{m.build}/packed/{variant}/", "packed_sha256": r["packed_sha256"]}
    m.wr(m.p("current.json"), json.dumps(ptr).encode())
    return r


class _Srv(http.server.ThreadingHTTPServer):
    daemon_threads = True


def serve_ranges(root, token="tok", mode=None):
    """A registry directory over HTTP/1.1 with keep-alive. `mode`: None | "200" (answer 200 + whole object to a Range request for an
    archive) | "truncate" (206, full Content-Length, half the body, connection closed) | "badcr" (206 with a shifted Content-Range) |
    "e503" (503 to archive ranges). Records (path, Range header, status) in `log`."""
    log = []

    class H(http.server.BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"

        def log_message(self, *a):
            pass

        def do_GET(self):
            rh = self.headers.get("Range")
            if self.headers.get("x-mreg-token") != token:
                log.append((self.path, rh, 403))
                self.send_response(403); self.send_header("Content-Length", "0"); self.end_headers(); return
            p = os.path.join(root, *self.path.split("/"))
            if not os.path.isfile(p):
                log.append((self.path, rh, 404))
                self.send_response(404); self.send_header("Content-Length", "0"); self.end_headers(); return
            b = open(p, "rb").read()
            is_arch = "/packed/" in self.path and self.path.endswith(".bin")
            if rh is None:
                log.append((self.path, rh, 200))
                self.send_response(200); self.send_header("Content-Length", str(len(b))); self.end_headers(); self.wfile.write(b); return
            mm = re.fullmatch(r"bytes=(\d+)-(\d+)", rh)
            if not mm or int(mm.group(1)) > int(mm.group(2)) or int(mm.group(2)) >= len(b):
                log.append((self.path, rh, 200))          # what the real endpoint does with a bad range: the whole object
                self.send_response(200); self.send_header("Content-Length", str(len(b))); self.end_headers(); self.wfile.write(b); return
            s, e = int(mm.group(1)), int(mm.group(2))
            if mode == "200":
                log.append((self.path, rh, 200))
                self.send_response(200); self.send_header("Content-Length", str(len(b))); self.end_headers(); self.wfile.write(b); return
            if mode == "e503":
                log.append((self.path, rh, 503))
                self.send_response(503); self.send_header("Content-Length", "0"); self.end_headers(); return
            body = b[s:e + 1]
            log.append((self.path, rh, 206))
            self.send_response(206)
            cr = f"bytes {s}-{e}/{len(b)}" if mode != "badcr" else f"bytes {s + 1}-{e + 1}/{len(b)}"
            self.send_header("Content-Range", cr)
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            if mode == "truncate":
                self.wfile.write(body[:len(body) // 2])
                self.wfile.flush()
                self.close_connection = True
                return
            self.wfile.write(body)

    srv = _Srv(("127.0.0.1", 0), H)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    return srv, log


class MergePlan(unittest.TestCase):
    def it(self, a, off, ln):
        return {"a": a, "off": off, "len": ln, "e": (a, off)}

    def test_adjacent_runs_floor_and_archive_boundaries(self):
        items = [self.it(0, 0, 100), self.it(0, 100, 50), self.it(0, 200, 10), self.it(0, 50000, 10), self.it(1, 0, 10)]
        rs = M.merge_ranges(items, 0, 100)
        self.assertEqual([(r["a"], r["start"], r["end"]) for r in rs], [(0, 0, 150), (0, 200, 210), (0, 50000, 50010), (1, 0, 10)])
        rs = M.merge_ranges(items, 16384, 100)               # the 50-byte gap merges, the 49,790-byte one does not, archives never merge
        self.assertEqual([(r["a"], r["start"], r["end"]) for r in rs], [(0, 0, 210), (0, 50000, 50010), (1, 0, 10)])

    def test_cap_merges_the_smallest_gaps_first_and_stops_at_archive_count(self):
        items = [self.it(0, 0, 10), self.it(0, 110, 10), self.it(0, 1000, 10), self.it(0, 1100, 10), self.it(1, 0, 10), self.it(1, 500, 10)]
        rs = M.merge_ranges(items, 0, 100)
        self.assertEqual(len(rs), 6)
        rs = M.merge_ranges(items, 0, 5)                      # gaps: 100, 880, 90 (a0), 490 (a1): the smallest (90) merges
        self.assertEqual([(r["a"], r["start"], r["end"]) for r in rs], [(0, 0, 10), (0, 110, 120), (0, 1000, 1110), (1, 0, 10), (1, 500, 510)])
        self.assertEqual(len(rs), 5)
        self.assertEqual((rs[2]["start"], rs[2]["end"]), (1000, 1110))
        rs = M.merge_ranges(items, 0, 1)                      # cannot go below one range per archive touched
        self.assertEqual([(r["a"], r["start"], r["end"]) for r in rs], [(0, 0, 1110), (1, 0, 510)])
        # every item still lies in exactly one range
        self.assertEqual(sum(len(r["items"]) for r in rs), len(items))


@unittest.skipIf(T._zstd is None, "needs Python 3.14 compression.zstd to build the test mirror")
class PackedImport(T.Base):
    def setUp(self):
        super().setUp()
        self.m = self.mirror()
        self.pr = add_packed(self.m)
        self.cone = self.m.cone(60)
        self.stored = {c: len(self.m.stored[("checking", c)]) for c in self.cone}

    def serve(self, mode=None):
        srv, log = serve_ranges(self.reg, mode=mode)
        self.addCleanup(srv.shutdown)
        self.env_http = {"MREG_REGISTRY": f"http://127.0.0.1:{srv.server_address[1]}", "MREG_TOKEN": "tok"}
        return log

    def add(self, *extra, entry=ENTRY, env=None):
        return self.run_cli("add", entry, "--packed-min", "0", *extra, env=env or getattr(self, "env_http", None))

    def assert_installed_exactly(self, js):
        want = self.cone
        self.assertEqual([c["id"] for c in self.lock()["chunks"]], want)
        c, vj, o, e = self.run_cli("verify")
        self.assertEqual(c, 0, o)
        self.assertEqual(js["fetched"] + js["reused"], len(want))

    def test_ranges_replace_chunk_requests(self):
        log = self.serve()
        c, js, o, e = self.add()
        self.assertEqual(c, 0, (o, e))
        pk = js["packed"]
        self.assertTrue(pk["used"])
        self.assertGreaterEqual(pk["ranges"], 1)
        self.assertLess(pk["ranges"], len(self.cone))
        self.assertEqual(pk["fallback_chunks"], 0)
        self.assertEqual(pk["non_206"], 0)
        self.assertEqual(pk["bytes_used"], sum(self.stored.values()))
        self.assertGreaterEqual(pk["bytes_fetched"], pk["bytes_used"])
        self.assertAlmostEqual(pk["overfetch_ratio"], pk["bytes_fetched"] / pk["bytes_used"], places=3)
        self.assertEqual(js["fetched"], len(self.cone))
        self.assertEqual(js["requests_objects"], pk["ranges"])
        self.assertEqual(js["bytes_fetched"], pk["bytes_fetched"])
        self.assertIn("seconds_fetch", js)
        ranged = [x for x in log if x[1]]
        self.assertEqual(len(ranged), pk["ranges"])
        self.assertTrue(all(x[2] == 206 for x in ranged))
        self.assertFalse([x for x in log if x[0].endswith(".olean.zst")], "no per-chunk file was requested")
        self.assert_installed_exactly(js)
        self.assertEqual(self.lock()["packed"]["path"], f"b1/packed/checking/")

    def test_every_range_sent_is_well_formed_and_inside_its_archive(self):
        log = self.serve()
        c, js, o, e = self.add()
        self.assertEqual(c, 0)
        sizes = {nm: os.path.getsize(self.m.p("b1", "packed", "checking", nm)) for nm in os.listdir(self.m.p("b1", "packed", "checking")) if nm.endswith(".bin")}
        n = 0
        for path, rh, st in log:
            if not path.endswith(".bin"):
                continue
            mm = re.fullmatch(r"bytes=(\d+)-(\d+)", rh)
            self.assertIsNotNone(mm, rh)
            s, e_ = int(mm.group(1)), int(mm.group(2))
            self.assertTrue(0 <= s <= e_ < sizes[path.rsplit("/", 1)[1]], (rh, path))
            n += 1
        self.assertEqual(n, js["packed"]["ranges"])

    def test_range_cap_and_budget_are_on_the_planned_count(self):
        self.serve()
        c, js, o, e = self.add("--dry-run")
        self.assertEqual(c, 0)
        archives_touched = len({self.m_archive(c_) for c_ in self.cone})
        planned = js["packed"]["ranges_planned"]
        self.assertEqual(js["budget"]["requests_needed"], planned + js["packed"]["direct_planned"])
        self.assertEqual(js["packed"]["chunks_missing"], len(self.cone))
        c, js1, o, e = self.add("--dry-run", "--range-requests", "1")
        self.assertEqual(js1["packed"]["ranges_planned"], archives_touched)
        # a real import under --max-requests below the archive count is refused, above it passes, with no --allow-over-budget
        if archives_touched > 1:
            c, jse, o, e = self.add("--max-requests", str(archives_touched - 1))
            self.assertEqual((c, jse["error"]["kind"]), (21, "over_budget"))
            self.assertEqual(self.proj_files(), [], "nothing was fetched or written")
        c, js2, o, e = self.add("--max-requests", str(archives_touched))
        self.assertEqual(c, 0, (o, e))
        self.assertEqual(js2["packed"]["ranges"], archives_touched)
        self.assertEqual(js2["budget"]["over_budget"], False)

    def m_archive(self, cid):
        for ln in gzip.open(self.m.p("b1", "packed", "checking", "layout.tsv.gz"), "rt").read().splitlines()[1:]:
            p = ln.split("\t")
            if p[0] == cid:
                return int(p[1])

    def test_chunks_already_in_the_store_are_not_fetched(self):
        log = self.serve()
        c, js, o, e = self.add(entry=f"{T.MATHLIB}#Mathlib.n40_0")
        self.assertEqual(c, 0, (o, e))
        first = js["fetched"]
        before = len(log)
        c, js2, o, e = self.add()
        self.assertEqual(c, 0, (o, e))
        self.assertGreater(js2["reused"], 0)
        need = [x for x in self.cone if x not in set(self.m.cone(40))]
        self.assertEqual(js2["fetched"], len(need))
        self.assertEqual(js2["packed"]["bytes_used"], sum(self.stored[x] for x in need))
        self.assertEqual([c["id"] for c in self.lock()["chunks"]], sorted(set(self.cone) | set(self.m.cone(40))))
        c, vj, o, e = self.run_cli("verify")
        self.assertEqual(c, 0, o)
        self.assertEqual(first + js2["fetched"], len(set(self.cone) | set(self.m.cone(40))))

    def test_server_answers_200_to_ranges_falls_back_and_counts(self):
        log = self.serve("200")
        c, js, o, e = self.add()
        self.assertEqual(c, 0, (o, e))
        pk = js["packed"]
        self.assertEqual(pk["non_206"], pk["ranges"])
        self.assertEqual(pk["non_206_kinds"], {"status_200": pk["ranges"]})
        self.assertEqual(pk["fallback_chunks"], len(self.cone))
        self.assertEqual(pk["fallback_ranges"], pk["ranges"])
        self.assertEqual(pk["bytes_used"], 0)
        # the whole-object body of a 200 was never read: wire bytes are the chunk files only
        self.assertEqual(js["bytes_fetched"], sum(self.stored.values()))
        self.assertTrue(any(x[0].endswith(".olean.zst") for x in log))
        self.assert_installed_exactly(js)
        self.assertTrue(any("fell back" in n for n in js["notes"]))

    def test_content_range_mismatch_is_an_error_for_that_range(self):
        self.serve("badcr")
        c, js, o, e = self.add()
        self.assertEqual(c, 0, (o, e))
        self.assertEqual(js["packed"]["non_206_kinds"], {"content_range": js["packed"]["ranges"]})
        self.assertEqual(js["packed"]["fallback_chunks"], len(self.cone))
        self.assert_installed_exactly(js)

    def test_truncated_range_retries_then_falls_back(self):
        log = self.serve("truncate")
        c, js, o, e = self.add()
        self.assertEqual(c, 0, (o, e))
        pk = js["packed"]
        self.assertGreaterEqual(pk["fallback_chunks"], 1)
        self.assertIn("short", pk["non_206_kinds"])
        ranged = [x for x in log if x[1]]
        self.assertGreater(len(ranged), pk["ranges"], "MREG_RETRIES=1: a short range is asked again once")
        self.assert_installed_exactly(js)

    def test_corrupted_byte_inside_an_archive_falls_back_for_that_chunk_only(self):
        # flip one byte in the archive inside a needed chunk; the per-chunk file is intact
        target = self.cone[len(self.cone) // 2]
        row = [ln.split("\t") for ln in gzip.open(self.m.p("b1", "packed", "checking", "layout.tsv.gz"), "rt").read().splitlines()[1:]
               if ln.startswith(target)][0]
        ap = self.m.p("b1", "packed", "checking", f"A{int(row[1]):04d}.bin")
        b = bytearray(open(ap, "rb").read())
        b[int(row[2]) + int(row[3]) // 2] ^= 1
        open(ap, "wb").write(bytes(b))
        self.serve()
        c, js, o, e = self.add()
        self.assertEqual(c, 0, (o, e))
        pk = js["packed"]
        self.assertEqual(pk["fallback_chunks"], 1)
        self.assertEqual(pk["fallback_reasons"], {"hash_mismatch": 1})
        self.assertEqual(pk["bytes_used"], sum(self.stored.values()) - self.stored[target])
        self.assertIn({"chunk": target, "reason": "hash_mismatch"}, pk["fallbacks"])
        self.assert_installed_exactly(js)

    def test_corrupt_in_the_archive_and_in_the_chunk_file_is_refused(self):
        target = self.cone[3]
        row = [ln.split("\t") for ln in gzip.open(self.m.p("b1", "packed", "checking", "layout.tsv.gz"), "rt").read().splitlines()[1:]
               if ln.startswith(target)][0]
        ap = self.m.p("b1", "packed", "checking", f"A{int(row[1]):04d}.bin")
        b = bytearray(open(ap, "rb").read())
        b[int(row[2]) + 1] ^= 1
        open(ap, "wb").write(bytes(b))
        self.m.corrupt_stored("checking", target)
        self.serve()
        c, js, o, e = self.add()
        self.assertEqual((c, js["error"]["kind"]), (14, "hash_mismatch"))
        self.assertFalse(os.path.exists(os.path.join(self.store, "objects", sha(self.m.stored[("checking", target)])[:2],
                                                     sha(self.m.stored[("checking", target)]))))

    def test_missing_archive_falls_back(self):
        os.unlink(self.m.p("b1", "packed", "checking", "A0000.bin"))
        self.serve()
        c, js, o, e = self.add()
        self.assertEqual(c, 0, (o, e))
        pk = js["packed"]
        in0 = [x for x in self.cone if self.m_archive(x) == 0]
        self.assertGreater(len(in0), 0)
        self.assertEqual(pk["non_206_kinds"], {"missing": pk["non_206"]})
        self.assertEqual(pk["fallback_chunks"], len(in0))
        self.assert_installed_exactly(js)

    def test_a_503_range_is_retried_then_falls_back(self):
        self.serve("e503")
        c, js, o, e = self.add()
        self.assertEqual(c, 0, (o, e))
        self.assertEqual(js["packed"]["fallback_chunks"], len(self.cone))
        self.assert_installed_exactly(js)

    def test_tables_that_fail_verification_are_reported_and_per_chunk_is_used(self):
        lp = self.m.p("b1", "packed", "checking", "layout.tsv.gz")
        b = bytearray(open(lp, "rb").read())
        b[len(b) // 2] ^= 1
        open(lp, "wb").write(bytes(b))
        log = self.serve()
        c, js, o, e = self.add()
        self.assertEqual(c, 0, (o, e))
        pk = js["packed"]
        self.assertFalse(pk["used"])
        self.assertIn("hash_mismatch", pk["error"])
        self.assertTrue(any("NOT used" in n for n in js["notes"]))
        self.assertEqual(js["requests_objects"], len(self.cone))
        self.assertFalse([x for x in log if x[1]])
        self.assert_installed_exactly(js)
        self.assertEqual(os.path.exists(os.path.join(self.store, "index", T.TRAIN, "b1", "packed-checking", "READY.json")), False)

    def test_packed_json_not_matching_the_pointer_is_reported(self):
        ptr = json.load(open(self.m.p("current.json")))
        ptr["packed"]["checking"]["packed_sha256"] = "0" * 64
        self.m.wr(self.m.p("current.json"), json.dumps(ptr).encode())
        self.serve()
        c, js, o, e = self.add()
        self.assertEqual(c, 0, (o, e))
        self.assertIn("packed.json", js["packed"]["error"])
        self.assertFalse(js["packed"]["used"])

    def test_manifest_disagreement_goes_per_chunk_for_that_chunk(self):
        # a layout row whose length differs from the manifest: rebuild the tables with a wrong length, re-pin them
        out = self.m.p("b1", "packed", "checking")
        rows = gzip.open(os.path.join(out, "layout.tsv.gz"), "rt").read().splitlines()
        victim = self.cone[2]
        for i, ln in enumerate(rows):
            if ln.startswith(victim):
                p = ln.split("\t")
                p[3] = str(int(p[3]) - 1)
                rows[i] = "\t".join(p)
        lay = BA.gz_bytes(("\n".join(rows) + "\n").encode())
        pj = json.load(open(os.path.join(out, "packed.json")))
        pj["layout_sha256"] = sha(lay)
        pjb = (json.dumps(pj, indent=1, sort_keys=True) + "\n").encode()
        open(os.path.join(out, "layout.tsv.gz"), "wb").write(lay)
        open(os.path.join(out, "packed.json"), "wb").write(pjb)
        ptr = json.load(open(self.m.p("current.json")))
        ptr["packed"]["checking"]["packed_sha256"] = sha(pjb)
        self.m.wr(self.m.p("current.json"), json.dumps(ptr).encode())
        self.serve()
        c, js, o, e = self.add()
        self.assertEqual(c, 0, (o, e))
        self.assertEqual(js["packed"]["fallback_reasons"], {"layout_mismatch": 1})
        self.assertEqual(js["packed"]["bytes_used"], sum(self.stored.values()) - self.stored[victim])
        self.assert_installed_exactly(js)

    def test_default_threshold_keeps_small_imports_per_chunk(self):
        log = self.serve()
        c, js, o, e = self.run_cli("add", ENTRY, env=self.env_http)           # default --packed-min 200: this cone is smaller
        self.assertEqual(c, 0, (o, e))
        self.assertFalse(js["packed"]["used"])
        self.assertIn("below", js["packed"]["reason"])
        self.assertEqual(js["requests_objects"], len(self.cone))
        self.assertFalse([x for x in log if x[1]])

    def test_no_packed_flag_and_absent_pointer_entry(self):
        self.serve()
        c, js, o, e = self.add("--no-packed")
        self.assertEqual(c, 0)
        self.assertEqual(js["packed"]["reason"], "--no-packed")
        self.assertEqual(js["requests_objects"], len(self.cone))
        shutil.rmtree(self.proj)
        shutil.rmtree(self.store)
        self.new_proj(self.proj)
        ptr = json.load(open(self.m.p("current.json")))
        ptr.pop("packed")
        self.m.wr(self.m.p("current.json"), json.dumps(ptr).encode())
        c, js, o, e = self.add()
        self.assertEqual(c, 0)
        self.assertFalse(js["packed"]["available"])
        self.assertEqual(js["requests_objects"], len(self.cone))

    def test_ci_restores_with_ranges_from_the_lock(self):
        self.serve()
        c, js, o, e = self.add()
        self.assertEqual(c, 0)
        shutil.rmtree(self.store)
        shutil.rmtree(os.path.join(self.proj, ".lake"))
        c, js, o, e = self.run_cli("ci", "--packed-min", "0", env=self.env_http)
        self.assertEqual(c, 0, (o, e))
        self.assertTrue(js["packed"]["used"])
        self.assertEqual(js["packed"]["fallback_chunks"], 0)
        self.assertEqual(js["fetched"], len(self.cone))

    def test_file_registry_uses_ranges_too(self):
        c, js, o, e = self.add()
        self.assertEqual(c, 0, (o, e))
        self.assertTrue(js["packed"]["used"])
        self.assertEqual(js["packed"]["fallback_chunks"], 0)
        self.assertEqual(js["fetched"], len(self.cone))
        self.assert_installed_exactly(js)

    def test_index_command_caches_the_tables(self):
        self.serve()
        c, js, o, e = self.run_cli("index", env=self.env_http)
        self.assertEqual(c, 0, (o, e))
        self.assertTrue(js["packed"]["tables_cached"])
        # with the tables cached even a small import goes by ranges
        c, js, o, e = self.run_cli("add", ENTRY, env=self.env_http)
        self.assertTrue(js["packed"]["used"])

    def test_no_secret_in_any_output(self):
        self.serve()
        c, js, o, e = self.add()
        for txt in (o, e, json.dumps(js)):
            self.assertNotIn("tok\"", txt)
            self.assertNotIn("x-mreg-token", txt)


@unittest.skipIf(T._zstd is None, "needs Python 3.14 compression.zstd")
class ThreadedInstall(unittest.TestCase):
    def test_install_chunks_threaded_matches_sequential_and_detects_damage(self):
        import random
        tmp = tempfile.mkdtemp(prefix="mreg-inst-")
        self.addCleanup(shutil.rmtree, tmp, True)
        store = M.Store(os.path.join(tmp, "store"))
        rnd = random.Random(3)
        ents = []
        for i in range(300):
            raw = bytes(rnd.randrange(256) for _ in range(50 + i))
            st = T._zstd.compress(raw, 3)
            cid = hashlib.sha256(str(i).encode()).hexdigest()[:32]
            M.write_in_place(store.obj(sha(st)), st)
            ents.append({"id": cid, "sha256_raw": sha(raw), "bytes_raw": len(raw), "sha256_stored": sha(st), "bytes_stored": len(st)})
        cd = os.path.join(tmp, "chunks")
        self.assertEqual(M.install_chunks(store, cd, ents), (300, 0))
        self.assertEqual(M.install_chunks(store, cd, ents), (0, 300))
        os.unlink(os.path.join(cd, *M.chunk_rel(ents[7]["id"]).split("/")))
        self.assertEqual(M.install_chunks(store, cd, ents), (1, 299))
        bad = os.path.join(store.root, "objects", ents[9]["sha256_stored"][:2], ents[9]["sha256_stored"])
        b = bytearray(open(bad, "rb").read()); b[-1] ^= 1; open(bad, "wb").write(bytes(b))
        os.unlink(os.path.join(cd, *M.chunk_rel(ents[9]["id"]).split("/")))
        with self.assertRaises(M.NIError) as cm:
            M.install_chunks(store, cd, ents)
        self.assertEqual(cm.exception.kind, "hash_mismatch")


if __name__ == "__main__":
    unittest.main(verbosity=1)
