#!/usr/bin/env python3
"""T-C3 tests: the local store is safe for concurrent use (mreg/next/mreg.py).

    python -I test_store_concurrency.py                 # all, about a minute
    MREG_TEST_PROCS=8 python -I ...                     # fewer processes (default 50, at most 12 at once)

Stdlib only; no Lean, no network (a synthetic file:// registry from test_named_import.Mirror). Child processes run at below-normal
priority on Windows. Needs Python 3.14 (compression.zstd) like the other named-import tests.

1. 50 processes install overlapping cones into ONE shared store (every one of them also races to build the same index): all exit 0,
   each project's chunks equal the model's cone, `verify --json` is clean in each, and the store afterwards is file for file, byte for
   byte, the store one process builds alone; no `.part-*`, `.lock` or other leftover remains.
2. A writer killed in the middle (the process is gone): a stale temporary file, a stale lock and a half-built index directory are
   left behind; the next run finishes, deletes what is stale, and the store equals the one-process store.
3. Unit tests of the helpers: unique temporary names, flush then replace, lock recovery by dead process, by age, wait bounded.
"""
import concurrent.futures as cf, hashlib, json, os, shutil, subprocess, sys, tempfile, time, unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import test_named_import as T       # noqa: E402

M = T.M
MREG = os.path.join(HERE, "mreg.py")
PROCS = int(os.environ.get("MREG_TEST_PROCS", "50"))
AT_ONCE = min(12, PROCS)
BELOW_NORMAL = 0x4000 if os.name == "nt" else 0


def entry(i, k=0):
    return f"{T.MATHLIB}#Mathlib.n{i}_{k}"


def _content(p, name):
    """The bytes compared. Everything is compared as written, except the one field that records how long the index build took
    (`built_seconds`, in READY.json and in the meta table of decl.sqlite): it is a wall-clock time and differs between any two builds."""
    raw = open(p, "rb").read()
    if name == "READY.json":
        d = json.loads(raw)
        d.get("lookup", {}).pop("built_seconds", None)
        return json.dumps(d, sort_keys=True).encode()
    if name.endswith(".sqlite"):
        import sqlite3
        db = sqlite3.connect(p)
        try:
            return chr(10).join(l for l in db.iterdump() if "built_seconds" not in l).encode()
        finally:
            db.close()
    return raw


def tree(root):
    """{relative path: sha256} of every file under root."""
    out = {}
    for dp, dn, fn in os.walk(root):
        for f in fn:
            p = os.path.join(dp, f)
            h = hashlib.sha256(_content(p, f)).hexdigest()
            out[os.path.relpath(p, root).replace(os.sep, "/")] = h
    return out


def leftovers(root):
    return sorted(p for p in tree(root) if ".part-" in p or p.endswith(".lock") or ".stale-" in p or p.endswith(".mreg-tmp"))


@unittest.skipIf(T._zstd is None, "needs Python 3.14 compression.zstd")
class Concurrent(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.mkdtemp(prefix="mreg-conc-")
        cls.reg = os.path.join(cls.tmp, "reg")
        cls.m = T.Mirror(cls.reg)
        cls.home = os.path.join(cls.tmp, "home")
        os.makedirs(cls.home)
        # PROCS entries over the chunks of the mathlib-like part: overlapping cones
        cls.entries = [entry(24 + (i * 7) % 46) for i in range(PROCS)]

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, True)

    def env(self, store):
        e = dict(os.environ, HOME=self.home, USERPROFILE=self.home, MREG_STORE=store, MREG_BACKOFF="0", MREG_RETRIES="1",
                 MREG_REGISTRY="file:///" + self.reg.replace("\\", "/").lstrip("/"), MREG_LOCK_WAIT="60")
        e.pop("MREG_TOKEN", None)
        return e

    def run_one(self, store, proj, ent, verify=True):
        os.makedirs(proj, exist_ok=True)
        with open(os.path.join(proj, "lean-toolchain"), "w") as f:
            f.write(T.TOOLCHAIN + "\n")
        res = {}
        for cmd in (["add", ent, "--train", T.TRAIN, "--json", "--allow-unverified"],) + ((["verify", "--json"],) if verify else ()):
            r = subprocess.run([sys.executable, "-I", MREG, "-C", proj] + cmd, capture_output=True, text=True, env=self.env(store),
                               creationflags=BELOW_NORMAL, timeout=300)
            res[cmd[0]] = (r.returncode, r.stdout, r.stderr)
        return res

    def single_process_store(self, entries):
        store = os.path.join(self.tmp, "single-store")
        shutil.rmtree(store, True)
        for i, ent in enumerate(entries):
            res = self.run_one(store, os.path.join(self.tmp, "single-proj", str(i)), ent, verify=False)
            self.assertEqual(res["add"][0], 0, res["add"][2] + res["add"][1][:300])
        return store

    def test_50_processes_share_one_store(self):
        store = os.path.join(self.tmp, "shared-store")
        t0 = time.time()
        with cf.ThreadPoolExecutor(AT_ONCE) as ex:
            futs = [ex.submit(self.run_one, store, os.path.join(self.tmp, "proj", str(i)), e) for i, e in enumerate(self.entries)]
            results = [f.result() for f in futs]
        secs = time.time() - t0
        print(f"\n{PROCS} processes, {AT_ONCE} at once: {secs:.1f} s", file=sys.stderr)
        for i, res in enumerate(results):
            a, v = res["add"], res["verify"]
            self.assertEqual(a[0], 0, (i, a[1][:400], a[2][:400]))
            self.assertEqual(v[0], 0, (i, v[1][:400], v[2][:400]))
            jv = json.loads(v[1])
            self.assertTrue(jv["ok"], jv)
            self.assertEqual((jv["mismatched"], jv["missing"], jv["extra"]), ([], [], []), (i, jv))
            idx = int(self.entries[i].split("Mathlib.n")[1].split("_")[0])
            cd = os.path.join(self.tmp, "proj", str(i), ".lake", "mreg-chunks", T.TRAIN)
            self.assertEqual(sorted(T.M.installed_chunk_files(cd)), self.m.cone(idx), i)
        self.assertEqual(leftovers(store), [])
        self.assertLess(secs, 60, "the plan asks for under a minute in total")
        ref = self.single_process_store(self.entries)
        got, want = tree(store), tree(ref)
        self.assertEqual(sorted(got), sorted(want))
        diff = [p for p in want if got[p] != want[p]]
        self.assertEqual(diff, [], "files that differ from the one-process store")
        self.assertTrue(any(p.startswith("index/") and p.endswith("READY.json") for p in got))
        self.assertTrue(any(p.startswith("objects/") for p in got))

    # ---- a writer that died
    def child(self, code):
        """Run `code` in a child python process that imports the client as M; returns the CompletedProcess."""
        pre = f"import importlib.util,os,sys\nsp=importlib.util.spec_from_file_location('m',{MREG!r});M=importlib.util.module_from_spec(sp);sp.loader.exec_module(M)\n"
        return subprocess.run([sys.executable, "-I", "-c", pre + code], capture_output=True, text=True, creationflags=BELOW_NORMAL, timeout=120)

    def test_killed_writers_leave_only_stale_files_and_the_next_run_recovers(self):
        store = os.path.join(self.tmp, "killed-store")
        ents = self.entries[:6]
        idxdir = os.path.join(store, "index", T.TRAIN)
        os.makedirs(idxdir)
        # 1. dies after writing the temporary file, before the rename: stale temp, no final file
        obj = os.path.join(store, "objects", "ab", "ab" + "0" * 62)
        r = self.child(f"M._replace=lambda s,d: os._exit(137)\nM.atomic_write({obj!r}, b'partial-or-whole')")
        self.assertEqual(r.returncode, 137, r.stderr)
        d = os.path.dirname(obj)
        stale_tmp = [x for x in os.listdir(d) if ".part-" in x]
        self.assertEqual(len(stale_tmp), 1)
        self.assertFalse(os.path.exists(obj), "a reader sees nothing, never a part")
        # 2. dies holding the index lock
        lockp = os.path.join(idxdir, self.m.build + ".lock")
        r = self.child(f"l=M.FileLock({lockp!r}).acquire()\nos._exit(137)")
        self.assertEqual(r.returncode, 137, r.stderr)
        self.assertTrue(os.path.exists(lockp))
        # 3. dies in the middle of building the index: a half-built directory named like the real ones
        half = os.path.join(idxdir, self.m.build + ".part-99999999-abc")        # pid 99999999 does not exist: a dead writer
        r = self.child(f"d={half!r}\nos.makedirs(d)\nopen(os.path.join(d,'manifest.tsv.gz'),'wb').write(b'x')\nos._exit(137)")
        self.assertEqual(r.returncode, 137, r.stderr)
        for nm in os.listdir(idxdir):               # make the leftovers older than the sweep's 5 s grace
            os.utime(os.path.join(idxdir, nm), (time.time() - 60, time.time() - 60))
        t0 = time.time()
        for i, e in enumerate(ents):
            res = self.run_one(store, os.path.join(self.tmp, "kproj", str(i)), e)
            self.assertEqual(res["add"][0], 0, res["add"][2] + res["add"][1][:400])
            self.assertEqual(res["verify"][0], 0, res["verify"][1][:400])
        self.assertLess(time.time() - t0, 60, "recovery did not wait out a lock timeout")
        self.assertEqual([p for p in leftovers(store) if "/objects/" not in "/" + p], [], "stale index lock, temp and half-built index are removed")
        ref = self.single_process_store(ents)
        got, want = tree(store), tree(ref)
        extra = sorted(set(got) - set(want))
        self.assertEqual([p for p in extra if not (p.startswith("objects/ab/") and ".part-" in p)], [])   # only the dead writer's temp object remains
        self.assertEqual([p for p in want if got.get(p) != want[p]], [])

    def test_a_live_lock_is_waited_for_then_gives_up(self):
        p = os.path.join(self.tmp, "live.lock")
        a = M.FileLock(p, wait=5).acquire()
        try:
            t0 = time.time()
            with self.assertRaises(TimeoutError):
                M.FileLock(p, wait=0.5).acquire()
            self.assertLess(time.time() - t0, 3)
        finally:
            a.release()
        self.assertFalse(os.path.exists(p))
        M.FileLock(p, wait=1).acquire().release()

    def test_old_lock_of_a_live_process_is_taken_over_by_age(self):
        p = os.path.join(self.tmp, "old.lock")
        a = M.FileLock(p).acquire()                # held by this (live) process
        os.utime(p, (time.time() - M.LOCK_STALE - 5,) * 2)
        b = M.FileLock(p, wait=2).acquire()        # judged stale by age
        b.release()
        a.release()                                # not ours any more: must not delete a newer lock
        self.assertFalse(os.path.exists(p))

    def test_lock_of_a_dead_process_is_taken_over(self):
        p = os.path.join(self.tmp, "dead.lock")
        r = self.child(f"M.FileLock({p!r}).acquire()\nos._exit(0)")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertTrue(os.path.exists(p))
        t0 = time.time()
        M.FileLock(p, wait=30).acquire().release()
        self.assertLess(time.time() - t0, 5)

    def test_unique_temporary_names_and_flush_then_replace(self):
        names = {M._tmp_name("x/y") for _ in range(1000)}
        self.assertEqual(len(names), 1000)
        self.assertTrue(all(n.startswith("x/y.part-%d-" % os.getpid()) for n in names))
        d = os.path.join(self.tmp, "aw")
        calls = []
        real = M._replace
        M._replace = lambda s, t: (calls.append((s, t, open(s, "rb").read())), real(s, t))[1]
        try:
            M.atomic_write(os.path.join(d, "f"), b"hello")
        finally:
            M._replace = real
        self.assertEqual(calls[0][2], b"hello", "the whole content is in the temporary file when it is renamed")
        self.assertEqual(os.listdir(d), ["f"])
        M.atomic_write(os.path.join(d, "f"), b"again")
        self.assertEqual(open(os.path.join(d, "f"), "rb").read(), b"again")

    def test_sweep_only_removes_dead_or_old_parts(self):
        d = os.path.join(self.tmp, "sw")
        os.makedirs(d)
        mine = os.path.join(d, "a.part-%d-1-ab" % os.getpid())
        dead = os.path.join(d, "b.part-99999999-1-ab")
        keep = os.path.join(d, "c.txt")
        for p in (mine, dead, keep):
            open(p, "w").write("x")
            os.utime(p, (time.time() - 60,) * 2)
        self.assertEqual(M.sweep_stale_parts(d), 1)
        self.assertEqual(sorted(os.listdir(d)), sorted(["a.part-%d-1-ab" % os.getpid(), "c.txt"]))


if __name__ == "__main__":
    unittest.main(verbosity=1)
