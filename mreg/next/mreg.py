#!/usr/bin/env python3
"""mreg v0: client of the mathregistry.com registry (private phase). Protocol: ../PROTOCOL_v0.md.

  mreg view <package id>                     what the registry holds for a package
  mreg train [<train>]                       a train's packages (default: the newest train)
  mreg init <dir> [--train T] [--name N]     new Lake project pinned to a train's Lean version
  mreg add <package id>[#<Decl.name>] [...]  require a package of the train (its commit on the train); with #Decl.name
                                             also record that declaration in mreg.json (installed module-level for now)
                                             a package in a repository subdirectory gets its Lake `subDir`; one with a path dependency pack
                                             also gets its other git dependencies pinned from the train build's signed lake-manifest.json
  mreg install [<Module.Name> ...] [--all] [--dry-run] [--check] [--no-rehash] [--train T] [--allow-source] [--allow-unverified]
                                             admission first: every build must pass the strict audit, else REFUSED (exit 4), nothing written
  mreg ci [--no-rehash] [--allow-unverified] install exactly what mreg.lock says (admission is run again), re-hash the installed files; any mismatch fails
  mreg verify                                re-hash the installed compiled files against the registry
  mreg audit [<id>[@<version>]] [--require G6,G8] [--json] [--strict|--lenient]
                                             check signature, reports and log of the locked (or named) builds; STRICT by default
                                             (signed, label clean or imported, every gate promotion requires); exit 1 on any failure
  mreg login [--provider github|google] [--label TEXT] [--no-browser] [--timeout S]
                                             sign in in the browser, create a per-user API key, store it in ~/.mreg/token
  mreg logout [--revoke]                     delete the stored key (--revoke: sign in again and revoke it at the service)
  mreg whoami                                what kind of key is stored (decoded locally, nothing printed that is secret)

`install` is by module. With no module named it takes what the project needs: every module its own sources import,
plus the project's own modules when the registry has a build of this exact commit. From those it follows imports
across every package in lake-manifest.json, Mathlib included, and downloads only the compiled modules in that
closure. `--all` takes every module of every package instead. An argument `owner/pkg#Decl.name` names a declaration: it is
resolved to the module that defines it (from the build's reports/graph.jsonl.zst) and that module's import closure is
installed. This is the module-level path (the module comes from a build that passed admission).

PATH DEPENDENCIES (0.6.4). A package in a repository subdirectory may name its own repository as a Lake path dependency (`path = "../.."`).
Lake checks the whole repository out to .lake/packages/<name> (the package is <clone>/<subDir>) and lists the dependency in the project's
lake-manifest.json as a path package inside that clone. The signed build manifest binds a pack of the dependency's compiled modules
(`path_dependencies`); `install` writes that pack into the checkout Lake made and nowhere else: the directory must be the one Lake resolved,
equal to the signed record, inside the clone, not .git or .lake, reached through no link, and the clone must be at the build's commit. The pack
is hash-checked (signed manifest -> nested manifest -> shard and index SHA-256 -> every file's SHA-256) before anything is written.
`verify`, `install --check` and `ci` re-hash it; mreg.lock records it under the package.

ADMISSION (0.5.0). Before anything is fetched or written, `install` and `ci` run the strict audit (the one `mreg audit` runs by
default: signed, label clean or imported, the gates that label needs pass, G7 run, signature, reports and log consistent) on every
registry build. A build that does not pass is REFUSED: exit 4, one line per package, nothing installed. `--allow-unverified` installs
it anyway, prints an UNVERIFIED banner, and mreg.lock records it as such (`admission`: proof_checked_under_policy false,
allowed_unverified true); `mreg audit` keeps showing it. Four statuses are kept apart and never merged into one word: `downloaded`
(the bytes were fetched), `hash_matched` (their SHA-256 equals the registry's recorded one), `compatible` (Lake's check passed; "not
checked" when it did not run) and `proof_checked_under_policy` (true only when the strict audit passed). The strict audit compares the
registry's records with each other; it does not re-check any proof here.
Declaration-level installs (`owner/pkg#Decl`) require a signed receipt covering the reduced proof environment and its source builds.
Compact declaration installs verify the current source gate reports and signed digests of supporting reports.
Use `mreg audit --strict` to download and hash every supporting report.
Older experimental stores require `--allow-unverified`. Use `--preserve-behavior` for source elaboration, tactics and execution
through the original checked modules.

Every byte is compared with the registry's own recorded SHA-256: package document -> manifest SHA-256 -> index file SHA-256 -> per-module frame SHA-256.
A hash match shows the bytes equal what the registry recorded. It is not a check of any proof, and importing a compiled file does not re-check its proofs.
Lake remains the judge: `--check` (always on in `ci`) ends with `lake build --no-build --rehash` on what was asked for.
Before that, `install --check` and `ci` re-hash every installed file of the packages they rely on against the registry's
recorded SHA-256 (the check `mreg verify` makes: a hash check, not a check of proofs), also for modules already installed, and fail (exit 1, `MISMATCH` lines)
on any difference. `--rehash` is Lake's own option and is the default because plain `--no-build` trusts the trace files;
it is not by itself a tamper check (a changed installed .olean was not flagged by it, 2026-11-13). `--no-rehash` keeps
the plain form. Plain `install` (without --check) and `--dry-run` re-hash nothing that is already installed.

`install` REFUSES (exit 4) when a dependency that a train holds is pinned in the project at a commit the registry has no
build for, naming the train's pin: left alone, Lake would compile that dependency from source (Mathlib: hours). The train
is `--train T`, else the newest train with the project's toolchain. `--allow-source` restores the old behaviour (the
dependency is left to Lake with a note); dependencies that no train holds are never refused.

Needs Python 3.10+, git, and Lake on PATH. zstd comes from Python 3.14, the `zstandard` module or the `zstd` program.
Token: environment MREG_TOKEN, or the file ~/.mreg/token. Registry: MREG_REGISTRY (default https://mathregistry.com),
or file:///<dir> (a directory with the registry's layout) or s3://<bucket> (no token for those two).

Signed builds (the package document says "signed": true) are checked against manifest.json.sig with a pure-Python
ECDSA P-256 verifier below. Signing keys are pinned per registry in ~/.mreg/keys.json (env MREG_KEYS names another
file). The first key a registry shows is pinned on first use (trust on first use: a `note: pinned signing key ...` line on
stderr says so; confirm the key id out of band). A DIFFERENT key later is refused unless --accept-new-key is given.
"""
import argparse, base64, contextlib, errno, hashlib, hmac, http.client, http.server, io, json, os, platform as _pf, re, select, socket, subprocess, sys, tarfile
import threading, time, webbrowser
import types as _types
import secrets as _secrets, socket as _sock, shutil
import urllib.error, urllib.parse, urllib.request
from concurrent.futures import ThreadPoolExecutor

VERSION = "0.6.6"
# THE ONE-LINE SWITCH (owner decided 2026-11-12, "Hand out, strict audit (Recommended)": strict is the default): True = `mreg audit` is strict unless `--lenient` is given;
# False = `mreg audit` is lenient (the 0.3 behaviour) unless `--strict` is given. Nothing else in the file reads a default.
AUDIT_STRICT_DEFAULT = True
# checker contract 1.2.0 (2026-11-13): when True (or MREG_REQUIRE_VIEWS=1 / --require-views), admission and audit also require the build's reports/verify.json to carry a `views` block with status pass
ADMISSION_REQUIRES_VIEWS = os.environ.get("MREG_REQUIRE_VIEWS", "").strip().lower() in ("1", "true", "yes")


def _admission_requires_views(a=None):
    if bool(getattr(a, "require_views", False)):
        return True
    v = os.environ.get("MREG_REQUIRE_VIEWS")
    if v is not None and v.strip() != "":
        return v.strip().lower() in ("1", "true", "yes")
    return bool(ADMISSION_REQUIRES_VIEWS)
# What the promotion rules require (promote/README.md 4, 4e, Imported builds). `clean`: G1 to G8 and G10 pass, G7 never "not run".
# `imported`: G1 is "not run" (the compile step was not re-run here), G2 to G10 pass.
AUDIT_LABELS = {"clean": ("G1", "G2", "G3", "G4", "G5", "G6", "G7", "G8", "G10"),
                "imported": ("G2", "G3", "G4", "G5", "G6", "G7", "G8", "G9", "G10")}
IMPORTED_MEANING = ("label imported = files compiled elsewhere, gated here (G2 to G10), a sample recompiled here and found identical; "
                    "the registry did not compile them all. It is not the label clean")
STATE = os.path.join(".lake", "mreg-state.json")
VERIFY_SCHEMA = "mreg-verify/1"     # module-level `verify --json` (added by the tamper fix; named-import documents keep NI_SCHEMA)
# Statuses the registry may answer with (T-C4). The name of the denial header is not final: it is kept in this one constant.
DENIAL_HEADER = "x-mreg-denial"
RETRY_AFTER_CAP = 30.0       # seconds: no single wait for a Retry-After (429, 503) is ever longer than this
DENIAL_MESSAGES = {
    "bad_signature": "the registry refused the access key: its signature is not valid (`mreg whoami`, then `mreg login` for a new key)",
    "revoked": "the registry refused the access key: it has been revoked (`mreg login` makes a new one)",
    "owner_blocked": "the registry refused the request: the owner of this key is blocked",
    "method_not_allowed": "the registry refused the request: this method is not allowed on that path",
}
DENIAL_KIND = {"bad_signature": "auth", "revoked": "auth", "owner_blocked": "auth", "method_not_allowed": "error"}


def denial_of(headers):
    """The denial kind named by the response header DENIAL_HEADER, or None when the header is absent or has a value not in the table
    (then the client behaves exactly as it did before the header existed)."""
    try:
        v = (headers.get(DENIAL_HEADER) or "").strip().lower() if headers is not None else ""
    except Exception:
        return None
    return v if v in DENIAL_MESSAGES else None


def retry_after_of(headers):
    """Seconds to wait from a Retry-After header (delta-seconds or an HTTP date), at most RETRY_AFTER_CAP, or None if absent or unreadable."""
    try:
        v = (headers.get("Retry-After") or "").strip() if headers is not None else ""
    except Exception:
        return None
    if not v:
        return None
    try:
        sec = float(v) if re.fullmatch(r"\d+(\.\d+)?", v) else None
        if sec is None:
            import email.utils
            dt = email.utils.parsedate_to_datetime(v)
            sec = dt.timestamp() - time.time()
    except Exception:
        return None
    return max(0.0, min(sec, RETRY_AFTER_CAP))


TAKEDOWN_MESSAGE = ("451 from the registry for {path}: the content was taken down (removed for legal reasons). "
                    "It will not come back by retrying; nothing was retried")
_TAKEDOWN = object()


GAP = 262144          # frames closer than this share one range request
WHOLE = 0.6           # above this share of a shard, download the whole shard


def die(msg):
    raise SystemExit("mreg: " + msg)


def token_path():
    return os.path.join(os.path.expanduser("~"), ".mreg", "token")


def read_token():
    """(value, source): MREG_TOKEN first, then ~/.mreg/token. (None, None) when there is none. Never print the value."""
    tok = os.environ.get("MREG_TOKEN")
    if tok:
        return tok, "environment variable MREG_TOKEN"
    p = token_path()
    if os.path.exists(p):
        try:
            tok = open(p, encoding="ascii", errors="replace").read().strip()
        except OSError as e:
            die(f"cannot read {p} ({e.strerror or type(e).__name__})")
        if tok:
            return tok, "file " + p
    return None, None


# ---------------------------------------------------------------- credential safety (T-C5)
# A key comes only from the environment (MREG_TOKEN) or the file ~/.mreg/token. It is refused on the command line and inside
# the registry address. Everything written to stdout, stderr, a SystemExit message or an unexpected exception passes `scrub`.
KEY_SHAPE = re.compile(r"mreg_[A-Za-z0-9_-]+\.[A-Za-z0-9_-]{43}")
CRED_LIKE = re.compile(r"mreg_[A-Za-z0-9_.-]{20,}")
REDACTED = "[redacted]"
_CRED_FLAG = re.compile(r"^--?(token|key|api-?key|access-?key|access-?token|auth|authorization|password|secret|credential)s?(=|$)", re.I)
_SECRETS = None          # the strings scrub removes: the stored key (environment or file) and keys or sign-in tokens met in this run
_EXTRA_SECRETS = []


def register_secret(v):
    if isinstance(v, str) and len(v) >= 8 and v not in _EXTRA_SECRETS:
        _EXTRA_SECRETS.append(v)


def _scrub_secrets():
    global _SECRETS
    if _SECRETS is None:
        out = []
        try:
            v = os.environ.get("MREG_TOKEN")
            if v:
                out.append(v)
            p = token_path()
            if os.path.isfile(p):
                with open(p, encoding="ascii", errors="replace") as f:
                    v = f.read().strip()
                if v and v not in out:
                    out.append(v)
        except Exception:
            pass
        _SECRETS = out
    return _SECRETS + _EXTRA_SECRETS


def scrub(s):
    """`s` with every key-shaped string (mreg_ and 20 or more key characters), the stored key, and any run of key characters that
    holds 20 consecutive characters of it, replaced by [redacted]."""
    if not isinstance(s, str) or not s:
        return s
    s = CRED_LIKE.sub("mreg_" + REDACTED, s)
    for tok in _scrub_secrets():
        if len(tok) < 8:
            continue
        s = s.replace(tok, REDACTED)
        if len(tok) >= 20:
            for i in range(len(tok) - 19):
                w = tok[i:i + 20]
                if w in s:
                    s = re.sub(r"[A-Za-z0-9_.+/=-]*" + re.escape(w) + r"[A-Za-z0-9_.+/=-]*", REDACTED, s)
    return s


class _ScrubWriter:
    """Wraps stdout and stderr for the length of `main`."""
    def __init__(self, inner):
        self._inner = inner

    def write(self, s):
        self._inner.write(scrub(s) if isinstance(s, str) else s)
        return len(s)

    def writelines(self, lines):
        for x in lines:
            self.write(x)

    def __getattr__(self, name):
        return getattr(self._inner, name)


def _key_like_arg(x):
    """True for an argument that is, or carries, something that looks like a key: it begins with `mreg_` (dotted or not, any length),
    or has `mreg_` straight after an `=` (`--x=mreg_...`), or holds a full key shape or 20 key characters after `mreg_` anywhere."""
    if x.startswith("mreg_"):
        return True
    if "=" in x and x.split("=", 1)[1].startswith("mreg_"):
        return True
    return bool(KEY_SHAPE.search(x) or CRED_LIKE.search(x))


def refuse_credential_in_args(argv):
    """A key on the command line shows in process lists and shell history: refused, and the argument is never echoed."""
    for x in argv:
        if _CRED_FLAG.match(x) or _key_like_arg(x):
            die("a key is never accepted on the command line (it would show in process lists and shell history). "
                "Set the environment variable MREG_TOKEN, or run `mreg login` to store one in ~/.mreg/token. Nothing was done")


def _addr_has_key_prefix(base):
    """`mreg_` at the start of any word of a network address (any length, dotted or not). Local file paths are not judged by this rule."""
    return re.search(r"(?<![A-Za-z0-9])mreg_", base) is not None


def registry_url_problem(base):
    """None, or why the registry address is refused: a key in the address would reach logs, proxies and history. The address is not echoed."""
    if base.startswith("s3://"):
        return "it contains a key" if _addr_has_key_prefix(base) else None
    pr = urllib.parse.urlparse(base)
    if pr.username is not None or pr.password is not None or "@" in pr.netloc:
        return "it has a user[:password]@ part"
    if "?" in base or "#" in base or pr.query or pr.fragment or pr.params:
        return "it has a ?query, #fragment or ;parameter"
    if KEY_SHAPE.search(base) or CRED_LIKE.search(base):
        return "it contains a key"
    if not base.startswith("file:") and _addr_has_key_prefix(base):
        return "it contains a key"
    return None


def check_registry_url(base):
    why = registry_url_problem(base)
    if why:
        die(f"MREG_REGISTRY is refused: {why}. The registry address is an address only; the key goes in MREG_TOKEN or ~/.mreg/token")


def _url_is_https_or_loopback(u):
    pr = urllib.parse.urlsplit(str(u or "").strip())
    if pr.scheme == "https" and bool(pr.hostname):
        return True
    if pr.scheme == "http" and (pr.hostname or "").lower() in ("127.0.0.1", "localhost", "::1"):
        return True
    return False


class _NoRedirectHandler(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        raise urllib.error.HTTPError(req.full_url, code, "redirects are not followed on auth/key endpoints", headers, fp)


class _SafeRegistryRedirectHandler(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        resolved = urllib.parse.urljoin(req.full_url, newurl)
        if not _url_is_https_or_loopback(resolved):
            raise urllib.error.HTTPError(resolved, code, "refusing redirect to insecure URL", headers, fp)
        new_req = super().redirect_request(req, fp, code, msg, headers, resolved)
        if new_req is None:
            return None
        src = urllib.parse.urlsplit(req.full_url)
        dst = urllib.parse.urlsplit(new_req.full_url)
        if (src.scheme.lower(), src.netloc.lower()) != (dst.scheme.lower(), dst.netloc.lower()):
            for hdrs in (new_req.headers, new_req.unredirected_hdrs):
                for hk in [h for h in list(hdrs) if h.lower() in ("x-mreg-token", "authorization")]:
                    del hdrs[hk]
        return new_req


def _no_redirect_open(req, timeout):
    return urllib.request.build_opener(_NoRedirectHandler()).open(req, timeout=timeout)


def _safe_redirect_open(req, timeout):
    return urllib.request.build_opener(_SafeRegistryRedirectHandler()).open(req, timeout=timeout)


def sha256(b):
    return hashlib.sha256(b).hexdigest()


def sha256_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


# ---------------------------------------------------------------- safe writes and locks (T-C3)
# Every write of a file another process may read (store objects, index tables, lock files, pins, the shard cache) goes to a temporary
# name made unique by process id, thread id and a random suffix, in the SAME directory, is flushed, and is renamed over the target with
# os.replace (atomic on POSIX and on Windows), so a reader sees the old file or the whole new one, never a part. A writer killed in the
# middle leaves only a `*.part-*` file, which no reader looks at and `sweep_stale_parts` removes.
LOCK_WAIT = 120.0       # seconds a process waits for another's lock before it gives up (MREG_LOCK_WAIT overrides)
LOCK_STALE = 900.0      # a lock file older than this many seconds is taken over even if its owner cannot be checked
PART_STALE = 3600.0     # a `*.part-*` file older than this many seconds, or one whose process is dead, is removed by a sweep


def _tmp_name(path):
    return f"{path}.part-{os.getpid()}-{threading.get_ident()}-{_secrets.token_hex(4)}"


def _replace(src, dst):
    """os.replace, retried for up to about 2 s when Windows refuses because another process has the target open or is replacing it."""
    for i in range(60):
        try:
            os.replace(src, dst)
            return
        except PermissionError:
            if i == 59:
                raise
            time.sleep(min(0.005 * (i + 1), 0.05))


def atomic_write(path, data):
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    tmp = _tmp_name(path)
    try:
        with open(tmp, "wb") as f:
            f.write(data)
            f.flush()
        _replace(tmp, path)
    finally:
        try:
            os.unlink(tmp)
        except OSError:
            pass


def read_file_retry(path):
    """The bytes of a file another process may be replacing right now: on Windows opening a file while it is being replaced is refused
    (PermissionError) for a few milliseconds, so the read is retried for up to about 2 s. FileNotFoundError is not retried."""
    for i in range(60):
        try:
            with open(path, "rb") as f:
                return f.read()
        except PermissionError:
            if i == 59:
                raise
            time.sleep(min(0.005 * (i + 1), 0.05))


def store_put(path, data):
    """Put a content-addressed object in the shared store. If the file is already there with exactly these bytes (another process was
    first) nothing is written: replacing a file that other processes are reading gains nothing. Otherwise `atomic_write`."""
    try:
        if os.path.getsize(path) == len(data) and read_file_retry(path) == data:
            return
    except OSError:
        pass
    atomic_write(path, data)


def atomic_write_text(path, text):
    atomic_write(path, text.encode("utf-8"))


def _pid_alive(pid):
    """Is process `pid` running on this machine? (Never os.kill on Windows: it terminates the process.)"""
    if pid <= 0:
        return False
    if sys.platform == "win32":
        import ctypes
        k = ctypes.WinDLL("kernel32", use_last_error=True)
        k.OpenProcess.restype = ctypes.c_void_p
        k.OpenProcess.argtypes = [ctypes.c_ulong, ctypes.c_int, ctypes.c_ulong]
        k.GetExitCodeProcess.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_ulong)]
        k.CloseHandle.argtypes = [ctypes.c_void_p]
        h = k.OpenProcess(0x1000, 0, pid)      # PROCESS_QUERY_LIMITED_INFORMATION
        if not h:
            return ctypes.get_last_error() == 5       # access denied: the process exists
        try:
            code = ctypes.c_ulong()
            return bool(k.GetExitCodeProcess(h, ctypes.byref(code))) and code.value == 259       # STILL_ACTIVE
        finally:
            k.CloseHandle(h)
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    except OSError:
        return False
    return True


_PART = re.compile(r"\.part-(\d+)-")


def sweep_stale_parts(d, older_than=PART_STALE):
    """Remove `<name>.part-<pid>-...` files left in directory d by a writer that died (its process is gone and the file is more than
    5 s old, or the file is older than `older_than`). Returns how many were removed. Never touches anything else."""
    n = 0
    try:
        names = os.listdir(d)
    except OSError:
        return 0
    now = time.time()
    for nm in names:
        m = _PART.search(nm)
        if not m:
            continue
        p = os.path.join(d, nm)
        try:
            age = now - os.path.getmtime(p)
            if age > older_than or (age > 5 and not _pid_alive(int(m.group(1)))):
                if os.path.isdir(p):
                    shutil.rmtree(p, ignore_errors=True)
                else:
                    os.unlink(p)
                n += 1
        except (OSError, ValueError):
            pass
    return n


class FileLock:
    """A lock file created with O_CREAT|O_EXCL, holding {"pid", "host", "t", "token"}. A lock whose process is dead (same host) or which
    is older than LOCK_STALE is taken over: it is first renamed to a unique name (only one taker can do that), and if the renamed file
    turns out not to be the one judged stale it is put back. Waiting is bounded by `wait` seconds, then TimeoutError."""

    def __init__(self, path, wait=None, stale=None):
        self.path = path
        self.wait = float(os.environ.get("MREG_LOCK_WAIT", LOCK_WAIT)) if wait is None else wait
        self.stale = LOCK_STALE if stale is None else stale
        self.token = _secrets.token_hex(8)

    def _read(self):
        try:
            with open(self.path, "rb") as f:
                return f.read()
        except OSError:
            return None

    def _is_stale(self, raw):
        try:
            age = time.time() - os.path.getmtime(self.path)
        except OSError:
            return False
        try:
            info = json.loads(raw)
            pid = int(info.get("pid", 0))
        except Exception:
            return age > 5          # unreadable: a writer that died between create and write
        if age > self.stale:
            return True
        return info.get("host") == _sock.gethostname() and not _pid_alive(pid)

    def _take_over(self, raw):
        brk = f"{self.path}.stale-{os.getpid()}-{_secrets.token_hex(4)}"
        try:
            os.replace(self.path, brk)
        except OSError:
            return
        try:
            got = open(brk, "rb").read()
        except OSError:
            got = None
        if got is not None and got != raw:       # not the lock judged stale: it was replaced meanwhile, put it back
            try:
                os.link(brk, self.path)
            except OSError:
                pass
        try:
            os.unlink(brk)
        except OSError:
            pass

    def acquire(self):
        os.makedirs(os.path.dirname(self.path) or ".", exist_ok=True)
        t_end = time.time() + self.wait
        delay = 0.01
        while True:
            try:
                fd = os.open(self.path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
            except (FileExistsError, PermissionError):      # PermissionError: Windows, the holder is deleting the file right now
                raw = self._read()
                if raw is not None and self._is_stale(raw):
                    self._take_over(raw)
                    continue
                if time.time() > t_end:
                    raise TimeoutError(f"gave up waiting {self.wait:.0f} s for the lock {self.path} held by another mreg process")
                time.sleep(delay)
                delay = min(delay * 1.5, 0.25)
                continue
            try:
                os.write(fd, json.dumps({"pid": os.getpid(), "host": _sock.gethostname(), "t": time.time(), "token": self.token}).encode())
            finally:
                os.close(fd)
            return self

    def release(self):
        raw = self._read()
        try:
            if raw is not None and json.loads(raw).get("token") != self.token:
                return          # taken over (it looked stale): not ours to delete
        except Exception:
            pass
        for _ in range(50):
            try:
                os.unlink(self.path)
                return
            except FileNotFoundError:
                return
            except PermissionError:
                time.sleep(0.01)

    def __enter__(self):
        return self.acquire()

    def __exit__(self, *a):
        self.release()


def unzstd(comp):
    try:
        from compression import zstd as z
        return z.decompress(comp)
    except ImportError:
        pass
    try:
        import zstandard   # the input may be several frames back to back
        return zstandard.ZstdDecompressor().stream_reader(io.BytesIO(comp), read_across_frames=True).read()
    except ImportError:
        return subprocess.run(["zstd", "-d", "-q", "-c"], input=comp, capture_output=True, check=True).stdout


def platform_triple():
    m = _pf.machine().lower()
    arch = {"amd64": "x86_64", "x86_64": "x86_64", "aarch64": "aarch64", "arm64": "aarch64"}.get(m, m)
    osn = {"linux": "unknown-linux-gnu", "darwin": "apple-darwin", "win32": "w64-windows-gnu"}.get(sys.platform, sys.platform)
    return f"{arch}-{osn}"


# ---------------------------------------------------------------- HTTP

class Registry:
    """The registry: https (token), file:///<dir> or s3://<bucket>[/<prefix>] (no token)."""

    def __init__(self, token=None):
        self.base = os.environ.get("MREG_REGISTRY", "https://mathregistry.com").rstrip("/")
        self.kind = "file" if self.base.startswith("file:") else "s3" if self.base.startswith("s3://") else "http"
        check_registry_url(self.base)
        self.tok, self.requests, self.bytes = None, 0, 0
        self.accept_new_key, self._keys, self._s3 = False, None, None
        if self.kind == "file":
            self.root = urllib.request.url2pathname(urllib.parse.urlparse(self.base).path)
        elif self.kind == "s3":
            self.bucket, _, pre = self.base[5:].partition("/")
            self.prefix = pre.strip("/") + "/" if pre.strip("/") else ""
        else:
            if not _url_is_https_or_loopback(self.base):
                die(f"MREG_REGISTRY must be an https address (http only for localhost), file:// or s3://: {self.base}")
            tok = token or read_token()[0]
            if not tok:
                die("no access token: run `mreg login`, or set MREG_TOKEN or create ~/.mreg/token")
            self.tok = tok

    def _local(self, path, rng):
        p = os.path.join(self.root, *[x for x in path.split("/") if x])
        with open(p, "rb") as f:
            if rng:
                f.seek(rng[0])
                return f.read(rng[1] - rng[0] + 1)
            return f.read()

    def _s3get(self, path, rng):
        key = self.prefix + path.lstrip("/")
        try:
            import boto3
        except ImportError:
            boto3 = None
        if boto3 is not None:
            if self._s3 is None:
                self._s3 = boto3.client("s3")
            kw = {"Range": f"bytes={rng[0]}-{rng[1]}"} if rng else {}
            try:
                return self._s3.get_object(Bucket=self.bucket, Key=key, **kw)["Body"].read()
            except Exception as e:
                if "NoSuchKey" in str(e) or "404" in str(e):
                    raise FileNotFoundError(path)
                raise
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            out = os.path.join(d, "obj")
            cmd = ["aws", "s3api", "get-object", "--bucket", self.bucket, "--key", key] + (
                ["--range", f"bytes={rng[0]}-{rng[1]}"] if rng else []) + [out]
            r = subprocess.run(cmd, capture_output=True, text=True)
            if r.returncode:
                if "NoSuchKey" in r.stderr or "Not Found" in r.stderr:
                    raise FileNotFoundError(path)
                raise IOError(r.stderr.strip()[:200])
            with open(out, "rb") as f:
                return f.read()

    def get(self, path, rng=None, missing_ok=False, takedown_ok=False):
        if self.kind != "http":
            try:
                self.requests += 1
                body = self._local(path, rng) if self.kind == "file" else self._s3get(path, rng)
            except (FileNotFoundError, NotADirectoryError):
                if missing_ok:
                    return None
                die(f"404 from the registry: {path}")
            except OSError as e:
                die(f"cannot read {path}: {e}")
            if rng and len(body) != rng[1] - rng[0] + 1:
                die(f"short read on {path}")
            self.bytes += len(body)
            return body
        h = {"x-mreg-token": self.tok, "User-Agent": "mreg/" + VERSION, "Accept-Encoding": "identity"}
        if rng:
            h["Range"] = f"bytes={rng[0]}-{rng[1]}"
        err = None
        for attempt in range(4):
            try:
                self.requests += 1
                with _safe_redirect_open(urllib.request.Request(self.base + path, headers=h), timeout=600) as r:
                    body = r.read()
                if rng and r.status == 200:
                    body = body[rng[0]:rng[1] + 1]
                if rng and len(body) != rng[1] - rng[0] + 1:
                    raise IOError(f"short read on {path}")
                self.bytes += len(body)
                return body
            except urllib.error.HTTPError as e:
                if e.code == 404 and missing_ok:
                    return None
                if e.code == 451:
                    if takedown_ok:
                        return _TAKEDOWN
                    die(TAKEDOWN_MESSAGE.format(path=path))
                if e.code in (301, 302, 303, 307, 308):
                    die(f"cannot fetch {path}: {e}")
                dn = denial_of(e.headers)
                if dn:
                    die(f"{e.code} from the registry for {path}: {DENIAL_MESSAGES[dn]}")
                if e.code == 403:
                    die(f"403 from the registry for {path}: the token is missing, wrong or revoked (`mreg whoami`, `mreg login`)")
                if e.code == 404:
                    die(f"404 from the registry: {path}")
                err = e
                if e.code in (429, 503):
                    ra = retry_after_of(e.headers)
                    if ra is not None:
                        time.sleep(ra)
                        continue
            except Exception as e:  # network trouble: try again
                err = e
            time.sleep(2 * (attempt + 1))
        die(f"cannot fetch {path}: {err}")

    def json(self, path, **kw):
        b = self.get(path, **kw)
        return None if b is None else json.loads(b)

    def keys(self):
        if self._keys is None:
            self._keys = self.json("/v1/index/keys.json", missing_ok=True) or {"keys": []}
        return self._keys


# ---------------------------------------------------------------- signatures: ECDSA P-256 / SHA-256, pure Python
# This block is a copy of promote/sign.py (verification half); promote/test_promote.py checks that both agree.
_P = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
_N = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
_B = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
_GX = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
_GY = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
_SPKI = bytes.fromhex("3059301306072a8648ce3d020106082a8648ce3d030107034200")


def _ec_add(a, b):
    if a is None or b is None:
        return b if a is None else a
    (x1, y1), (x2, y2) = a, b
    if x1 == x2:
        if (y1 + y2) % _P == 0:
            return None
        m = (3 * x1 * x1 - 3) * pow(2 * y1, -1, _P) % _P
    else:
        m = (y2 - y1) * pow(x2 - x1, -1, _P) % _P
    x3 = (m * m - x1 - x2) % _P
    return x3, (m * (x1 - x3) - y1) % _P


def _ec_mul(k, pt):
    r = None
    while k:
        if k & 1:
            r = _ec_add(r, pt)
        pt = _ec_add(pt, pt)
        k >>= 1
    return r


def _der_item(b, i, tag):
    if i + 2 > len(b) or b[i] != tag:
        raise ValueError("bad DER")
    n, j = b[i + 1], i + 2
    if n & 0x80:
        k = n & 0x7f
        if k == 0 or k > 2 or j + k > len(b) or b[j] == 0:
            raise ValueError("bad DER length")
        n, j = int.from_bytes(b[j:j + k], "big"), j + k
        if n < 128:
            raise ValueError("non-minimal DER length")
    if j + n > len(b):
        raise ValueError("DER truncated")
    return b[j:j + n], j + n


def _der_uint(c):
    if not c or (c[0] & 0x80) or (len(c) > 1 and c[0] == 0 and not c[1] & 0x80):
        raise ValueError("bad DER integer")
    return int.from_bytes(c, "big")


def parse_signature(der):
    body, end = _der_item(bytes(der), 0, 0x30)
    if end != len(der):
        raise ValueError("trailing bytes after the signature")
    rc, i = _der_item(body, 0, 0x02)
    sc, i = _der_item(body, i, 0x02)
    if i != len(body):
        raise ValueError("trailing bytes inside the signature")
    return _der_uint(rc), _der_uint(sc)


def pem_to_der(pem):
    m = re.fullmatch(r"\s*-----BEGIN PUBLIC KEY-----\s*([A-Za-z0-9+/=\s]+?)\s*-----END PUBLIC KEY-----\s*", pem or "")
    if not m:
        raise ValueError("not a PEM public key")
    return base64.b64decode("".join(m.group(1).split()), validate=True)


def spki_point(der):
    if len(der) != len(_SPKI) + 65 or not der.startswith(_SPKI) or der[len(_SPKI)] != 4:
        raise ValueError("not an uncompressed P-256 public key")
    x, y = int.from_bytes(der[-64:-32], "big"), int.from_bytes(der[-32:], "big")
    if not (0 <= x < _P and 0 <= y < _P and (y * y - (x * x * x - 3 * x + _B)) % _P == 0):
        raise ValueError("public key point is not on the curve")
    return x, y


def ec_verify_digest(pem, digest, sig_der):
    q = spki_point(pem_to_der(pem))
    if not isinstance(digest, (bytes, bytearray)) or len(digest) != 32:
        return False
    try:
        r, s = parse_signature(sig_der)
    except (ValueError, TypeError):
        return False
    if not (1 <= r < _N and 1 <= s < _N):
        return False
    w, e = pow(s, -1, _N), int.from_bytes(digest, "big")
    pt = _ec_add(_ec_mul(e * w % _N, (_GX, _GY)), _ec_mul(r * w % _N, q))
    return pt is not None and pt[0] % _N == r


def ec_verify(pem, message, sig_der):
    return ec_verify_digest(pem, hashlib.sha256(message).digest(), sig_der)


def sig_message(pid, version, key, msha, labels, promoted_at):
    return "\n".join(["mreg-sig-v1", pid, version, key, msha, ",".join(sorted(labels)), promoted_at, ""]).encode("utf-8")


def head_message(n, sha):
    return f"mreg-log-head-v1\n{n}\n{sha}\n".encode("utf-8")


REDACT_TAG = "mreg-log-redact-v1"


def redact_message(n, entry_sha256, prev, time_str, reason):
    return "\n".join([REDACT_TAG, str(n), entry_sha256, prev, time_str, reason, ""]).encode("utf-8")


def pins_path():
    return os.environ.get("MREG_KEYS") or os.path.join(os.path.expanduser("~"), ".mreg", "keys.json")


def pin_key(reg, key_id):
    """Key pinning, per registry address. Returns a problem string, or None when the key is pinned or was pinned now."""
    p = pins_path()
    try:
        with FileLock(p + ".lock"):          # read-modify-write of one shared file: one writer at a time
            pins = {"schema": "mreg-pins/1", "registries": {}}
            if os.path.exists(p):
                with open(p, encoding="utf-8") as f:
                    pins = json.load(f)
            ids = pins["registries"].setdefault(reg.base, {"key_ids": []})["key_ids"]
            if key_id in ids:
                return None
            if ids and not reg.accept_new_key:
                return (f"the registry's signing key {key_id} is not one pinned for {reg.base} (pinned: {', '.join(ids)}); "
                        "if the registry rotated its key on purpose, rerun with --accept-new-key")
            ids.append(key_id)
            atomic_write_text(p, json.dumps(pins, indent=1))
    except TimeoutError as e:
        die(str(e))
    print(f"note: pinned signing key {key_id} for {reg.base} in {p}", file=sys.stderr)
    return None


def key_pem(reg, key_id):
    """The PEM of a key of keys.json, after checking that key_id really is the hash of that key. (pem or None, problem)"""
    k = next((x for x in reg.keys().get("keys", []) if x.get("key_id") == key_id), None)
    if k is None:
        return None, f"signing key {key_id} is not in keys.json"
    try:
        if hashlib.sha256(pem_to_der(k["public_key_pem"])).hexdigest()[:16] != key_id:
            return None, f"keys.json: key {key_id} does not hash to its key_id"
        spki_point(pem_to_der(k["public_key_pem"]))
    except (ValueError, KeyError) as e:
        return None, f"keys.json: key {key_id} is malformed ({e})"
    return k["public_key_pem"], None


def check_signature(reg, pid, version, key, msha, sigraw):
    """(signature document or None, [problems]). Checks the fields, the signature and the key pin."""
    try:
        sg = json.loads(sigraw)
        if sg.get("schema") != "mreg-sig/1" or sg.get("alg") != "ECDSA_P256_SHA256":
            return None, ["manifest.json.sig: unknown schema or algorithm"]
        for f, want in (("id", pid), ("version", version), ("build_key", key), ("manifest_sha256", msha)):
            if sg.get(f) != want:
                return None, [f"manifest.json.sig is for another {f}: {sg.get(f)!r}, expected {want!r}"]
        labels, sigb = sg["labels"], base64.b64decode(sg["signature"], validate=True)
        if not isinstance(labels, list) or not isinstance(sg["promoted_at"], str):
            return None, ["manifest.json.sig: malformed fields"]
    except (ValueError, KeyError, TypeError, AttributeError):
        return None, ["manifest.json.sig is malformed"]
    pem, prob = key_pem(reg, sg.get("key_id"))
    if prob:
        return None, [prob]
    if not ec_verify(pem, sig_message(pid, version, key, msha, labels, sg["promoted_at"]), sigb):
        return None, ["the signature does not verify"]
    prob = pin_key(reg, sg["key_id"])
    return (None, [prob]) if prob else (sg, [])


# ---------------------------------------------------------------- the Lake project (same rules as lbc.py)

def read_manifest(d):
    p = os.path.join(d, "lake-manifest.json")
    return json.load(open(p, encoding="utf-8")) if os.path.exists(p) else None


def toolchain_of(d):
    return open(os.path.join(d, "lean-toolchain"), encoding="utf-8").read().strip()


def _safe_subdir(sub, who):
    """A git package's `subDir` from lake-manifest.json: relative, forward slashes, no `.` or `..` part."""
    if sub in (None, "", "."):
        return ""
    if (not isinstance(sub, str) or sub.startswith(("/", "\\")) or "\\" in sub or re.match(r"[A-Za-z]:", sub)
            or any(p in ("", ".", "..") for p in sub.split("/"))):
        die(f"{who}: unsafe subDir {sub!r} in lake-manifest.json")
    return sub


def clone_dir(proj, root, name):
    """The checkout Lake made of a git package: <packagesDir>/<name>. It is the repository root, also for a package with a subDir."""
    base = os.path.join(proj, root.get("packagesDir", ".lake/packages"))
    d, plain = os.path.join(base, name), os.path.join(base, name.strip("«»"))
    return d if os.path.isdir(d) or not os.path.isdir(plain) else plain


def package_dir(proj, root, name):
    """The directory of the Lake package: the project, a path dependency's `dir`, or a git package's checkout with its `subDir`
    (measured with Lake 2026-11-17: the clone is the whole repository, the package lives in <clone>/<subDir>)."""
    if name == root.get("name"):
        return proj
    for p in root.get("packages", []):
        if p.get("name") == name and p.get("type") == "path" and p.get("dir"):
            return os.path.normpath(os.path.join(proj, p["dir"]))
    d = clone_dir(proj, root, name)
    p = next((x for x in root.get("packages", []) if x.get("name") == name and x.get("type", "git") == "git"), None)
    sub = _safe_subdir((p or {}).get("subDir"), name)
    return os.path.join(d, *sub.split("/")) if sub else d


def git(d, *args):
    return subprocess.run(["git", "-C", d] + list(args), capture_output=True, text=True).stdout.strip()


def closure(proj, root, package):
    revs = {p["name"]: p.get("rev", "") for p in root.get("packages", [])}
    if package == root.get("name"):
        names, own = set(revs), (package, git(proj, "rev-parse", "HEAD"))
    else:
        pm = read_manifest(package_dir(proj, root, package)) or {}
        names, own = {p["name"] for p in pm.get("packages", [])}, (package, revs[package])
        if [n for n in names if n not in revs]:
            return None
    return sorted({(n, revs[n]) for n in names} | {own})


def source_changes(proj, root, cl):
    out = {}
    for name, _ in cl:
        if name == root.get("name"):
            continue
        d = package_dir(proj, root, name)
        if not (os.path.exists(os.path.join(d, ".git")) or os.path.exists(os.path.join(clone_dir(proj, root, name), ".git"))):
            continue                  # (a package with a subDir is checked out inside its repository's clone)
        spec = ["--", ".", ":(exclude).lake"]
        diff = subprocess.run(["git", "-C", d, "diff", "--binary", "HEAD"] + spec, capture_output=True).stdout
        unt = sorted(u for u in subprocess.run(["git", "-C", d, "ls-files", "--others", "--exclude-standard", "-z"] + spec,
                                               capture_output=True).stdout.split(b"\0") if u)
        if not diff and not unt:
            continue
        h = hashlib.sha256(diff)
        for u in unt:
            h.update(b"\0" + u + b"\0")
            with open(os.path.join(d, u.decode()), "rb") as f:
                h.update(f.read())
        out[name] = h.hexdigest()[:16]
    return out


def resolve_key(toolchain, cl, changes):
    s = f"mreg-resolve-key-v0\n{toolchain}\n" + json.dumps([list(x) for x in cl], separators=(",", ":"))
    if changes:
        s += "\nsource-changes:" + json.dumps(sorted(changes.items()), separators=(",", ":"))
    return sha256(s.encode())[:16]


def id_from_url(url, sub=""):
    m = re.match(r"(?:https?://github\.com/|git@github\.com:)([^/]+)/([^/]+?)(?:\.git)?/?$", (url or "").strip())
    return None if not m else f"{m.group(1)}/{m.group(2)}" + (f"/{sub.strip('/')}" if sub and sub not in (".", "") else "")


def parse_imports(path):
    try:
        text = open(path, encoding="utf-8", errors="replace").read()
    except OSError:
        return []
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    toks = "\n".join(line.split("--", 1)[0] for line in text.splitlines()).split()
    out, i = [], 0
    while i < len(toks) and toks[i] in ("module", "prelude"):
        i += 1
    while i < len(toks):
        j = i
        while j < len(toks) and toks[j] in ("public", "private", "meta"):
            j += 1
        if j >= len(toks) or toks[j] != "import":
            break
        j += 1
        while j < len(toks) and toks[j] in ("all", "runtime"):
            j += 1
        if j >= len(toks):
            break
        out.append(toks[j]); i = j + 1
    return out


def own_sources(proj):
    for dp, dns, fns in os.walk(proj):
        dns[:] = [d for d in dns if d not in (".lake", ".git")]
        for fn in fns:
            if fn.endswith(".lean") and fn != "lakefile.lean":
                yield os.path.join(dp, fn)


# ---------------------------------------------------------------- builds

def _artifact_parts(name):
    parts = name.split("/")
    if (parts[:2] != [".lake", "build"] or len(parts) < 3
            or any(not p or p in (".", "..") or p.endswith((" ", "."))
                   or any(ord(c) < 32 or c in '<>:"\\|?*' for c in p)
                   or re.fullmatch(r"(?:CON|PRN|AUX|NUL|CONIN\$|CONOUT\$|(?:COM|LPT)[1-9¹²³])(?:\..*)?",
                                   p, re.IGNORECASE) for p in parts)):
        die(f"refusing unsafe archive member {name!r}")
    return parts


@contextlib.contextmanager
def _frame_reader(compressed):
    try:
        from compression import zstd
    except ImportError:
        zstd = None
    if zstd is not None:
        with zstd.open(io.BytesIO(compressed), "rb") as stream:
            yield stream
        return
    try:
        import zstandard
    except ImportError:
        zstandard = None
    if zstandard is not None:
        with zstandard.ZstdDecompressor().stream_reader(io.BytesIO(compressed), read_across_frames=True) as stream:
            yield stream
        return
    # The portable CLI fallback streams stdout. Using a temporary input avoids
    # deadlocking on a full stdin pipe while the decoder writes a large frame.
    with _tempfile.TemporaryFile() as source:
        source.write(compressed)
        source.seek(0)
        with subprocess.Popen(["zstd", "-d", "-q", "-c"], stdin=source, stdout=subprocess.PIPE) as proc:
            try:
                with proc.stdout as stream:
                    yield stream
            finally:
                if proc.poll() is None and sys.exc_info()[0] is not None:
                    proc.kill()
            if proc.wait() != 0:
                die("invalid compressed registry frame")


def _artifact_directory(path):
    """Return a real directory, rejecting Windows junctions and other reparse points."""
    import stat
    value = os.lstat(path)
    if (not stat.S_ISDIR(value.st_mode) or
            getattr(value, "st_file_attributes", 0) & stat.FILE_ATTRIBUTE_REPARSE_POINT):
        die(f"refusing linked or non-directory archive destination: {path}")


def _write_archive_file(dest, parts, source, executable):
    parent = os.path.abspath(dest)
    os.makedirs(parent, exist_ok=True)
    _artifact_directory(parent)
    if os.name == "posix":
        # Anchor every lookup to an opened directory, including temporary-file
        # creation and replacement, so concurrent directory swaps cannot redirect writes.
        flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
        fd = os.open(parent, flags)
        try:
            for part in parts[:-1]:
                try:
                    os.mkdir(part, dir_fd=fd)
                except FileExistsError:
                    pass
                child = os.open(part, flags, dir_fd=fd)
                os.close(fd)
                fd = child
            tmp = _tmp_name(parts[-1])
            raw = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600, dir_fd=fd)
            try:
                with os.fdopen(raw, "wb") as out:
                    shutil.copyfileobj(source, out)
                    os.fchmod(out.fileno(), 0o755 if executable else 0o644)
                os.replace(tmp, parts[-1], src_dir_fd=fd, dst_dir_fd=fd)
            finally:
                try:
                    os.unlink(tmp, dir_fd=fd)
                except FileNotFoundError:
                    pass
        finally:
            os.close(fd)
        return
    for part in parts[:-1]:
        parent = os.path.join(parent, part)
        os.makedirs(parent, exist_ok=True)
        _artifact_directory(parent)
    out = os.path.join(parent, parts[-1])
    tmp = _tmp_name(out)
    with open(tmp, "xb") as temp:
        try:
            shutil.copyfileobj(source, temp)
        except BaseException:
            temp.close()
            os.unlink(tmp)
            raise
    try:
        os.chmod(tmp, 0o755 if executable else 0o644)
        _replace(tmp, out)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)

class Build:
    """One registry build of one package of the project."""

    def __init__(self, reg, lake_name, pid, version, key, manifest_sha256, dest, signed=None):
        """signed: True = the signature is required and must verify; False = the registry says unsigned (one warning);
        None = unknown (a lock written before signing): checked if the registry has a signature."""
        self.reg, self.lake_name, self.id, self.version, self.key, self.dest = reg, lake_name, pid, version, key, dest
        self.base = f"/v1/blobs/{pid}/-/{version}/{key}/"
        raw = reg.get(self.base + "manifest.json")
        if sha256(raw) != manifest_sha256:
            die(f"{pid}: manifest SHA-256 differs from the one recorded (expected {manifest_sha256[:16]}...)")
        self.manifest_sha256 = manifest_sha256
        self.path_deps, self.declared_changes = [], {}    # path dependency packs, source changes accepted through a bound rewrite
        self.signed, self.labels = False, []
        if signed is not False:
            sigraw = reg.get(self.base + "manifest.json.sig", missing_ok=True)
            if sigraw is None and signed:
                die(f"{pid} {version}: the registry says this build is signed but manifest.json.sig is missing")
            if sigraw is not None:
                sg, problems = check_signature(reg, pid, version, key, manifest_sha256, sigraw)
                if problems:
                    die(f"{pid} {version}: signature check failed: {problems[0]}")
                self.signed, self.labels = True, sg["labels"]
        if not self.signed:
            print(f"warning: {pid} {version}: this build is not signed; its bytes are checked against the registry's own "
                  "hashes only", file=sys.stderr)
        self.man = json.loads(raw)
        if self.man.get("schema") != "lean-build-manifest/2":
            die(f"{pid}: unknown manifest schema {self.man.get('schema')!r}")
        self.frames = [json.loads(l) for l in self._aux("shards/frames.jsonl").decode("utf-8").splitlines() if l.strip()]
        self.mods = {}
        for l in self._aux("shards/modules.jsonl").decode("utf-8").splitlines():
            if l.strip():
                e = json.loads(l); self.mods[e["module"]] = e["imports"]

    def _aux(self, rel):
        aux = self.man["aux_files"]
        if rel + ".zst" in aux:
            raw = self.reg.get(self.base + rel + ".zst")
            if sha256(raw) != aux[rel + ".zst"]["sha256"]:
                die(f"{self.id}: {rel}.zst does not match the manifest")
            return unzstd(raw)
        raw = self.reg.get(self.base + rel)
        if sha256(raw) != aux[rel]["sha256"]:
            die(f"{self.id}: {rel} does not match the manifest")
        return raw

    def extract_many(self, pairs, verified=False):
        """Verify frame hashes unless the shard is already verified, then unpack each frame within its declared size."""
        if not verified:
            for comp, fr in pairs:
                if len(comp) != fr["length"] or sha256(comp) != fr["sha256"]:
                    die(f"{self.id}: frame of {fr['module']} in {fr['shard']} does not match its SHA-256; refused, "
                        "nothing from it was written")
        n = 0
        for compressed, fr in pairs:
            remaining = fr["raw_length"]
            if type(remaining) is not int or remaining < 0:
                die(f"{self.id}: invalid frame size")
            with _tempfile.SpooledTemporaryFile(max_size=4 << 20) as raw, _frame_reader(compressed) as stream:
                while remaining:
                    block = stream.read(min(remaining, 1 << 20))
                    if not block:
                        die(f"{self.id}: incomplete compressed frame")
                    raw.write(block)
                    remaining -= len(block)
                if stream.read(1):
                    die(f"{self.id}: decompressed frame exceeds its declared size")
                raw.seek(0)
                n += self.extract(raw, fr)
        return n

    def extract(self, raw, fr):
        n = 0
        seen = set()
        with tarfile.open(fileobj=io.BytesIO(raw) if isinstance(raw, bytes) else raw, mode="r:") as tf:
            for m in tf:
                parts = _artifact_parts(m.name)
                key = m.name.casefold() if os.name == "nt" else m.name
                if not m.isreg() or m.sparse is not None or key in seen:
                    die(f"{self.id}: refusing unsafe archive member {m.name!r}")
                seen.add(key)
                with tf.extractfile(m) as source:
                    _write_archive_file(self.dest, parts, source, bool(m.mode & 0o100))
                n += 1
        if n != fr["files"]:
            die(f"{self.id}: frame of {fr['module']} held {n} files, the index says {fr['files']}")
        return n

    def fetch(self, modules, cache):
        """Download and unpack the frames of `modules` (None = all) plus the package-level frame. Returns counts."""
        sel = [fr for fr in self.frames if modules is None or fr["module"] is None or fr["module"] in modules]
        by = {}
        for fr in sel:
            by.setdefault(fr["shard"], []).append(fr)
        sizes = {s["name"]: s for s in self.man["shards"]}
        files = 0
        for sh, frs in sorted(by.items()):
            frs.sort(key=lambda f: f["offset"])
            if sum(f["length"] for f in frs) > WHOLE * sizes[sh]["bytes"]:
                p = os.path.join(cache, sizes[sh]["sha256"])
                if not (os.path.exists(p) and sha256_file(p) == sizes[sh]["sha256"]):
                    body = self.reg.get(self.base + sh)
                    if sha256(body) != sizes[sh]["sha256"]:
                        die(f"{self.id}: shard {sh} does not match its SHA-256; refused")
                    os.makedirs(cache, exist_ok=True)
                    atomic_write(p, body)
                with open(p, "rb") as f:   # the whole shard matched its SHA-256, so its frames need no second check
                    pairs = []
                    for fr in frs:
                        f.seek(fr["offset"]); pairs.append((f.read(fr["length"]), fr))
                files += self.extract_many(pairs, verified=True)
                continue
            runs, cur = [], None
            for fr in frs:
                if cur and fr["offset"] - cur[1] <= GAP:
                    cur[1] = fr["offset"] + fr["length"]; cur[2].append(fr)
                else:
                    cur = [fr["offset"], fr["offset"] + fr["length"], [fr]]; runs.append(cur)

            def do(run, sh=sh):
                body = self.reg.get(self.base + sh, rng=(run[0], run[1] - 1))
                return self.extract_many([(body[fr["offset"] - run[0]: fr["offset"] - run[0] + fr["length"]], fr) for fr in run[2]])

            with ThreadPoolExecutor(8) as ex:
                files += sum(ex.map(do, runs))
        for docname, hfield in (("LICENSE", "license_sha256"), ("NOTICE", "notice_sha256")):
            body = self.reg.get(self.base + docname, missing_ok=True)
            if body is not None:
                want_sha = self.man.get(hfield)
                if want_sha and sha256(body) != want_sha:
                    die(f"{self.id}: {docname} does not match the manifest")
                atomic_write(os.path.join(self.dest, docname), body)
        return {"frames": len(sel), "files": files, "bytes": sum(f["length"] for f in sel)}


def checkout_dirt(clone):
    """Lines of `git status` of the clone (untracked and ignored files included) outside every `.lake` directory: anything here is a local change."""
    r = subprocess.run(["git", "-C", clone, "status", "--porcelain", "--untracked-files=all", "--ignored", "-z"], capture_output=True)
    if r.returncode:
        return ["git status failed"]
    out = []
    for ent in r.stdout.decode("utf-8", "replace").split("\0"):
        path = ent[3:].replace("\\", "/")
        if ent and ".lake" not in path.split("/"):
            out.append(ent)
    return out


def bind_rewrite(reg, proj, name, pid, ver, entry, changed):
    """None when the rewrite the SIGNED manifest records for `entry` (the builder's toolchain bump and train-pin rewrite of the project's
    lake-manifest.json) is the one that turns this clean checkout into the project the build was made from; else the reason, as text.
    Guarantee: (1) the build is signed and on a train; (2) the clone is at the build's commit with no local change (tracked, untracked or ignored,
    outside .lake); (3) the package's own lake-manifest.json is byte-identical to the signed `from_sha256` and its lean-toolchain is the signed
    `toolchain.from`; (4) applying the signed revision changes (each `from` equal to the clone's revision, each `to` equal to the revision this
    project's Lake resolved) with the builder's own serialisation reproduces the signed `to_sha256`, which is the SHA-256 of the build's published
    lake-manifest.json, and the build's toolchain is `toolchain.to` and this project's. What is NOT re-derived: the `source_changes` digest itself,
    which also covers files the builder created in the repository and did not publish; every changed name must be a path package of this checkout."""
    base = f"/v1/blobs/{pid}/-/{ver}/{entry['build_key']}/"
    raw = reg.get(base + "manifest.json", missing_ok=True)
    if raw is None or sha256(raw) != entry["manifest"]["sha256"]:
        return "its manifest is missing or differs from the package document"
    man = json.loads(raw)
    rw = man.get("lake_manifest_rewrite")
    if not isinstance(rw, dict) or not all(isinstance(rw.get(k), str) and _HEX64.fullmatch(rw[k]) for k in ("from_sha256", "to_sha256")):
        return "the signed manifest records no lake-manifest rewrite"
    tc = rw.get("toolchain") or {}
    clone, pdir = clone_dir(proj.dir, proj.root, name), package_dir(proj.dir, proj.root, name)
    if man.get("commit") != proj.commit(name) or git(clone, "rev-parse", "HEAD") != man.get("commit"):
        return "the checkout is not at the build's commit"
    if set(man.get("source_changes") or {}) != changed or {n for n, _ in (tuple(c) for c in man.get("closure", []))} & changed != changed:
        return "the signed source changes name other packages than the path packages of this checkout"
    dirt = checkout_dirt(clone)
    if dirt:
        return "the checkout has local changes (" + "; ".join(d.strip() for d in dirt[:3]) + ")"
    lm_path = os.path.join(pdir, "lake-manifest.json")
    if not os.path.isfile(lm_path):
        return "the package has no lake-manifest.json"
    original = open(lm_path, "rb").read()
    if sha256(original) != rw["from_sha256"]:
        return "the package's lake-manifest.json is not the signed original"
    if tc and ((tc.get("from"), tc.get("to")) != (man.get("declared_toolchain"), man.get("toolchain"))
               or toolchain_of(pdir) != tc.get("from") or tc.get("to") != proj.toolchain):
        return "the toolchain before or after the signed rewrite does not match this checkout and project"
    m = json.loads(original)
    revs = {p["name"]: p.get("rev", "") for p in proj.root.get("packages", [])}
    done = set()
    for c in (rw.get("changes") or []):
        pk = next((x for x in m.get("packages", []) if x.get("name") == c.get("name") and x.get("type", "git") == "git"), None)
        if pk is None or pk.get("rev") != c.get("from") or revs.get(c["name"]) != c.get("to") or c["name"] in done:
            return f"the signed rewrite of {c.get('name')!r} is not original -> what Lake resolved"
        pk["rev"] = c["to"]
        done.add(c["name"])
    if not done and sha256(original) != rw["to_sha256"]:
        return "the signed rewrite has no changes but the manifest differs"
    if done and sha256((json.dumps(m, indent=2, ensure_ascii=False) + "\n").encode("utf-8")) != rw["to_sha256"]:
        return "applying the signed rewrite does not give the signed rewritten lake-manifest.json"
    if (man.get("aux_files") or {}).get("lake-manifest.json", {}).get("sha256") != rw["to_sha256"] or man.get("lake_manifest_sha256") != rw["to_sha256"]:
        return "the signed rewritten lake-manifest.json is not the one the manifest lists"
    return None


class Project:
    def __init__(self, d):
        self.dir = os.path.abspath(d)
        self.root = read_manifest(self.dir)
        if self.root is None:
            die("no lake-manifest.json here: run `lake update` (or `mreg add`) first")
        self.toolchain = toolchain_of(self.dir)
        self.platform = platform_triple()
        self.names = [self.root["name"]] + [p["name"] for p in self.root.get("packages", [])]

    def pid(self, name):
        if name == self.root["name"]:
            top = git(self.dir, "rev-parse", "--show-toplevel")
            sub = os.path.relpath(self.dir, top).replace(os.sep, "/") if top else ""
            # the URL as configured, not `git remote get-url`: that one applies url.<base>.insteadOf, which would turn a
            # GitHub address into whatever mirror the user's git configuration maps it to and lose the package identity
            url = git(self.dir, "config", "--get", "remote.origin.url") or git(self.dir, "remote", "get-url", "origin")
            return id_from_url(url, "" if sub == "." else sub)
        p = next(x for x in self.root["packages"] if x["name"] == name)
        return id_from_url(p.get("url"), p.get("subDir") or "")

    def in_checkout_path_deps(self, name):
        """Names of the path packages of the project whose directory lies inside the checkout Lake made of the git package `name`."""
        if name == self.root["name"] or not any(p.get("name") == name and p.get("type", "git") == "git" for p in self.root.get("packages", [])):
            return set()
        clone, out = os.path.abspath(clone_dir(self.dir, self.root, name)), set()
        for p in self.root.get("packages", []):
            if p.get("type") == "path" and isinstance(p.get("dir"), str) and p["dir"]:
                d = os.path.abspath(os.path.join(self.dir, p["dir"]))
                try:
                    if os.path.commonpath([clone, d]) == clone:
                        out.add(p["name"])
                except ValueError:
                    pass
        return out

    def commit(self, name):
        if name == self.root["name"]:
            return git(self.dir, "rev-parse", "HEAD")
        return next(x for x in self.root["packages"] if x["name"] == name).get("rev", "")

    def resolve(self, reg, any_platform=False, skip_root=False):
        """{lake name: Build} for every package the registry has a matching build of; and notes for the rest.
        skip_root: leave the project's own package out (a builder is about to compile it; its registry build, if any, is
        neither needed nor fetched, so an absent one cannot stop the install of the dependencies)."""
        builds, notes = {}, {}
        for name in self.names:
            if skip_root and name == self.root["name"]:
                continue
            pid = self.pid(name)
            if pid is None:
                notes[name] = "not a GitHub package"; continue
            doc = reg.json(f"/v1/index/{pid}.json", missing_ok=True)
            if doc is None:
                notes[name] = f"{pid} is not in the registry"; continue
            c = self.commit(name)
            ver = next((v for v, e in doc["versions"].items() if e["commit"] == c), None)
            if ver is None:
                notes[name] = f"{pid} has no version for commit {c[:12]}"; continue
            pdir = package_dir(self.dir, self.root, name)
            cl = closure(self.dir, self.root, name) if os.path.isdir(pdir) else None
            if cl is None:
                notes[name] = "not checked out (run `lake update`)"; continue
            changes = source_changes(self.dir, self.root, cl)
            rk = resolve_key(self.toolchain, cl, changes)
            cand = [b for b in doc["versions"][ver]["builds"] if b["resolve_key"] == rk]
            inpath = self.in_checkout_path_deps(name)
            bound, reasons = {}, []
            if not cand and inpath:
                # A package whose path dependency lies in its own checkout (teorth/IEANTN Solutions/CH2.v4). The builder's `source_changes` for that
                # path package is the digest of what it changed in the repository before building: its toolchain bump and the rewrite of the
                # project's lake-manifest.json to the train's pins (plus files of its own that are not published). A clean checkout has none of
                # that, so the digest cannot match. The build is taken only when the SIGNED manifest's recorded rewrite is bound to this checkout:
                # see bind_rewrite. Nothing else about the sources is relaxed: other packages' source changes still stop the match.
                for b in doc["versions"][ver]["builds"]:
                    sc = b.get("source_changes") or {}
                    if (b.get("signed") and b.get("trains") and sc and set(sc) <= inpath
                            and resolve_key(self.toolchain, cl, sc) == b["resolve_key"]):
                        why = bind_rewrite(reg, self, name, pid, ver, b, set(sc))
                        if why is None:
                            cand.append(b); bound[b["build_key"]] = dict(sc)
                        else:
                            reasons.append(f"build {b['build_key']} not taken: {why}")
            ok = [b for b in cand if any_platform or any(u["platform"] == self.platform for u in b["usable_on"])]
            if not ok:
                notes[name] = (f"{pid} {ver}: a build exists but the registry does not list it as usable on {self.platform} (use --any-platform)"
                               if cand else f"{pid} {ver}: no build for this toolchain and these dependency commits"
                               + (" (" + "; ".join(reasons) + ")" if reasons else ""))
                continue
            b = ok[0]
            builds[name] = Build(reg, name, pid, ver, b["build_key"], b["manifest"]["sha256"], pdir,
                                 signed=bool(b.get("signed")))
            builds[name].trains = list(b.get("trains") or [])      # for the one-train guard
            if b["build_key"] in bound:
                builds[name].declared_changes = bound[b["build_key"]]
            attach_path_deps(reg, self, name, builds[name])
        for b in builds.values():
            for d in b.path_deps:
                notes.pop(d.name, None)       # installed from the package's pack, not a package of its own
        return builds, notes


# ---------------------------------------------------------------- path dependencies of a registry build (2026-11-17)
# A package in a repository subdirectory can name its own repository as a Lake path dependency (`path = "../.."`; teorth/IEANTN
# Solutions/CH2.v4 does). The builder packs the compiled modules of such a dependency beside the package (`pathdeps/<name>/`) and the SIGNED
# manifest binds that pack: `path_dependencies[]` = name, dir, build_key, manifest_sha256 of pathdeps/<name>/manifest.json, index_sha256 of
# pathdeps/<name>/shards/index.jsonl. Lake (measured 2026-11-17) clones the whole repository to <packagesDir>/<lake name>, puts the package at
# <clone>/<subDir> and lists the dependency in the consumer's lake-manifest.json as a path package whose `dir` resolves into that clone.
# The client writes the pack into that directory and nowhere else. Trust chain: signature -> top manifest -> nested manifest sha -> shard sha
# and index sha -> every extracted file's sha against the index. The nested frames.jsonl and modules.jsonl are not pinned by the signature, so
# they are never trusted: frames are not used at all (the whole shard is read), modules.jsonl only chooses which Mathlib modules to fetch.

PATHDEP_SCHEMAS = ("lean-build-manifest/1", "lean-build-manifest/2")


def path_dep_entries(man, who):
    """The validated `path_dependencies` of a signed build manifest."""
    out, seen = [], set()
    for e in man.get("path_dependencies") or []:
        ok = (isinstance(e, dict) and all(isinstance(e.get(k), str) for k in ("name", "dir", "build_key", "path", "manifest_sha256", "index_sha256"))
              and _NAME_OK.fullmatch(e["name"]) and e["path"] == f"pathdeps/{e['name']}/" and e["name"] not in seen
              and _HEX64.fullmatch(e["manifest_sha256"]) and _HEX64.fullmatch(e["index_sha256"]))
        if not ok:
            die(f"{who}: malformed path_dependencies entry in the signed manifest; refused, nothing written")
        seen.add(e["name"])
        out.append(e)
    return out


def path_dep_target(proj, parent, e):
    """Where the dependency's compiled files go: the directory Lake resolved for the path dependency, shown to lie inside the pinned
    checkout (the clone Lake made of the package that needs it) and to be the one the signed build records. Dies, writing nothing, else."""
    who = f"{parent}: path dependency {e['name']}"
    entry = next((p for p in proj.root.get("packages", []) if p.get("name") == e["name"] and p.get("type") == "path"), None)
    if entry is None or not isinstance(entry.get("dir"), str) or not entry["dir"]:
        die(f"{who}: Lake's manifest has no path dependency of that name (run `lake update`); refused, nothing written")
    clone, pdir = clone_dir(proj.dir, proj.root, parent), package_dir(proj.dir, proj.root, parent)
    if os.path.islink(clone) or not os.path.isdir(clone):
        die(f"{who}: the checkout {clone} is not a real directory; refused, nothing written")
    dest = os.path.normpath(os.path.join(proj.dir, entry["dir"]))
    if os.path.isabs(e["dir"]) or dest != os.path.normpath(os.path.join(pdir, e["dir"])):
        die(f"{who}: Lake resolved it to {dest}, the signed build records dir {e['dir']!r} from {pdir}; refused, nothing written")
    rel = os.path.relpath(os.path.abspath(dest), os.path.abspath(clone))
    parts = [] if rel == "." else rel.split(os.sep)
    if os.pardir in parts or os.path.isabs(rel) or (parts and parts[0] in (".git", ".lake")):
        die(f"{who}: {dest} is not inside the pinned checkout {clone} (or is its .git or .lake); refused, nothing written")
    rc = os.path.realpath(clone)
    if os.path.normcase(os.path.realpath(dest)) != os.path.normcase(os.path.normpath(os.path.join(rc, *parts))):
        die(f"{who}: {dest} reaches outside the checkout through a link; refused, nothing written")
    if not os.path.isdir(dest):
        die(f"{who}: {dest} is not a directory (run `lake update`); refused, nothing written")
    return dest


class _CapRead:
    """Reads at most `cap` bytes of a decompressed stream; one more byte is an error (a frame that grows past its declared size)."""

    def __init__(self, f, cap, who):
        self.f, self.left, self.who = f, cap, who

    def read(self, n=-1):
        if n is None or n < 0 or n > self.left + 1:
            n = self.left + 1
        b = self.f.read(n)
        self.left -= len(b)
        if self.left < 0:
            die(f"{self.who}: the shard decompresses to more than its declared size; refused, nothing written")
        return b


class PathDep:
    """One path dependency pack of one registry build, authenticated against the signed manifest before anything is written."""

    def __init__(self, reg, proj, parent, build, e):
        self.dest = path_dep_target(proj, parent, e)
        clone = clone_dir(proj.dir, proj.root, parent)
        if not build.man.get("commit") or git(clone, "rev-parse", "HEAD") != build.man["commit"]:
            die(f"{build.id}: the checkout {clone} is not at the build's commit {str(build.man.get('commit'))[:12]}; refused, nothing written")
        self.parent = parent
        self._load(reg, build, e, navigation=True)

    @classmethod
    def for_checking(cls, reg, build, entry):
        """Read only authenticated metadata. The checker supplies its temporary extraction directory."""
        if entry not in path_dep_entries(build.man, build.id):
            die(f"{build.id}: path dependency is absent from its signed manifest")
        dep = cls.__new__(cls)
        dep.dest = None
        dep.parent = None
        dep._load(reg, build, entry, navigation=False)
        return dep

    def _load(self, reg, build, e, navigation):
        self.reg, self.build, self.e, self.name = reg, build, e, e["name"]
        self.who = f"{build.id} {build.version}: path dependency {self.name}"
        self.base = build.base + e["path"]
        raw = reg.get(self.base + "manifest.json")
        if sha256(raw) != e["manifest_sha256"]:
            die(f"{self.who}: manifest.json does not match the SHA-256 in the signed manifest; refused, nothing written")
        self.man = json.loads(raw)
        for k in ("commit", "toolchain", "platform"):
            if self.man.get(k) != build.man.get(k):
                die(f"{self.who}: its manifest says {k} {self.man.get(k)!r}, the build's says {build.man.get(k)!r}; refused")
        if self.man.get("schema") not in PATHDEP_SCHEMAS or self.man.get("build_key") != e["build_key"]:
            die(f"{self.who}: its manifest has another schema or build key than the signed manifest records; refused")
        shards = self.man.get("shards")
        if (not isinstance(shards, list) or not shards or not all(
                isinstance(s, dict) and isinstance(s.get("name"), str) and isinstance(s.get("bytes"), int) and isinstance(s.get("bytes_uncompressed"), int)
                and isinstance(s.get("sha256"), str) and _HEX64.fullmatch(s["sha256"]) for s in shards)):
            die(f"{self.who}: its shard list is malformed; refused")
        self.shards = {s["name"]: s for s in shards}
        if (len(self.shards) != len(shards) or any(not re.fullmatch(r"shards/[A-Za-z0-9_.-]+\.tar\.zst", n)
                or s["bytes"] <= 0 or s["bytes_uncompressed"] <= 0 for n, s in self.shards.items())):
            die(f"{self.who}: malformed or repeated signed shard path")
        raw = reg.get(self.base + "shards/index.jsonl")
        if sha256(raw) != e["index_sha256"]:
            die(f"{self.who}: shards/index.jsonl does not match the SHA-256 in the signed manifest; refused, nothing written")
        self.index, mods = {}, set()
        for line in raw.decode("utf-8").splitlines():
            if not line.strip():
                continue
            r = json.loads(line)
            if (not isinstance(r, dict) or not isinstance(r.get("path"), str) or not isinstance(r.get("sha256"), str) or not _HEX64.fullmatch(r["sha256"])
                    or not isinstance(r.get("bytes"), int) or r.get("shard") not in self.shards or r["path"] in self.index):
                die(f"{self.who}: malformed or repeated entry in shards/index.jsonl; refused")
            _artifact_parts(r["path"])
            self.index[r["path"]] = r
            if isinstance(r.get("module"), str):
                mods.add(r["module"])
        if not self.index:
            die(f"{self.who}: the pack lists no files; refused")
        # imports: navigation only (not pinned by the signature); a malformed line means "unknown", and an unknown import list takes everything
        self.mods = {m: None for m in mods}
        if not navigation:
            self.mods = dict.fromkeys(self.checked_modules())
            return
        raw = reg.get(self.base + "shards/modules.jsonl", missing_ok=True)
        for line in (raw or b"").decode("utf-8", "replace").splitlines():
            try:
                r = json.loads(line)
                if r["module"] in self.mods and isinstance(r["imports"], list) and all(isinstance(i, str) for i in r["imports"]):
                    self.mods[r["module"]] = r["imports"]
            except (ValueError, KeyError, TypeError):
                continue

    def checked_modules(self):
        """Module names with a compiled .olean at their canonical signed index path."""
        return {r["module"] for r in self.index.values() if isinstance(r.get("module"), str)
                and r["path"] == ".lake/build/lib/lean/" + r["module"].replace(".", "/") + ".olean"}

    def record(self, proj):
        return {"build_key": self.e["build_key"], "manifest_sha256": self.e["manifest_sha256"], "index_sha256": self.e["index_sha256"],
                "dest": os.path.relpath(self.dest, proj.dir).replace(os.sep, "/"), "files": len(self.index)}

    def _members(self, body, sname):
        """(member name, parts, executable, file object) of every member of a shard, each one in the index, none twice."""
        s = self.shards[sname]
        seen = set()
        with _frame_reader(body) as stream:
            with tarfile.open(fileobj=_CapRead(stream, s["bytes_uncompressed"], self.who), mode="r|", ignore_zeros=True) as tf:
                for m in tf:
                    r = self.index.get(m.name)
                    key = m.name.casefold() if os.name == "nt" else m.name
                    if r is None or r["shard"] != sname or not m.isreg() or m.sparse is not None or key in seen or m.size != r["bytes"]:
                        die(f"{self.who}: unexpected archive member {m.name!r}; refused, nothing written")
                    seen.add(key)
                    with tf.extractfile(m) as f:
                        yield m.name, _artifact_parts(m.name), bool(m.mode & 0o100), f

    def prepare(self):
        """Download every shard and verify the whole pack against the pinned index. Nothing is written; call before anything else is."""
        bodies = {}
        for name, s in sorted(self.shards.items()):
            body = self.reg.get(self.base + name)
            if len(body) != s["bytes"] or sha256(body) != s["sha256"]:
                die(f"{self.who}: shard {name} does not match its SHA-256; refused, nothing written")
            bodies[name] = body
        got = set()
        for name, body in bodies.items():            # every member's bytes against the pinned index
            for path, _parts, _x, f in self._members(body, name):
                h = hashlib.sha256()
                for block in iter(lambda: f.read(1 << 20), b""):
                    h.update(block)
                if h.hexdigest() != self.index[path]["sha256"]:
                    die(f"{self.who}: {path} does not match the index SHA-256; refused, nothing written")
                got.add(path)
        if got != set(self.index):
            die(f"{self.who}: the shards lack {len(set(self.index) - got)} file(s) the index lists; refused, nothing written")
        self._bodies = bodies

    def install(self):
        """Write the verified pack into the checkout (prepare() first). Returns the file count."""
        if self.dest is None:
            die(f"{self.who}: a checking destination is required")
        n = 0
        for name, body in self._bodies.items():
            for _path, parts, x, f in self._members(body, name):
                _write_archive_file(self.dest, parts, f, x)
                n += 1
        self._bodies = None
        return n

    def rehash(self):
        """[(path, state)] of the installed files: 'ok', 'missing', 'differs'."""
        out = []
        for path, r in self.index.items():
            p = os.path.join(self.dest, *path.split("/"))
            out.append((path, "ok" if os.path.isfile(p) and sha256_file(p) == r["sha256"] else "differs" if os.path.exists(p) else "missing"))
        return out


def attach_path_deps(reg, proj, name, b):
    """Authenticate and plan the path dependency packs of a registry build of package `name` (not the project's own package)."""
    b.path_deps = []
    ents = path_dep_entries(b.man, b.id)
    if not ents:
        return
    if name == proj.root["name"]:
        print(f"note: {b.id} names path dependenc{'y' if len(ents) == 1 else 'ies'} {', '.join(e['name'] for e in ents)}; the project's own package "
              "is not built from the registry here, so they are left to Lake", file=sys.stderr)
        return
    b.path_deps = [PathDep(reg, proj, name, b, e) for e in ents]


def plan(proj, builds, targets, take_all, extra=(), only_named=False, deps_out=None):
    """{lake name: set of modules, or None for all}, plus the list of requested modules and unresolved names.
    extra: modules that declarations resolved to; they are added to the targets. only_named: the install is exactly what
    was named (modules and declarations), so an empty `targets` does not fall back to the project's own imports.
    deps_out: a set that receives the modules of path dependency packs the closure reaches (they are installed whole, not by module)."""
    owner = {m: n for n, b in builds.items() for m in b.mods}
    dep_imps = {m: imps for b in builds.values() for d in getattr(b, "path_deps", ()) for m, imps in d.mods.items()}
    if take_all:
        if deps_out is not None:
            deps_out |= set(dep_imps)
        return {n: None for n in builds}, sorted(set(owner) | set(dep_imps)), []
    if not targets and not only_named:
        targets = set()
        if proj.root["name"] in builds:
            targets |= set(builds[proj.root["name"]].mods)
        for src in own_sources(proj.dir):
            targets |= set(parse_imports(src))
        targets = sorted(t for t in targets if t in owner or t in dep_imps)
    if extra:
        targets = list(targets) + [m for m in extra if m not in targets]
    need, todo, missing, seen_dep = set(), list(targets), [], set()
    while todo:
        m = todo.pop()
        if m in need or m in seen_dep:
            continue
        if m in dep_imps:
            seen_dep.add(m)
            if dep_imps[m] is None:
                if deps_out is not None:
                    deps_out |= set(dep_imps)
                return {n: None for n in builds}, list(targets), missing   # imports unknown: take all
            todo += dep_imps[m]
            continue
        if m not in owner:
            if m in targets:
                missing.append(m)
            continue
        need.add(m)
        imps = builds[owner[m]].mods[m]
        if imps is None:
            if deps_out is not None:
                deps_out |= seen_dep
            return {n: None for n in builds}, list(targets), missing   # a module without a parsed header: take all
        todo += imps
    if deps_out is not None:
        deps_out |= seen_dep
    return {n: {m for m in need if owner[m] == n} for n in builds}, list(targets), missing


# ---------------------------------------------------------------- declarations (plan 2a)
# The unit a consumer names is the declaration. The registry cannot serve declaration-level bundles yet, so a declaration
# is resolved to the module that defines it (reports/graph.jsonl.zst of the build) and that module's import closure is
# installed as for any module. Only resolve_declarations()/find_decl() know the graph; a later declaration-level fetch
# replaces the fetch step in do_install (what turns `want` into downloaded frames), not these.

GRAPH = "reports/graph.jsonl.zst"
DECL_RE = re.compile(r"^([^/\s#]+/[^\s#]+)#([^\s#]+)$")
LOCK_SCHEMAS = ("mreg-lock/0", "mreg-lock/1")


def parse_decl(entry):
    """'owner/pkg#Decl.name' -> (package id, declaration name); None when the text is not of that form."""
    m = DECL_RE.match(entry or "")
    return (m.group(1), m.group(2)) if m else None


def load_graph_text(reg, base, man, who):
    """The build's declaration graph as text, after checking it against the SHA-256 the manifest lists."""
    rep = man.get("reports") or {}
    if GRAPH not in rep:
        die(f"{who}: this build has no declaration graph ({GRAPH}), so a declaration cannot be resolved; "
            "name a module instead: mreg install <Module.Name>")
    raw = reg.get(base + GRAPH, missing_ok=True)
    if raw is None:
        die(f"{who}: the manifest lists {GRAPH} but the registry does not hold it")
    if sha256(raw) != rep[GRAPH]:
        die(f"{who}: {GRAPH} does not match the manifest's SHA-256; refused")
    return unzstd(raw).decode("utf-8")


def find_decl(text, name, who, mods=None):
    """The one `decl` record of the graph with exactly this name. Unknown, ambiguous and helper names are errors."""
    needles = {name, json.dumps(name)[1:-1], json.dumps(name, ensure_ascii=False)[1:-1]}
    exact, near = [], []
    for line in text.splitlines():
        if not any(n in line for n in needles):
            continue
        try:
            r = json.loads(line)
        except ValueError:
            continue
        if not isinstance(r, dict) or r.get("t") != "decl" or not isinstance(r.get("name"), str):
            continue
        if r["name"] == name:
            exact.append(r)
        elif r["name"].endswith("." + name) or r["name"].lower() == name.lower():
            near.append(r["name"])
    if not exact:
        hint = f" (did you mean {', '.join(sorted(set(near))[:5])}?)" if near else ""
        die(f"{who}: no declaration named {name!r} in this build's graph{hint}; that is all this answer says: the name may exist in "
            "another build, version or train")
    if len(exact) > 1:
        die(f"{who}: the name {name!r} is ambiguous: defined in " + ", ".join(sorted({str(r.get('module')) for r in exact})))
    r = exact[0]
    if r.get("helper"):
        die(f"{who}: {name} is a generated helper ({r.get('helper_why', 'helper')}); name the declaration that uses it")
    if not isinstance(r.get("module"), str) or (mods is not None and r["module"] not in mods):
        die(f"{who}: the graph puts {name} in module {r.get('module')!r}, which the build does not contain")
    return r


def decl_record(entry, pid, lake_name, r):
    return {"entry": entry, "id": pid, "lake_name": lake_name, "name": r["name"], "module": r["module"],
            "kind": r.get("kind"), "th": r.get("th")}


def resolve_declarations(builds, entries):
    """[decl records] for 'owner/pkg#Decl.name' entries, using the hash-matched builds an install fetched."""
    by_id = {b.id: (n, b) for n, b in builds.items()}
    out, graphs, seen = [], {}, set()
    for entry in entries:
        if entry in seen:
            continue
        seen.add(entry)
        pd = parse_decl(entry)
        if pd is None:
            die(f"{entry!r}: expected owner/pkg#Decl.name")
        pid, name = pd
        if pid not in by_id:
            die(f"{entry}: no registry build of {pid} matches this project (see the notes above); cannot resolve a declaration")
        lake, b = by_id[pid]
        who = f"{pid} {b.version} (build {b.key}, manifest sha256 {b.manifest_sha256})"
        if pid not in graphs:
            graphs[pid] = load_graph_text(b.reg, b.base, b.man, who)
        out.append(decl_record(entry, pid, lake, find_decl(graphs[pid], name, who, b.mods)))
    return out


def train_declaration(reg, train, pid, pkg, name):
    """`mreg add` time check: the declaration exists in the graph of the train's build of the package. The install
    resolves it again against the hash-matched build; this only stops a typo from being recorded."""
    doc = reg.json(f"/v1/index/{pid}.json", missing_ok=True)
    if doc is None:
        die(f"{pid} is not in the registry")
    builds = (doc["versions"].get(pkg["version"]) or {}).get("builds") or []
    b = next((x for x in builds if train["train"] in (x.get("trains") or [])), builds[0] if builds else None)
    if b is None:
        die(f"{pid} {pkg['version']}: the registry has no build")
    base = f"/v1/blobs/{pid}/-/{pkg['version']}/{b['build_key']}/"
    raw = reg.get(base + "manifest.json")
    if sha256(raw) != b["manifest"]["sha256"]:
        die(f"{pid}: manifest SHA-256 differs from the package document's")
    man = json.loads(raw)
    who = f"{pid} {pkg['version']} (build {b['build_key']}, manifest sha256 {b['manifest']['sha256']})"
    return decl_record(f"{pid}#{name}", pid, pkg["lake_name"], find_decl(load_graph_text(reg, base, man, who), name, who))


def cone_size(builds, want):
    """(modules, compressed bytes, packages) that the frames of `want` (from plan) come to."""
    n = size = pk = 0
    for name, b in builds.items():
        mods = want.get(name)
        sel = set(b.mods) if mods is None else mods
        if not sel:
            continue
        pk += 1
        n += len(sel)
        size += sum(f["length"] for f in b.frames if f["module"] in sel or f["module"] is None)
    return n, size, pk


def human_bytes(n):
    return f"{n} B" if n < 1000 else f"{n/1e3:.1f} kB" if n < 1e6 else f"{n/1e6:.1f} MB" if n < 1e9 else f"{n/1e9:.2f} GB"


def load_cfg(d):
    p = os.path.join(d, "mreg.json")
    return json.load(open(p, encoding="utf-8")) if os.path.exists(p) else {}


def load_state(proj):
    p = os.path.join(proj.dir, STATE)
    return json.load(open(p, encoding="utf-8")) if os.path.exists(p) else {"packages": {}}


def lake_check(proj, targets, whole_root, rehash, skip=False):
    """`lake build --no-build [--rehash]`; rehash is the caller's choice (the commands default it to on)."""
    if skip:
        print("lake build --no-build: SKIPPED (--no-lake-check); Lake has not judged this install")
        return 0
    cmd = ["lake", "build", "--no-build"] + (["--rehash"] if rehash else [])
    if not whole_root:
        cmd += ["+" + t for t in targets]
    r = subprocess.run(cmd, cwd=proj.dir, capture_output=True, text=True, env=dict(os.environ, MATHLIB_NO_CACHE_ON_UPDATE="1"))
    tail = [l for l in (r.stdout + r.stderr).splitlines() if l.strip()][-1:] or [""]
    print(f"lake build --no-build{' --rehash' if rehash else ''}: exit {r.returncode}: {tail[0][:160]}")
    return r.returncode


REFUSED_EXIT = 4
_NOT_REFUSED = ("not checked out", "not a GitHub package")

# ---- admission (0.5.0): the strict audit decides, before anything is fetched or written, whether a registry build may be installed
ADMISSION_POLICY = "strict"
ADMISSION_PROBLEMS_KEPT = 5
CHUNK_UNVERIFIED = ("declaration chunks are experimental and unverified (no axiom audit, kernel replay or second kernel has checked them)")


def allow_unverified(a):
    return bool(getattr(a, "allow_unverified", False))


def notice(a, text, err=True):
    """A line for the user. With --json the document owns stdout, so notices go to stderr."""
    print(text, file=sys.stderr if (err or getattr(a, "json", False)) else sys.stdout)


def unverified_banner(a, what, version, why):
    notice(a, f"UNVERIFIED: {what} {version} is installed without passing the registry's proof policy: {why}", err=False)


def admission_record(row, allowed):
    """What mreg.lock keeps of one admission decision. proof_checked_under_policy is true only when the strict audit row is ok."""
    ok = bool(row["ok"])
    return {"policy": ADMISSION_POLICY, "proof_checked_under_policy": ok,
            "problems": [] if ok else list(row["problems"][:ADMISSION_PROBLEMS_KEPT]),
            "allowed_unverified": bool(allowed and not ok)}


def first_problem(row):
    ps = row["problems"]
    return ps[0] if ps else "unknown"


def admit_builds(reg, builds, a, tool="install"):
    """Run the strict audit on every build BEFORE anything is fetched or written. Returns {lake name: admission record}.
    A build that does not pass is refused (exit REFUSED_EXIT, one line per package, 'nothing was installed') unless --allow-unverified,
    which installs it with a banner and a lock that says so."""
    docs, rows = {}, {}
    for name, b in builds.items():
        rows[name] = audit_build(reg, b.id, b.version, b.key, b.manifest_sha256, [], docs, strict=True)
    if _admission_requires_views(a):       # contract 1.2.0: verify.json is hash-matched to the manifest inside audit_build before `views` is read
        for r in rows.values():
            if r["ok"] and r.get("views") != "pass":
                r["problems"].append("views check (contract 1.2.0) not passed")
                r["ok"] = False
    bad = {n: r for n, r in rows.items() if not r["ok"]}
    if bad and not allow_unverified(a):
        for n, r in bad.items():
            b = builds[n]
            more = f" (+{len(r['problems']) - 1} more)" if len(r["problems"]) > 1 else ""
            print(f"mreg: refused: {b.id} {b.version}: does not pass the registry's proof policy ({ADMISSION_POLICY}): {first_problem(r)}{more}",
                  file=sys.stderr)
        print(f"mreg: refused: {len(bad)} of {len(rows)} package{'s' if len(rows) != 1 else ''} fail admission; nothing was installed. "
              "Pass --allow-unverified to install them anyway (they stay marked unverified in mreg.lock and `mreg audit`).", file=sys.stderr)
        sys.exit(REFUSED_EXIT)
    out = {n: admission_record(r, allow_unverified(a)) for n, r in rows.items()}
    for n, r in bad.items():
        unverified_banner(a, builds[n].id, builds[n].version, first_problem(r))
    return out


def status_line(b, st):
    """One line per package, the four statuses side by side."""
    yn = lambda v: "yes" if v else "no"
    adm = st["admission"]
    tail = "" if adm["proof_checked_under_policy"] else "  UNVERIFIED"
    return (f"status {b.id} {b.version}: downloaded={yn(st['downloaded'])} hash_matched={yn(st['hash_matched'])} "
            f"compatible={st['compatible']} proof_checked_under_policy={yn(adm['proof_checked_under_policy'])}{tail}")


def finish_statuses(proj, a, rc, ran):
    """After the Lake check: set `compatible` (passed / failed / not checked), rewrite the lock's admission records, print the lines."""
    stat = getattr(proj, "status", None)
    if not stat:
        return
    word = "not checked" if not ran else ("passed" if rc == 0 else "failed")
    lp = os.path.join(proj.dir, "mreg.lock")
    lock = json.load(open(lp, encoding="utf-8")) if os.path.exists(lp) else None
    for e in (lock or {}).get("packages", []):
        st = stat.get(e["lake_name"])
        if st:
            st["compatible"] = word
            e["admission"] = dict(st["admission"], downloaded=st["downloaded"], hash_matched=st["hash_matched"], compatible=word)
    if lock is not None:
        atomic_write_text(lp, json.dumps(lock, indent=1))
    for name, st in stat.items():
        print(status_line(st["build"], st))
    _json_data[a.cmd] = {"admission": {st["build"].id: dict(st["admission"], downloaded=st["downloaded"], hash_matched=st["hash_matched"],
                                                           compatible=st["compatible"]) for st in stat.values()}}


def find_train(reg, proj, name=None):
    """The train document to measure the project against: the one named, else the newest train whose toolchain is the
    project's. None when there is no train document at all (a registry without trains)."""
    if name:
        t = reg.json(f"/v1/index/trains/{name}.json", missing_ok=True)
        if t is None:
            die(f"no train {name}")
        return t
    idx = reg.json("/v1/index/trains.json", missing_ok=True)
    for e in reversed((idx or {}).get("trains", [])):
        t = reg.json(f"/v1/index/trains/{e['train']}.json", missing_ok=True)
        if t and t.get("toolchain") == proj.toolchain:
            return t
    return None


def train_refusals(proj, builds, notes, train):
    """Lines naming each dependency the train holds that has no registry build at the project's pin."""
    held = dict(train.get("pins") or {})
    for pid, p in (train.get("packages") or {}).items():
        held.setdefault(p.get("lake_name"), p.get("commit"))
    out = []
    nothing_to_host = train.get("not_in_train") or {}      # e.g. lean4-cli: pinned by Mathlib, no compiled module, no build
    for name, why in sorted(notes.items()):
        if name == proj.root["name"] or name in builds or name not in held or why.startswith(_NOT_REFUSED):
            continue
        if proj.pid(name) in nothing_to_host:
            continue
        out.append(f"{name}: the project pins {proj.commit(name)[:12]}, train {train['train']} pins {str(held[name])[:12]} ({why})")
    return out


def do_install(proj, reg, builds, notes, targets, take_all, dry, lock_targets=None, decls=(), only_named=False, rehash=False, admission=None):
    dep_need = set()
    want, asked, missing = plan(proj, builds, targets, take_all, [d["module"] for d in decls], only_named, deps_out=dep_need)
    if decls:
        cw = plan(proj, builds, [], False, [d["module"] for d in decls], True)[0]
        n, size, pk = cone_size(builds, cw)
        nm = len({d["module"] for d in decls})
        print(f"note: module-level install for now (the registry serves no declaration-level bundles yet): "
              f"{len(decls)} declaration{'s' if len(decls) != 1 else ''} in {nm} module{'s' if nm != 1 else ''} "
              f"need {n} modules, {human_bytes(size)} compressed, from {pk} package{'s' if pk != 1 else ''}")
    for m in missing:
        print(f"note: {m} is not a module of any package build found (Lean core, or not in the registry)")
    state = load_state(proj)
    cache = os.path.join(proj.dir, ".lake", "mreg-cache")
    t0, tot = time.time(), {"modules": 0, "frames": 0, "files": 0, "bytes": 0}
    fetched_now = set()
    pd_state = state.setdefault("path_dependencies", {})
    pd_todo = []              # (lake name, build, path dependency, record): the packs to write; each is verified before anything is written
    for name, b in builds.items():
        for d in b.path_deps:
            rec = d.record(proj)
            wanted = want[name] is None or bool(want[name]) or any(m in dep_need for m in d.mods) or name in state["packages"]
            if not wanted:
                continue
            if (pd_state.get(name) or {}).get(d.name) == rec:
                print(f"{b.id}: path dependency {d.name}: {len(d.index)} files already installed")
                continue
            pd_todo.append((name, b, d, rec))
            if not dry:
                d.prepare()
    for name, b in builds.items():
        mods = want[name]
        n_all = len(b.mods)
        st = state["packages"].get(name, {})
        have = set(st.get("modules", [])) if st.get("build_key") == b.key else set()
        need = (set(b.mods) if mods is None else mods) - have
        allb = sum(s["bytes"] for s in b.man["shards"])
        if not need:
            print(f"{b.id}: {len(set(b.mods) if mods is None else mods)} of {n_all} modules needed, all already installed")
            continue
        size = sum(f["length"] for f in b.frames if f["module"] in need or f["module"] is None)
        print(f"{b.id} {b.version}: {len(need)} of {n_all} modules, {size/1e6:.1f} of {allb/1e6:.1f} MB")
        if dry:
            continue
        r = b.fetch(need if (mods is not None or have) else None, cache)
        fetched_now.add(name)
        tot["modules"] += len(need); tot["frames"] += r["frames"]; tot["files"] += r["files"]; tot["bytes"] += r["bytes"]
        state["packages"][name] = {"id": b.id, "version": b.version, "build_key": b.key, "modules": sorted(have | need)}
    for name, b in builds.items():
        if b.declared_changes:
            print(f"note: {b.id} {b.version}: the build records source changes in {', '.join(sorted(b.declared_changes))} (its builder's toolchain bump and "
                  "train-pin rewrite of the project's files); the clean checkout was bound to the signed rewrite (original and rewritten lake-manifest.json "
                  "hashes, toolchain before and after); the digest itself is not re-derived, and Lake's no-build check judges the sources")
    for name, b, d, rec in pd_todo:
        print(f"{b.id} {b.version}: path dependency {d.name}: {len(d.mods)} modules, {len(d.index)} files into "
              f"{rec['dest']}/.lake/build (checkout pinned at {b.man['commit'][:12]})")
        if dry:
            continue
        d.install()
        fetched_now.add(name)
        pd_state.setdefault(name, {})[d.name] = rec
    for name, why in notes.items():
        if name not in builds and name != proj.root["name"]:
            print(f"{name}: no registry build ({why}); Lake compiles it from source if it is needed")
    if dry:
        print(f"dry run: nothing written; {reg.requests} requests so far"); return asked
    os.makedirs(os.path.join(proj.dir, ".lake"), exist_ok=True)
    atomic_write_text(os.path.join(proj.dir, STATE), json.dumps(state))
    rehashed = None
    if rehash:       # install --check and ci: whatever the state file calls installed is re-hashed, fetched now or not
        rn, rbad, rbook, _ = rehash_installed(proj, reg, state, set(builds))
        if rbad:
            print(f"mreg: {rbad} installed compiled file{'s' if rbad != 1 else ''} differ{'' if rbad != 1 else 's'} from the registry's "
                  f"recorded SHA-256 (MISMATCH lines above); mreg.lock not written; remove the changed file's module from "
                  f"{STATE.replace(os.sep, '/')} (or delete the file) and rerun to fetch it again", file=sys.stderr)
            sys.exit(1)
        rehashed = rn
    # the four statuses, kept apart (see the module docstring): the bytes are on disk; their hashes were matched in this run (every frame
    # fetched now is matched on arrival, `--check`/ci re-hash all installed files); Lake's verdict comes later; the strict audit's verdict
    proj.status = {}
    for name, b in builds.items():
        st = state["packages"].get(name, {})
        proj.status[name] = {"build": b, "downloaded": bool(st.get("modules")) and st.get("build_key") == b.key,
                             "hash_matched": name in fetched_now or rehashed is not None, "compatible": "not checked",
                             "admission": (admission or {}).get(name) or {"policy": ADMISSION_POLICY, "proof_checked_under_policy": False,
                                                                           "problems": ["admission was not run"], "allowed_unverified": False}}
    # mreg-lock/0 stays what is written when no declaration was involved, so older clients keep reading those locks
    lock = {"schema": "mreg-lock/1" if decls else "mreg-lock/0", "registry": reg.base,
            "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "toolchain": proj.toolchain,
            "lake_manifest_sha256": sha256_file(os.path.join(proj.dir, "lake-manifest.json")),
            "targets": sorted(lock_targets if lock_targets is not None else asked), "all_modules": bool(take_all), "packages": []}
    if decls:
        lock["install_level"] = "module"   # what was installed; `declarations` per package is what was asked
    via = {d.name: n for n, b in builds.items() for d in b.path_deps}
    for name in proj.names:
        e = {"lake_name": name, "role": "root" if name == proj.root["name"] else "dependency", "commit": proj.commit(name)}
        if name in builds:
            b = builds[name]
            e.update({"id": b.id, "version": b.version, "from": "registry", "build_key": b.key,
                      "resolve_key": b.man["resolve_key"], "manifest_sha256": b.manifest_sha256, "signed": b.signed,
                      "shards": [{"name": s["name"], "sha256": s["sha256"], "bytes": s["bytes"]} for s in b.man["shards"]],
                      "source_changes": b.man.get("source_changes")})
            if b.path_deps:
                e["path_dependencies"] = [dict({"name": d.name, "dir": d.e["dir"]}, **d.record(proj)) for d in b.path_deps]
            ps = proj.status[name]
            e["admission"] = dict(ps["admission"], downloaded=ps["downloaded"], hash_matched=ps["hash_matched"], compatible=ps["compatible"])
            if decls:
                e["declarations"] = [{k: d[k] for k in ("entry", "name", "module", "kind", "th")} for d in decls
                                     if d["lake_name"] == name]
                st = state["packages"].get(name, {})
                e["modules"] = sorted(st.get("modules", [])) if st.get("build_key") == b.key else []
        elif name in via:
            e.update({"from": "registry-path-dependency", "via": via[name]})   # installed from the build of `via`; old clients read it as a source package
        else:
            e["from"] = "source"
        lock["packages"].append(e)
    atomic_write_text(os.path.join(proj.dir, "mreg.lock"), json.dumps(lock, indent=1))
    print(f"installed {tot['modules']} modules ({tot['files']} files, {tot['bytes']/1e6:.1f} MB compressed) in "
          f"{time.time()-t0:.0f} s with {reg.requests} requests; every frame's SHA-256 matched the registry's recorded hash (not a check of proofs); wrote mreg.lock")
    if rehashed is not None:
        print(f"re-hashed the installed files: {rehashed} files of the packages above equal the registry's recorded SHA-256 (not a check of proofs)")
    return asked


# ---------------------------------------------------------------- one train (phase A)

def one_train_guard(d, asked, items):
    """Refuse to mix trains. items: [(package id, version, trains the build is on)]. The project's train is --train, else the one recorded
    (mreg-chunks.lock.json, mreg.json), else the baseline; with no recorded train the baseline is only a default: the builds must then have
    one train in common. Raises NIError forbidden_mix (exit 15) naming the package and both trains."""
    T, src = lc_project_train(d, asked)
    items = [(p, v, list(t or [])) for p, v, t in items]
    none = [f"{p} {v}" for p, v, t in items if not t]
    if none:
        raise NIError("forbidden_mix", "refusing: " + ", ".join(none) + " has no train on record (the registry's package document lists none, or it is missing): "
                      "it cannot be shown to belong to the project's one train", packages=[x.split(" ")[0] for x in none])
    if src != "baseline":
        bad = [f"{p} {v} is on train(s) {', '.join(t)}" for p, v, t in items if T not in t]
        if bad:
            raise NIError("forbidden_mix", f"refusing to mix trains: the project is on train {T} ({src}) but " + "; ".join(bad) +
                          "; every package of a project must be on its one train", train=T, packages=[x.split(" ")[0] for x in bad])
        return
    common = None
    for p, v, t in items:
        common = set(t) if common is None else common & set(t)
    if items and not common:
        first = items[0]
        other = next((x for x in items if not set(x[2]) & set(first[2])), items[-1])
        raise NIError("forbidden_mix", f"refusing to mix trains: {first[0]} {first[1]} is on train(s) {', '.join(first[2])}, "
                      f"{other[0]} {other[1]} is on train(s) {', '.join(other[2])}: no train holds both", packages=[first[0], other[0]])


def add_train_guard(d, cfg, asked, t, reg):
    """`mreg add` of a package of train t into a project that is already on another train: the recorded one (mreg.json, chunk lock), or,
    when none is recorded, the trains of the builds the project has installed (mreg.lock)."""
    rec = (_read_json(os.path.join(d, CHUNK_LOCK)) or {}).get("train") or cfg.get("train")
    if rec and t["train"] != rec:
        held = sorted({e["id"] for e in lc_lock_packages_dir(d)})
        raise NIError("forbidden_mix", f"refusing to mix trains: the project is on train {rec}, this add is for train {t['train']}"
                      + (f" (packages already installed: {', '.join(held)})" if held else "") + "; start a new project for the other train",
                      train=rec, asked=t["train"])
    if not rec:
        bad = [(e, lc_locked_trains(reg, e)) for e in lc_lock_packages_dir(d)]
        bad = [(e, trs) for e, trs in bad if t["train"] not in trs]          # a build with no train on record is a refusal too
        if bad:
            raise NIError("forbidden_mix", "refusing to mix trains: this add is for train " + t["train"] + " but " +
                          "; ".join(f"{e['id']} {e['version']} (installed) is on train(s) {', '.join(trs) or 'none on record'}" for e, trs in bad) +
                          "; start a new project for the other train", asked=t["train"], packages=[e["id"] for e, _ in bad])


def lc_locked_trains(reg, e):
    doc = reg.json(f"/v1/index/{e['id']}.json", missing_ok=True)
    b = next((x for x in (((doc or {}).get("versions") or {}).get(e["version"]) or {}).get("builds", []) if x.get("build_key") == e["build_key"]), None)
    return list((b or {}).get("trains") or [])


# ---------------------------------------------------------------- commands

def use_original_modules(a):
    return a.module_level or (getattr(a, "variant", None) == "full" and not a.chunks and not allow_unverified(a))


def named_or_fallback(cmd, a, entries, record=False):
    try:
        return ni_run(cmd, a, entries, record=record)
    except NIError as error:
        if (error.extra.get("verified_selection_unavailable") and not a.chunks
                and not os.path.exists(os.path.join(a.dir, CHUNK_LOCK))):
            notice(a, f"{error.message}. Using original modules.")
            return None
        raise


def cmd_install(a):
    named = [m for m in a.modules if "#" in m]
    cfgc = (load_cfg(os.path.abspath(a.dir)).get("chunks") or {}).get("declarations")
    if not use_original_modules(a) and (named or (not a.modules and (cfgc or a.upgrade_build))) and (a.chunks or os.path.exists(os.path.join(os.path.abspath(a.dir), CHUNK_LOCK)) or ni_guard("install", a, lambda: ni_probe(a))):
        if [m for m in a.modules if "#" not in m]:
            die("name either declarations (owner/pkg#Decl) or modules, not both")
        result = ni_guard("install", a, lambda: named_or_fallback("install", a, named))
        if result is not None:
            sys.exit(result)
    proj, reg = Project(a.dir), Registry()
    ni_guard("install", a, lambda: reverse_mix(proj.dir, list(proj.names)))
    reg.accept_new_key = a.accept_new_key
    builds, notes = proj.resolve(reg, a.any_platform, a.skip_root)
    ni_guard("install", a, lambda: one_train_guard(proj.dir, a.train, [(b.id, b.version, getattr(b, "trains", [])) for b in builds.values()]))
    if not a.allow_source:
        train = find_train(reg, proj, a.train)
        bad = train_refusals(proj, builds, notes, train) if train else []
        if bad:
            for line in bad:
                print("mreg: " + line, file=sys.stderr)
            print(f"mreg: refused: {len(bad)} dependenc{'y' if len(bad) == 1 else 'ies'} held by train {train['train']} "
                  f"(toolchain {train.get('toolchain')}) have no registry build at the project's pin; nothing was installed. "
                  "Pin them at the train's commit (the train's pins are listed by `mreg train`), or pass --allow-source to leave "
                  "them to Lake (it compiles them from source).", file=sys.stderr)
            sys.exit(REFUSED_EXIT)
    if not builds:
        for n, why in notes.items():
            print(f"{n}: {why}")
        die("the registry has no build for any package of this project")
    admission = admit_builds(reg, builds, a, "install")     # before anything is fetched or written
    # An argument with '#' names a declaration (owner/pkg#Decl.name). Naming anything installs exactly that; naming
    # nothing installs what the project needs plus the declarations recorded in mreg.json.
    named = list(a.modules)
    mods = [m for m in named if "#" not in m]
    entries = [m for m in named if "#" in m] if named else list(load_cfg(proj.dir).get("declarations") or [])
    decls = resolve_declarations(builds, entries)
    asked = do_install(proj, reg, builds, notes, mods, a.all, a.dry_run, decls=decls, only_named=bool(named), rehash=a.check,
                       admission=admission)
    if a.dry_run:
        return
    rc, ran = 0, False
    if a.check:
        rc, ran = lake_check(proj, asked, a.all or (not named and proj.root["name"] in builds), not a.no_rehash, a.no_lake_check), not a.no_lake_check
    finish_statuses(proj, a, rc, ran)
    if a.check:
        sys.exit(rc)


def cmd_ci(a):
    cl = os.path.exists(os.path.join(os.path.abspath(a.dir), CHUNK_LOCK))
    if cl:
        rc = ni_guard("ci", a, lambda: ni_ci(a))
        if not os.path.exists(os.path.join(os.path.abspath(a.dir), "mreg.lock")) or a.chunks_only:
            sys.exit(rc)
        sys.stdout = sys.stderr if a.json else sys.stdout     # the JSON document above stays alone on stdout
    proj, reg = Project(a.dir), Registry()
    reg.accept_new_key = a.accept_new_key
    lp = os.path.join(proj.dir, "mreg.lock")
    if not os.path.exists(lp):
        die("no mreg.lock here")
    lock = json.load(open(lp, encoding="utf-8"))
    if lock.get("schema") not in LOCK_SCHEMAS:
        die(f"unknown lock schema {lock.get('schema')!r}")
    if sha256_file(os.path.join(proj.dir, "lake-manifest.json")) != lock["lake_manifest_sha256"]:
        die("lake-manifest.json is not the one this lock was made for")
    if proj.toolchain != lock["toolchain"]:
        die(f"lean-toolchain is {proj.toolchain}, the lock is for {lock['toolchain']}")
    builds, notes = {}, {}
    ni_guard("ci", a, lambda: one_train_guard(proj.dir, a.train, [(e["id"], e["version"], lc_locked_trains(reg, e)) for e in lock["packages"]
                                                                  if e["from"] == "registry"]))
    for e in lock["packages"]:
        if e["from"] == "registry":
            if proj.commit(e["lake_name"]) != e["commit"]:
                die(f"{e['lake_name']}: checkout is not at the locked commit")
            builds[e["lake_name"]] = Build(reg, e["lake_name"], e["id"], e["version"], e["build_key"], e["manifest_sha256"],
                                           package_dir(proj.dir, proj.root, e["lake_name"]),
                                           signed=True if e.get("signed") else None)
            for s, t in zip(builds[e["lake_name"]].man["shards"], e["shards"]):
                if (s["name"], s["sha256"], s["bytes"]) != (t["name"], t["sha256"], t["bytes"]):
                    die(f"{e['id']}: shard list differs from the lock")
            b = builds[e["lake_name"]]
            attach_path_deps(reg, proj, e["lake_name"], b)
            key = lambda r: (r["name"], r["build_key"], r["manifest_sha256"], r["index_sha256"])
            if sorted(key(r) for r in e.get("path_dependencies") or []) != sorted(key(d.e | {"name": d.name}) for d in b.path_deps):
                die(f"{e['id']}: its path dependency packs differ from the lock (an older lock holds none: run `mreg install` again)")
    admission = admit_builds(reg, builds, a, "ci")     # run again on every ci, whatever the lock says (an old lock has no admission field)
    # A package locked as "source" has no registry build. That is fine when none of its modules is needed (Mathlib
    # pins lean4-cli but the library never imports it). If one is needed, the `--no-build` check below fails,
    # because `ci` never compiles anything.
    # declarations the lock records are looked up again in the locked build's graph: same module, same statement hash
    decls = []
    for e in lock["packages"]:
        for d in e.get("declarations") or []:
            b = builds.get(e["lake_name"])
            if b is None:
                die(f"{d['entry']}: its package is not locked from the registry")
            who = f"{b.id} {b.version}"
            r = find_decl(load_graph_text(reg, b.base, b.man, who), d["name"], who, b.mods)
            if r["module"] != d["module"] or r.get("th") != d.get("th"):
                die(f"{d['entry']}: the locked build's graph says module {r['module']} (statement {r.get('th')}), "
                    f"the lock says {d['module']} ({d.get('th')})")
            decls.append(decl_record(d["entry"], b.id, e["lake_name"], r))
    do_install(proj, reg, builds, notes, lock["targets"], lock.get("all_modules", False), False, lock_targets=lock["targets"],
               decls=decls, rehash=True, admission=admission)
    whole = lock.get("all_modules") or proj.root["name"] in builds
    rc = lake_check(proj, lock["targets"], whole, not a.no_rehash, a.no_lake_check)
    finish_statuses(proj, a, rc, not a.no_lake_check)
    sys.exit(rc)


def rehash_installed(proj, reg, state, names=None):
    """Re-hash the installed files of the packages of `state` (all, or only `names`) against the registry's recorded SHA-256
    (package manifest -> shards/index.jsonl -> per-file hash). Prints a MISMATCH line per differing or missing compiled file.
    Returns (files checked, compiled-file mismatches, bookkeeping files rewritten, [MISMATCH names]).

    Compiled files (.olean, .ilean, .ir, .c ...) must match the registry byte for byte. `.hash` and `.trace` files
    are Lake's own bookkeeping beside them: Lake may rewrite one (seen 2026-11-10: a hash stored as 15 hex digits
    rewritten as the same number with a leading zero), so a difference there is reported but is not a failure."""
    bad, n, book, names_bad = 0, 0, 0, []
    for name, st in state["packages"].items():
        if names is not None and name not in names:
            continue
        base = f"/v1/blobs/{st['id']}/-/{st['version']}/{st['build_key']}/"
        man = json.loads(reg.get(base + "manifest.json"))
        raw = reg.get(base + "shards/index.jsonl")
        if sha256(raw) != man["aux_files"]["shards/index.jsonl"]["sha256"]:
            die(f"{st['id']}: index.jsonl does not match the manifest")
        mods, dest = set(st["modules"]), package_dir(proj.dir, proj.root, name)
        for line in raw.decode("utf-8").splitlines():
            if not line.strip():
                continue
            e = json.loads(line)
            if e["module"] in mods:
                p = os.path.join(dest, *e["path"].split("/")); n += 1
                if not os.path.exists(p) or sha256_file(p) != e["sha256"]:
                    if e["path"].endswith((".hash", ".trace")) and os.path.exists(p):
                        book += 1; print(f"rewritten by Lake (bookkeeping, not a compiled file) {name}: {e['path']}")
                    else:
                        bad += 1; names_bad.append(f"{name}: {e['path']}"); print(f"MISMATCH {name}: {e['path']}")
        # the path dependency packs installed for this package (pinned by the signed manifest, which is checked again here)
        for dname, rec in sorted((state.get("path_dependencies") or {}).get(name, {}).items()):
            ent = next((x for x in path_dep_entries(man, st["id"]) if x["name"] == dname), None)
            if ent is None or any(ent[k] != rec[k] for k in ("build_key", "manifest_sha256", "index_sha256")):
                bad += 1; names_bad.append(f"{name}: path dependency {dname}"); print(f"MISMATCH {name}: path dependency {dname} is not the one the signed manifest records")
                continue
            b = _types.SimpleNamespace(id=st["id"], version=st["version"], base=base, man=man, reg=reg, path_deps=[])
            d = PathDep(reg, proj, name, b, ent)
            if os.path.normcase(os.path.normpath(os.path.join(proj.dir, rec["dest"]))) != os.path.normcase(d.dest):
                bad += 1; names_bad.append(f"{name}: path dependency {dname}"); print(f"MISMATCH {name}: path dependency {dname} was installed somewhere else than Lake's directory now")
                continue
            for path, res in d.rehash():
                n += 1
                if res == "ok":
                    continue
                if path.endswith((".hash", ".trace")) and res == "differs":
                    book += 1; print(f"rewritten by Lake (bookkeeping, not a compiled file) {dname}: {path}")
                else:
                    bad += 1; names_bad.append(f"{dname}: {path}"); print(f"MISMATCH {dname} (path dependency of {name}): {path} ({res})")
    return n, bad, book, names_bad


def cmd_verify(a):
    d = os.path.abspath(a.dir)
    has_chunks, has_state = os.path.exists(os.path.join(d, CHUNK_LOCK)), os.path.exists(os.path.join(d, STATE))
    if not has_chunks and not has_state:
        msg = f"nothing to verify: no {STATE.replace(os.sep, '/')} and no {CHUNK_LOCK} found in {d} (`mreg install` writes them)"
        if a.json:
            print(json.dumps({"schema": VERIFY_SCHEMA, "ok": False, "command": "verify", "error": msg}, indent=1))
        die(msg)
    ni_doc = None
    if has_chunks:
        if a.json and has_state:          # one JSON document on stdout: the chunk part is held and merged with the module part
            buf = io.StringIO()
            try:
                with contextlib.redirect_stdout(buf):
                    ni_guard("verify", a, lambda: ni_verify(a))
            except SystemExit:
                sys.stdout.write(buf.getvalue())
                raise
            ni_doc = json.loads(buf.getvalue())
        else:
            rc = ni_guard("verify", a, lambda: ni_verify(a))
            if not has_state:
                sys.exit(rc)
    proj, reg = Project(a.dir), Registry()
    state = load_state(proj)
    with contextlib.redirect_stdout(sys.stderr if a.json else sys.stdout):
        n, bad, book, names_bad = rehash_installed(proj, reg, state)
        empty = n == 0
        if empty:
            print("mreg: nothing to verify: .lake/mreg-state.json lists no installed files", file=sys.stderr)
        print(f"hashes matched: {n - bad - book} of {n} files of {len(state['packages'])} packages equal the registry's recorded SHA-256 "
              f"(this says nothing about proofs): {bad} compiled-file mismatches, {book} bookkeeping files rewritten locally")
    ok = not bad and not empty
    if a.json:
        mod = {"schema": VERIFY_SCHEMA, "ok": ok, "command": "verify", "files": n, "matched": n - bad - book,
               "packages": len(state["packages"]), "mismatched": names_bad, "bookkeeping_rewritten": book}
        if ni_doc is not None:
            ni_doc["module_level"] = mod
            ni_doc["ok"] = bool(ni_doc.get("ok")) and ok
            mod = ni_doc
        print(json.dumps(mod, indent=1))
    sys.exit(0 if ok else 1)


def cmd_view(a):
    doc = Registry().json(f"/v1/index/{a.id}.json", missing_ok=True)
    if doc is None:
        die(f"{a.id} is not in the registry")
    _json_data["view"] = {"package": doc}
    print(f"{doc['id']}  (Lake name {doc['lake_name']}, licence {doc['license']['spdx']}, {doc['ownership']})")
    print("tags: " + ", ".join(f"{k}={v}" for k, v in doc["dist_tags"].items()))
    for v, e in doc["versions"].items():
        print(f"  {v}  commit {e['commit'][:12]}  {e['committed_at']}  ({e['version_from']})")
        for b in e["builds"]:
            g = " ".join(f"{k}:{s}" for k, s in b["gates"].items() if s != "not run")
            lab = ",".join(b.get("labels") or []) or "-"
            print(f"    build {b['build_key']}  {b['toolchain'].split(':')[-1]}  {b['modules']} modules  "
                  f"{b['bytes_compressed']/1e6:.1f} MB  trains {','.join(b['trains']) or '-'}  usable on "
                  f"{','.join(u['platform'] for u in b['usable_on'])}  [{g}]  labels={lab}  "
                  + ("signed" if b.get("signed") else "unsigned: no registry gate record"))
            if "imported" in (b.get("labels") or []):
                print("      note: " + IMPORTED_MEANING)
            if b.get("declared_toolchain"):
                print("      " + declared_line(b.get("toolchain"), b["declared_toolchain"]))


def get_train(reg, name):
    if not name:
        ts = reg.json("/v1/index/trains.json")["trains"]
        name = ts[-1]["train"]
    t = reg.json(f"/v1/index/trains/{name}.json", missing_ok=True)
    if t is None:
        die(f"no train {name}")
    return t


def cmd_train(a):
    t = get_train(Registry(), a.train)
    _json_data["train"] = {"train": t}
    print(f"{t['train']}  {t['toolchain']}  Mathlib {t['mathlib']['rev'][:12]} ({t['mathlib'].get('input_rev')})  {t['state']}")
    for pid, p in t["packages"].items():
        print(f"  {pid:45s} {p['version']:38s} {p['modules']:6d} modules  roots {','.join(p['module_roots'])}")


def cmd_init(a):
    reg = Registry()
    t = get_train(reg, a.train)
    d = os.path.abspath(a.dir)
    name = a.name or re.sub(r"[^A-Za-z0-9_]", "_", os.path.basename(d)).capitalize()
    os.makedirs(os.path.join(d, name), exist_ok=True)
    def w(rel, text):
        p = os.path.join(d, rel)
        if not os.path.exists(p):
            atomic_write_text(p, text)
    w("lean-toolchain", t["toolchain"] + "\n")
    w("lakefile.toml", f'name = "{name}"\ndefaultTargets = ["{name}"]\n\n[[lean_lib]]\nname = "{name}"\n')
    w(name + ".lean", "")
    w(".gitignore", ".lake/\n")
    w("mreg.json", json.dumps({"registry": reg.base, "train": t["train"]}, indent=1) + "\n")
    if not os.path.exists(os.path.join(d, ".git")):
        subprocess.run(["git", "-C", d, "init", "-q"])
    _json_data["init"] = {"project": {"dir": d, "name": name, "train": t["train"], "toolchain": t["toolchain"]}}
    print(f"created {d}: Lake project {name} on train {t['train']} ({t['toolchain']}); next: mreg add <package id>")


def _toml(v):
    return json.dumps(v, ensure_ascii=False)


def toml_requires(text, name):
    """Does the lakefile text already have a [[require]] with this name?"""
    return any(re.search(r'^\s*name\s*=\s*(?:"%s"|\'%s\')\s*$' % (re.escape(name), re.escape(name)), blk, re.M)
               for blk in text.split("[[require]]")[1:])


def train_pins(reg, t, pid, p):
    """The git dependencies of a train build, as its signed lake-manifest.json pins them, for a package that is built from a rewritten manifest
    (a path dependency pack, or a subdirectory package): Lake would otherwise take them at the pins of the package's own, unrewritten manifest.
    The build is the one the TRAIN names (version, build key, commit); its manifest is checked against the package document and the signature,
    and the lake-manifest.json against the signed manifest's SHA-256."""
    version, build_key = p.get("version"), p.get("build_key")
    doc = reg.json(f"/v1/index/{pid}.json", missing_ok=True) or {}
    rel = (doc.get("versions") or {}).get(version) or {}
    ent = next((b for b in rel.get("builds", []) if b.get("build_key") == build_key), None)
    if ent is None or rel.get("commit") != p.get("commit") or t["train"] not in (ent.get("trains") or []) or not ent.get("signed") or rel.get("yanked"):
        die(f"{pid}: the train does not name a signed, current build of its own (version {version}, build {build_key})")
    base = f"/v1/blobs/{pid}/-/{version}/{build_key}/"
    mraw = reg.get(base + "manifest.json")
    msha = sha256(mraw)
    if msha != ent["manifest"]["sha256"]:
        die(f"{pid} {version}: manifest.json differs from the package document's SHA-256")
    sigraw = reg.get(base + "manifest.json.sig", missing_ok=True)
    if sigraw is None:
        die(f"{pid} {version}: the build is not signed (manifest.json.sig is missing)")
    sg, problems = check_signature(reg, pid, version, build_key, msha, sigraw)
    if problems:
        die(f"{pid} {version}: signature check failed: {problems[0]}")
    man = json.loads(mraw)
    if (man.get("id"), man.get("version"), man.get("build_key"), man.get("commit")) != (pid, version, build_key, p.get("commit")) or t["toolchain"] != man.get("toolchain"):
        die(f"{pid} {version}: the signed manifest names another id, version, build key, commit or toolchain than the train")
    lraw = reg.get(base + "lake-manifest.json")
    if sha256(lraw) != (man.get("aux_files") or {}).get("lake-manifest.json", {}).get("sha256"):
        die(f"{pid} {version}: lake-manifest.json differs from the signed manifest's SHA-256")
    deps = []
    for q in json.loads(lraw).get("packages", []):
        if q.get("type", "git") == "path" or q.get("name") == p["lake_name"]:
            continue
        if not (isinstance(q.get("name"), str) and isinstance(q.get("url"), str) and re.fullmatch(r"[0-9a-f]{40}", q.get("rev") or "")):
            die(f"{pid} {version}: its lake-manifest.json has a dependency without a name, url or full revision")
        deps.append({"name": q["name"], "git": q["url"], "rev": q["rev"], "subDir": _safe_subdir(q.get("subDir"), q["name"])})
    return deps


def cmd_add(a):
    d = os.path.abspath(a.dir)
    if any("#" in r for r in a.ids) and not use_original_modules(a):
        # declaration-level path when the registry serves a store for the train; else the module-level fallback below
        if a.chunks or os.path.exists(os.path.join(d, CHUNK_LOCK)) or ni_guard("add", a, lambda: ni_probe(a)):
            decl = [r for r in a.ids if "#" in r]
            rc = ni_guard("add", a, lambda: named_or_fallback("add", a, decl, record=not a.dry_run))
            if rc is not None:
                a.ids = [r for r in a.ids if "#" not in r]
                if not a.ids or rc:
                    sys.exit(rc)
    cfg = load_cfg(d)
    reg = Registry()
    t = get_train(reg, a.train or cfg.get("train"))
    ni_guard("add", a, lambda: add_train_guard(d, cfg, a.train, t, reg))
    lf = os.path.join(d, "lakefile.toml")
    if not os.path.exists(lf):
        die("no lakefile.toml here (mreg add edits TOML lakefiles only)")
    text, names, newdecls = open(lf, encoding="utf-8").read(), [], []
    for raw in a.ids:
        pd = parse_decl(raw) if "#" in raw else (raw, None)
        if pd is None:
            die(f"{raw!r}: expected <owner/pkg> or <owner/pkg>#<Decl.name>")
        pid, decl = pd
        p = t["packages"].get(pid)
        if p is None:
            die(f"{pid} is not on train {t['train']}")
        if decl is not None:
            r = train_declaration(reg, t, pid, p, decl)
            newdecls.append(r["entry"])
            print(f"{r['entry']}: {r['kind']} defined in module {r['module']}; recorded in mreg.json, installed module-level for now")
        ni_guard("add", a, lambda: reverse_mix(d, [p["lake_name"]]))
        if re.search(r'name\s*=\s*"%s"' % re.escape(p["lake_name"]), text.split("[[require]]", 1)[-1] if "[[require]]" in text else ""):
            print(f"{pid}: already required"); continue
        text += f'\n[[require]]\nname = "{p["lake_name"]}"\ngit = "{p["git"]}"\nrev = "{p["commit"]}"\n'
        sub = p.get("subdir") or ("/".join(pid.split("/")[2:]) if len(pid.split("/")) > 2 else "")
        if sub:        # <owner>/<repo>/<subdir>: the package is in a subdirectory of the repository, Lake needs its subDir
            text += f'subDir = {_toml(_safe_subdir(sub, pid))}\n'
        names.append(p["lake_name"]); print(f"{pid}: require {p['lake_name']} at {p['commit'][:12]} ({p['version']})" + (f" subDir {sub}" if sub else ""))
        if p.get("path_dependencies"):
            # its build was made from a lake-manifest.json rewritten to the train's pins: pin the same dependencies here
            deps = train_pins(reg, t, pid, p)
            for dep in deps:
                if not toml_requires(text, dep["name"]):
                    text += (f'\n[[require]]\nname = {_toml(dep["name"])}\ngit = {_toml(dep["git"])}\nrev = {_toml(dep["rev"])}\n'
                             + (f'subDir = {_toml(dep["subDir"])}\n' if dep["subDir"] else ""))
                    names.append(dep["name"])
            print(f"{pid}: {len(deps)} dependencies pinned from the train build's signed lake-manifest.json; path dependency pack(s): "
                  + ", ".join(sorted(p["path_dependencies"])))
    atomic_write_text(lf, text)
    if newdecls:
        have = list(cfg.get("declarations") or [])
        cfg = dict(cfg)
        cfg.setdefault("registry", reg.base)
        cfg.setdefault("train", t["train"])
        cfg["declarations"] = have + [e for e in dict.fromkeys(newdecls) if e not in have]
        atomic_write_text(os.path.join(d, "mreg.json"), json.dumps(cfg, indent=1) + "\n")
    if names and a.no_lake_update:
        print("lake update skipped (--no-lake-update); run `lake update " + " ".join(names) + "` before mreg install")
    elif names:
        # sources only: Mathlib's own post-update hook would otherwise download its whole cache
        r = subprocess.run(["lake", "update"] + names, cwd=d, env=dict(os.environ, MATHLIB_NO_CACHE_ON_UPDATE="1"))
        if r.returncode:
            die("lake update failed")
        print("sources resolved; next: mreg install")


_REDACT_FIELDS = frozenset({"schema", "n", "time", "prev", "type", "entry_sha256", "reason", "key_id", "signature"})


def log_entry_raw(reg, n):
    cache = reg.__dict__.setdefault("_log", {})
    if n not in cache:
        try:
            raw = reg.get(f"/v1/log/{n}.json", missing_ok=True, takedown_ok=True)
        except TypeError:
            raw = reg.get(f"/v1/log/{n}.json", missing_ok=True)
        if raw is None or raw is _TAKEDOWN:
            alt = reg.get(f"/v1/log/redacted/{n}.json", missing_ok=True)
            if alt is not None:
                raw = alt
            elif raw is _TAKEDOWN:
                raw = None
        cache[n] = raw
    return cache[n]


def _verify_redacted_chain_sha(reg, raw, e, n):
    """Verify a redacted tombstone log entry; return (entry_sha256, None) or (None, problem)."""
    if not isinstance(e, dict) or set(e.keys()) != _REDACT_FIELDS:
        return None, f"log entry {n} (redacted): malformed fields"
    if e.get("schema") != "mreg-log/1" or e.get("type") != "redacted" or e.get("n") != n or isinstance(n, bool):
        return None, f"log entry {n} (redacted): malformed header"
    if not (isinstance(e.get("time"), str) and re.fullmatch(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z", e["time"])):
        return None, f"log entry {n} (redacted): malformed time"
    if not (isinstance(e.get("prev"), str) and re.fullmatch(r"[0-9a-f]{64}", e["prev"])):
        return None, f"log entry {n} (redacted): malformed prev"
    if not (isinstance(e.get("entry_sha256"), str) and re.fullmatch(r"[0-9a-f]{64}", e["entry_sha256"])):
        return None, f"log entry {n} (redacted): malformed entry_sha256"
    if not (isinstance(e.get("reason"), str) and re.fullmatch(r"[a-z0-9][a-z0-9_-]{1,63}", e["reason"])):
        return None, f"log entry {n} (redacted): malformed reason"
    if not (isinstance(e.get("key_id"), str) and re.fullmatch(r"[0-9a-f]{16}", e["key_id"])):
        return None, f"log entry {n} (redacted): malformed key_id"
    if raw != json.dumps(e, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8") + b"\n":
        return None, f"log entry {n} (redacted): not in canonical JSON form"
    pem, prob = key_pem(reg, e["key_id"])
    if prob:
        return None, f"log entry {n} (redacted): {prob}"
    try:
        sigb = base64.b64decode(e.get("signature", ""), validate=True)
    except (ValueError, TypeError):
        return None, f"log entry {n} (redacted): malformed signature"
    if not ec_verify(pem, redact_message(n, e["entry_sha256"], e["prev"], e["time"], e["reason"]), sigb):
        return None, f"log entry {n} (redacted): signature does not verify"
    return e["entry_sha256"], None


def chain_problems(reg, from_n):
    """Walk the log from entry `from_n` to the head: every `prev` must be the hash of the stored bytes of the entry
    before it (or signed `entry_sha256` for a redacted tombstone), the head must name the last entry's hash, and the head's signature must verify."""
    head = reg.json("/v1/log/head.json", missing_ok=True)
    if head is None:
        return ["the registry has no log head"]
    if not isinstance(head.get("n"), int) or head["n"] < from_n:
        return [f"the log head ({head.get('n')}) is older than entry {from_n}"]
    problems, prev = [], "0" * 64
    if from_n > 1:
        raw = log_entry_raw(reg, from_n - 1)
        if raw is None:
            return [f"log entry {from_n - 1} is missing"]
        try:
            e0 = json.loads(raw)
        except ValueError:
            e0 = None
        if isinstance(e0, dict) and e0.get("type") == "redacted":
            sha0, prob0 = _verify_redacted_chain_sha(reg, raw, e0, from_n - 1)
            if prob0:
                return [prob0]
            prev = sha0
        else:
            prev = sha256(raw)
    last = None
    for n in range(from_n, head["n"] + 1):
        raw = log_entry_raw(reg, n)
        if raw is None:
            problems.append(f"log entry {n} is missing")
            return problems
        try:
            e = json.loads(raw)
        except ValueError:
            e = {}
            problems.append(f"log entry {n} is not JSON")
        if e.get("n") != n:
            problems.append(f"log entry {n} says n={e.get('n')}")
        if e.get("prev") != prev:
            problems.append(f"log entry {n}: prev does not match the stored bytes of entry {n - 1} (a changed entry)")
        if isinstance(e, dict) and e.get("type") == "redacted":
            sha_cur, prob = _verify_redacted_chain_sha(reg, raw, e, n)
            if prob:
                problems.append(prob)
                prev = last = sha256(raw)
            else:
                prev = last = sha_cur
        else:
            prev = last = sha256(raw)
    if head.get("sha256") != last:
        problems.append(f"log entry {head['n']} does not match the hash in the log head")
    pem, prob = key_pem(reg, head.get("key_id"))
    try:
        if prob:
            problems.append("log head: " + prob)
        elif not ec_verify(pem, head_message(head["n"], head["sha256"]), base64.b64decode(head["signature"], validate=True)):
            problems.append("the log head's signature does not verify")
    except (KeyError, ValueError, TypeError):
        problems.append("the log head is malformed")
    return problems


def declared_toolchain(entry, man=None):
    """(compiled with, source declares) for a build: `declared_toolchain` from the package document's build entry first, else the manifest.
    (None, None) when the field is absent: nothing is then printed."""
    d = (entry or {}).get("declared_toolchain") or (man or {}).get("declared_toolchain")
    if not d:
        return None, None
    return ((entry or {}).get("toolchain") or (man or {}).get("toolchain")), d


def declared_line(compiled, declared):
    return f"compiled with {compiled or 'unknown'}; source declares {declared}"


def audit_build(reg, pid, version, key, lock_msha, require, docs, strict=False, receipt_report_pins=False):
    row = {"id": pid, "version": version, "build_key": key, "gates": {}, "labels": [], "problems": [], "signature": "none", "mode": "strict" if strict else "lenient"}
    P = row["problems"]
    if pid not in docs:
        docs[pid] = reg.json(f"/v1/index/{pid}.json", missing_ok=True)
    doc = docs[pid]
    release = (doc or {}).get("versions", {}).get(version, {})
    ent = next((b for b in release.get("builds", []) if b["build_key"] == key), None)
    if strict and (release.get("yanked") or (ent or {}).get("yanked")):
        P.append("the registry has withdrawn this source version or build")
    if ent is None:
        P.append("the package document has no such build")
    base = f"/v1/blobs/{pid}/-/{version}/{key}/"
    raw = reg.get(base + "manifest.json", missing_ok=True)
    if raw is None:
        P.append("manifest.json is missing")
        return finish_row(row, require, strict)
    msha = sha256(raw)
    if ent and ent["manifest"]["sha256"] != msha:
        P.append("manifest.json differs from the package document's SHA-256")
    if lock_msha and lock_msha != msha:
        P.append("manifest.json differs from the lock file's SHA-256")
    man = json.loads(raw)
    c_tc, d_tc = declared_toolchain(ent, man)
    if d_tc:
        row["compiled_toolchain"], row["declared_toolchain"] = c_tc, d_tc
    if (man.get("id"), man.get("version"), man.get("build_key")) != (pid, version, key):
        P.append("the manifest names another id, version or build key than its path")
    sigraw = reg.get(base + "manifest.json.sig", missing_ok=True)
    sg = None
    if sigraw is None:
        P.append("UNSIGNED: manifest.json.sig is missing")
        row["signature"] = "missing"
    else:
        sg, probs = check_signature(reg, pid, version, key, msha, sigraw)
        P.extend(probs)
        row["signature"] = "valid" if sg else "invalid"
        if sg:
            row["labels"] = sg["labels"]
            if ent and sorted(ent.get("labels", [])) != sorted(sg["labels"]):
                P.append("the package document's labels differ from the signed labels")
    # reports: every hash the manifest lists, then the gates in verify.json against the manifest's
    reps = man.get("reports")
    if not isinstance(reps, dict) or "reports/verify.json" not in reps:
        P.append("the manifest lists no reports/verify.json (a build from before the gates)")
    else:
        for rel, h in sorted(reps.items()):
            if receipt_report_pins:
                parts = rel.split("/")
                if (len(parts) < 2 or parts[0] != "reports" or any(not _NAME_OK.fullmatch(p) for p in parts[1:])
                        or not isinstance(h, str) or not _HEX64.fullmatch(h)):
                    P.append("invalid path or SHA-256 in signed source report inventory")
                    continue
                # The signed declaration receipt covered all source report bodies at release.
                # Re-read the report that drives current gate policy on every install and restore.
                if rel != "reports/verify.json":
                    continue
            body = reg.get(base + rel, missing_ok=True)
            if body is None:
                P.append(f"report {rel} is missing")
            elif sha256(body) != h:
                P.append(f"report {rel} differs from the manifest's SHA-256")
            elif rel == "reports/verify.json":
                try:
                    vg = json.loads(body)["gates"]
                    row["gates"] = {g: (s.get("status") if isinstance(s, dict) else s) for g, s in vg.items()}
                    vw = json.loads(body).get("views")
                    row["views"] = vw.get("status") if isinstance(vw, dict) else vw
                    mg = {g: (s.get("status") if isinstance(s, dict) else s) for g, s in (man.get("gates") or {}).items()}
                    if mg != row["gates"]:
                        P.append("the manifest's gates differ from verify.json")
                except (ValueError, KeyError, AttributeError):
                    P.append("reports/verify.json is malformed")
    # path dependency packs (the nested modules the build needs, bound by the signed manifest): well formed, every gate of theirs passed
    try:
        for pd in path_dep_entries(man, pid):
            bad = sorted(g for g, v in (pd.get("gates") or {}).items() if v != "pass")
            if not isinstance(pd.get("gates"), dict) or not pd["gates"] or bad:
                P.append(f"path dependency {pd['name']}: its own gates are not all pass" + (f" ({', '.join(bad)})" if bad else " (none recorded)"))
            if pd.get("modules_built") != pd.get("modules_expected"):
                P.append(f"path dependency {pd['name']}: {pd.get('modules_built')} of {pd.get('modules_expected')} modules built")
    except SystemExit as e:
        P.append(str(e).removeprefix("mreg: "))
    # the log: this build's entry, then the chain to the head
    n = (ent or {}).get("log_n")
    if not isinstance(n, int):
        P.append("the package document names no log entry for this build")
    else:
        raw_e = log_entry_raw(reg, n)
        if raw_e is None:
            P.append(f"log entry {n} is missing")
        else:
            try:
                e = json.loads(raw_e)
                if isinstance(e, dict) and e.get("type") == "redacted":
                    reason = e.get("reason", "redacted")
                    P.append(f"log entry {n} has been redacted ({reason})")
                else:
                    want = {"id": pid, "version": version, "build_key": key, "manifest_sha256": msha}
                    if sigraw is not None:
                        want["sig_sha256"] = sha256(sigraw)
                    if sg:
                        want["labels"] = sg["labels"]
                    for f, v in want.items():
                        if e.get(f) != v:
                            P.append(f"log entry {n}: {f} differs from the build")
                    if e.get("type") not in ("promote", "adopt"):
                        P.append(f"log entry {n} is of type {e.get('type')!r}")
            except ValueError:
                P.append(f"log entry {n} is not JSON")
            P.extend(chain_problems(reg, n))
    return finish_row(row, require, strict)


def strict_problems(row):
    """What strict mode adds: every rule the promotion rules require, each failure one line that says which. Unsigned or badly signed
    builds have no registry gate record, so their gate statuses are not judged (they are not the registry's record)."""
    out = []
    sig = row.get("signature")
    if sig in ("none", "missing"):
        return ["unsigned: no registry gate record (the gate statuses shown, if any, are the builder's own, not a registry record)"]
    if sig != "valid":
        return ["signature not valid: no trustworthy registry gate record"]
    labels = sorted(set(row.get("labels") or []))
    known = [l for l in labels if l in AUDIT_LABELS]
    if not labels:
        out.append("no label: the signed record carries none")
    elif len(known) != 1 or len(labels) != 1:
        out.append(f"label {','.join(labels)} is not exactly one of clean or imported (strict needs clean or imported)")
    gates = row.get("gates") or {}
    need = AUDIT_LABELS[known[0]] if len(known) == 1 else AUDIT_LABELS["clean"]
    for g in need:
        st = gates.get(g)
        if st == "pass":
            continue
        if g == "G7" and st == "not run":
            out.append("gate G7 (second kernel) is not run: a build with G7 not run is never accepted")
        else:
            out.append(f"gate {g} is {st if st else 'missing'}, not pass")
    imp = len(known) == 1 and known[0] == "imported"
    if imp:
        st = gates.get("G1")
        if st != "not run":
            out.append(f"gate G1 is {st if st else 'missing'}: an imported build records G1 as not run (compile step not re-run here)")
    for g, st in sorted(gates.items()):
        if g in need or (imp and g == "G1"):
            continue
        if st in ("flag", "fail"):
            out.append(f"gate {g} is {st}")
    return out


def finish_row(row, require, strict=False):
    for g in require:
        st = row["gates"].get(g)
        if st != "pass":
            row["problems"].append(f"required gate {g} is {st if st else 'missing'}, not pass")
    if strict:
        for p in strict_problems(row):
            row["problems"].append("strict: " + p)
    row["ok"] = not row["problems"]
    return row


def cmd_audit(a):
    if getattr(a, "strict", False) and getattr(a, "lenient", False):
        die("--strict and --lenient exclude each other")
    strict = True if getattr(a, "strict", False) else False if getattr(a, "lenient", False) else AUDIT_STRICT_DEFAULT
    reg = Registry()
    reg.accept_new_key = a.accept_new_key
    require = [g.strip() for g in a.require.split(",") if g.strip()]
    lp = os.path.join(os.path.abspath(a.dir), "mreg.lock")
    lock = json.load(open(lp, encoding="utf-8")) if os.path.exists(lp) else None
    chunk_lock = _read_json(os.path.join(os.path.abspath(a.dir), CHUNK_LOCK))
    chunk_row = None
    if not a.target and chunk_lock and (chunk_lock.get("receipt_sha256") or not lock):
        def audit_slices():
            if chunk_lock.get("schema") != CHUNK_LOCK_SCHEMA:
                raise NIError("error", "unknown declaration lock schema")
            pin = receipt_pin(None, chunk_lock, chunk_lock["build"], chunk_lock["variant"])
            if not pin:
                raise chunk_refusal("`mreg audit` of the chunk lock")
            admission, _ = validate_chunk_lock(Fetcher(), Store(), a, chunk_lock, pin, full_reports=True)
            return {"id": "mreg/declaration-slices", "version": chunk_lock["train"], "build_key": chunk_lock["build"],
                    "ok": True, "gates": {f"C{i}": "pass" for i in range(7)}, "admission": admission,
                    "labels": ["verified-declarations"], "problems": []}
        chunk_row = ni_guard("audit", a, audit_slices)
        if not lock:
            if a.json:
                print(json.dumps([chunk_row], indent=1))
            else:
                print(f"{chunk_lock['train']} {chunk_lock['build']}: signed kernel-declaration receipt and "
                      f"{len(chunk_row['admission']['sources'])} source builds passed the strict audit")
            sys.exit(0)
    todo = []
    if a.target:
        pid, _, ver = a.target.partition("@")
        doc = reg.json(f"/v1/index/{pid}.json", missing_ok=True)
        if doc is None:
            die(f"{pid} is not in the registry")
        ver = ver or doc["dist_tags"].get("latest")
        if ver not in doc["versions"]:
            die(f"{pid} has no version {ver}")
        locked = [e for e in (lock or {}).get("packages", []) if e.get("id") == pid and e.get("version") == ver]
        todo = [(pid, ver, e["build_key"], e["manifest_sha256"]) for e in locked] or \
               [(pid, ver, b["build_key"], None) for b in doc["versions"][ver]["builds"]]
    else:
        if lock is None:
            die("no mreg.lock here: name a package, `mreg audit <id>[@<version>]`")
        todo = [(e["id"], e["version"], e["build_key"], e["manifest_sha256"]) for e in lock["packages"] if e.get("from") == "registry"]
    if not todo and chunk_row is None:
        die("nothing to audit")
    docs, rows = {}, []
    require_views = _admission_requires_views(a)
    locked_adm = {(e.get("id"), e.get("version"), e.get("build_key")): e.get("admission") for e in (lock or {}).get("packages", [])}
    for pid, ver, key, msha in todo:
        row = audit_build(reg, pid, ver, key, msha, require, docs, strict)
        if require_views and row.get("views") != "pass":
            row["problems"].append("views check (contract 1.2.0) not passed")
            row["ok"] = False
        rows.append(row)
        adm = locked_adm.get((pid, ver, key))
        if adm:
            rows[-1]["lock_admission"] = adm
    if chunk_row:
        rows.append(chunk_row)
    if a.json:
        print(json.dumps(rows, indent=1))
    else:
        for r in rows:
            g = " ".join(f"{k}:{r['gates'][k]}" for k in sorted(r["gates"], key=lambda x: int(x[1:])) if r["gates"][k] != "not run")
            print(f"{r['id']} {r['version']} {r['build_key']}  [{g}]  labels={','.join(r['labels']) or '-'}  "
                  f"{'OK' if r['ok'] else 'FAIL'}")
            if "imported" in r["labels"]:
                print("    note: " + IMPORTED_MEANING)
            if r.get("declared_toolchain"):
                print("    " + declared_line(r.get("compiled_toolchain"), r["declared_toolchain"]))
            for p in r["problems"]:
                print("    - " + p)
            if (r.get("lock_admission") or {}).get("allowed_unverified"):
                print("    UNVERIFIED: mreg.lock records this build as installed with --allow-unverified (it did not pass the registry's proof policy)")
        if chunk_lock and not chunk_lock.get("receipt_sha256"):
            print(f"UNVERIFIED: {CHUNK_LOCK} holds declaration chunks: {CHUNK_UNVERIFIED}")
        if strict:
            print(f"audit (strict): {sum(1 for r in rows if r['ok'])} of {len(rows)} builds pass every rule promotion requires "
                  f"(signed, label clean or imported, the gates that label needs pass, G7 run, signature, reports and log consistent); "
                  f"{sum(1 for r in rows if not r['ok'])} do not. This compares the registry's records with each other and is not a check of proofs"
                  + (f" (required: {','.join(require)})" if require else ""))
        else:
            print(f"audit: {sum(1 for r in rows if r['ok'])} of {len(rows)} builds with consistent signature, reports and log; "
                  f"{sum(1 for r in rows if not r['ok'])} without (a problem found, or a required gate not passing; this compares the build's records with each other and is not a check of proofs)"
                  + (f" (required: {','.join(require)})" if require else ""))
    if not strict:
        print("warning: --lenient is on. A gate that is 'not run' or 'flag' is NOT counted as a failure, and a label other than clean or imported "
              "is accepted; use plain `mreg audit` for the strict check", file=sys.stderr)
    sys.exit(0 if all(r["ok"] for r in rows) else 1)


# ---------------------------------------------------------------- accounts: login, logout, whoami (plan B.4)
# Sign-in is the pool's hosted page (authorization code + PKCE, public client, no secret). The ID token it returns is used
# once, as the bearer of the key service (accounts/keys.mjs), to create a read-scope key; the key is what is stored.
# Nothing in this block ever prints, logs or puts into an error message a token, a code, a verifier or a key.

AUTH_URL = "https://auth.mathregistry.com"
KEYS_URL = "https://rycrjjvbnn2dgpiswhqv4wqqdy0yflmp.lambda-url.us-east-1.on.aws"   # from the public account page
CLIENT_ID = "2mm3ahppct637hhb2ggks7m5i2"
LOGIN_PORT = 8976            # primary localhost callback registered on the app client (as http://localhost:8976/callback)
LOGIN_PORTS = (8976, 8977, 8978)
WELL_KNOWN_AUTH_PATH = "/.well-known/mreg-auth.json"
KEY_RE = re.compile(r"^mreg_([A-Za-z0-9_-]+)\.([A-Za-z0-9_-]{43})$")
PROVIDERS = {"github": "GitHub", "google": "Google"}
ACCOUNT_PAGE = "https://mathregistry.com/account"


def _validate_endpoint_url(label, u):
    u = str(u or "").strip().rstrip("/")
    pr = urllib.parse.urlparse(u)
    if pr.username is not None or pr.password is not None or pr.query or pr.fragment or pr.params:
        die(f"{label} must be an https address (http only for localhost): {u}")
    if (pr.scheme == "https" and pr.hostname) or (pr.scheme == "http" and pr.hostname in ("127.0.0.1", "localhost", "::1")):
        return u
    die(f"{label} must be an https address (http only for localhost): {u}")


def _endpoint(env, default):
    return _validate_endpoint_url(env, os.environ.get(env) or default)


def discover_auth_config(base=None):
    """Discover auth endpoints from <registry>/.well-known/mreg-auth.json with HTTPS/localhost enforcement and built-in fallback.
    Explicit environment variables (MREG_AUTH_URL, MREG_KEYS_URL, MREG_CLIENT_ID, MREG_LOGIN_PORT) always take precedence."""
    env_auth = _endpoint("MREG_AUTH_URL", os.environ["MREG_AUTH_URL"]) if os.environ.get("MREG_AUTH_URL") else None
    env_keys = _endpoint("MREG_KEYS_URL", os.environ["MREG_KEYS_URL"]) if os.environ.get("MREG_KEYS_URL") else None
    env_client = os.environ.get("MREG_CLIENT_ID") or None
    env_port_raw = os.environ.get("MREG_LOGIN_PORT") or ""
    env_port = None
    if env_port_raw:
        try:
            env_port = int(env_port_raw)
        except ValueError:
            die("MREG_LOGIN_PORT is not a number")

    cfg = {"auth_url": AUTH_URL, "keys_url": KEYS_URL, "client_id": CLIENT_ID,
           "login_ports": list(LOGIN_PORTS), "account_page": ACCOUNT_PAGE, "discovered": False}

    if not (env_auth and env_keys and env_client and env_port is not None):
        reg = (base if base is not None else os.environ.get("MREG_REGISTRY", "https://mathregistry.com")).rstrip("/")
        pr = urllib.parse.urlparse(reg)
        can_http = (pr.scheme == "https" and pr.hostname) or (pr.scheme == "http" and pr.hostname in ("127.0.0.1", "localhost", "::1"))
        if can_http:
            raw = None
            req = urllib.request.Request(reg + WELL_KNOWN_AUTH_PATH, headers={"User-Agent": "mreg/" + VERSION})
            try:
                with _no_redirect_open(req, timeout=5) as r:
                    raw = r.read(65536)
            except (urllib.error.HTTPError, OSError, ValueError):
                raw = None
            if raw:
                try:
                    doc = json.loads(raw)
                except ValueError:
                    doc = None
                if isinstance(doc, dict) and doc.get("schema", "mreg-auth/1") == "mreg-auth/1":
                    new_auth = _validate_endpoint_url("auth_url in mreg-auth.json", doc["auth_url"]) if doc.get("auth_url") is not None else None
                    new_keys = _validate_endpoint_url("keys_url in mreg-auth.json", doc["keys_url"]) if doc.get("keys_url") is not None else None
                    new_acct = _validate_endpoint_url("account_page in mreg-auth.json", doc["account_page"]) if doc.get("account_page") is not None else None
                    cid = doc.get("client_id")
                    new_cid = cid if isinstance(cid, str) and re.fullmatch(r"[A-Za-z0-9_.-]{1,128}", cid) else None
                    if new_auth and new_keys and new_cid:
                        cfg["discovered"] = True
                        cfg["auth_url"] = new_auth
                        cfg["keys_url"] = new_keys
                        cfg["client_id"] = new_cid
                        if new_acct:
                            cfg["account_page"] = new_acct
                        ports = doc.get("login_ports")
                        if isinstance(ports, list):
                            clean_ports = []
                            for pt in ports:
                                if isinstance(pt, int) and not isinstance(pt, bool) and 1 <= pt <= 65535 and pt not in clean_ports:
                                    clean_ports.append(pt)
                            if clean_ports:
                                cfg["login_ports"] = clean_ports

    if env_auth:
        cfg["auth_url"] = env_auth
    if env_keys:
        cfg["keys_url"] = env_keys
    if env_client:
        cfg["client_id"] = env_client
    if env_port is not None:
        cfg["login_ports"] = [env_port]
    return cfg


def _b64u(b):
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode("ascii")


def clean_label(t):
    t = (t or "").strip()
    return t if 1 <= len(t) <= 64 and not re.search(r"[\x00-\x1f\x7f<>]", t) else None


def default_label():
    host = re.sub(r"[\x00-\x1f\x7f<>]", "", socket.gethostname()).strip() or "machine"
    return ("mreg on " + host)[:64]


def _open_browser(url):
    try:
        return bool(webbrowser.open(url))
    except Exception:
        return False


def _err_code(e):
    """The short `error` code of an HTTP error body (the services answer {"error": "..."}), else 'HTTP <n>'. Never the body."""
    try:
        c = json.loads(e.read(4096)).get("error")
        if isinstance(c, str) and re.fullmatch(r"[A-Za-z0-9_ -]{1,40}", c):
            return c
    except Exception:
        pass
    return f"HTTP {e.code}"


class _Callback(http.server.ThreadingHTTPServer):
    # The listener is bound to 127.0.0.1 only. The port must never be shared with another process (it would read the authorization code).
    # Windows: SO_REUSEADDR would let a second process bind the same port, so it stays off and SO_EXCLUSIVEADDRUSE is set in server_bind.
    # POSIX: SO_REUSEADDR only allows binding over TIME_WAIT leftovers of an earlier sign-in (the server closes first, so they sit on this
    # port for about a minute); a socket that is listening still refuses a second bind. SO_REUSEPORT, which would share, is never set.
    allow_reuse_address = os.name != "nt"
    allow_reuse_port = False
    daemon_threads = True
    block_on_close = False

    def server_bind(self):          # no reverse DNS lookup of the host name
        import socketserver
        if os.name == "nt" and hasattr(socket, "SO_EXCLUSIVEADDRUSE"):
            self.socket.setsockopt(socket.SOL_SOCKET, socket.SO_EXCLUSIVEADDRUSE, 1)
        socketserver.TCPServer.server_bind(self)
        self.server_name, self.server_port = self.server_address[0], self.server_address[1]


class _CallbackV6(_Callback):
    address_family = socket.AF_INET6

    def server_bind(self):
        if hasattr(socket, "IPV6_V6ONLY"):
            self.socket.setsockopt(socket.IPPROTO_IPV6, socket.IPV6_V6ONLY, 1)
        super().server_bind()


def _cb_get_result(srv):
    sh = getattr(srv, "_shared", None)
    return sh["result"] if sh is not None else srv.result


def _cb_set_result(srv, val):
    srv.result = val
    sh = getattr(srv, "_shared", None)
    if sh is not None:
        sh["result"] = val


class _CallbackHandler(http.server.BaseHTTPRequestHandler):
    timeout = 10                    # a connection that sends nothing (browser pre-connect) must not hold the flow

    def log_message(self, *args):
        pass                        # the request line carries the authorization code: log nothing

    def _page(self, code, text):
        body = ("<!doctype html><meta charset=utf-8><title>mreg</title><p>%s</p>" % text).encode("utf-8")
        self.send_response(code)
        for k, v in (("Content-Type", "text/html; charset=utf-8"), ("Content-Length", str(len(body))),
                     ("Cache-Control", "no-store"), ("Referrer-Policy", "no-referrer"), ("Connection", "close")):
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        srv = self.server
        if (self.headers.get("Host") or "").lower() not in (
            f"localhost:{srv.server_port}", f"127.0.0.1:{srv.server_port}", f"[::1]:{srv.server_port}"
        ):
            return self._page(400, "Wrong host.")      # DNS rebinding guard
        pr = urllib.parse.urlparse(self.path)
        if pr.path != "/callback":
            return self._page(404, "Not found.")
        q = urllib.parse.parse_qs(pr.query)
        one = lambda k: (q.get(k) or [""])[0][:2048]
        with srv.lock:
            if _cb_get_result(srv) is not None:
                return self._page(409, "Already answered.")
            expected = getattr(srv, "expected_state", None)
            if one("error"):
                if expected is not None:
                    st = one("state")
                    if not st:
                        return self._page(400, "Bad request.")
                    if not hmac.compare_digest(st.encode("utf-8"), expected.encode("ascii")):
                        _cb_set_result(srv, {"code": "", "state": st})
                        return self._page(400, "Sign-in failed: state parameter did not match.")
                _cb_set_result(srv, {"error": one("error")[:60]})
                return self._page(200, "Sign-in was not completed. You can close this window.")
            if one("code") and one("state"):
                _cb_set_result(srv, {"code": one("code"), "state": one("state")})
                if expected is not None and not hmac.compare_digest(one("state").encode("utf-8"), expected.encode("ascii")):
                    return self._page(400, "Sign-in failed: state parameter did not match.")
                return self._page(200, "mreg received the sign-in. Return to the terminal; you can close this window.")
        return self._page(400, "Bad request.")


def signin(provider=None, timeout=300.0, no_browser=False, auth_cfg=None):
    """Browser sign-in, authorization code + PKCE (S256). Returns the pool's ID token, the bearer of the key service."""
    cfg = auth_cfg if auth_cfg is not None else discover_auth_config()
    auth = cfg["auth_url"]
    client = cfg["client_id"]
    ports = cfg["login_ports"]
    servers, last_err = [], None
    for port in ports:
        srv4 = srv6 = None
        try:
            srv4 = _Callback(("127.0.0.1", port), _CallbackHandler)
            actual_port = srv4.server_port
            try:
                srv6 = _CallbackV6(("::1", actual_port), _CallbackHandler)
            except OSError as e:
                no_v6 = e.errno in (
                    getattr(errno, "EAFNOSUPPORT", -1),
                    getattr(errno, "EPROTONOSUPPORT", -1),
                    getattr(errno, "EADDRNOTAVAIL", -1),
                )
                in_use = e.errno == errno.EADDRINUSE or getattr(e, "winerror", None) == 10048
                if no_v6 or (port == 0 and in_use):
                    srv6 = None
                else:
                    srv4.server_close()
                    srv4 = None
                    last_err = (port, e)
                    continue
            servers = [s for s in (srv4, srv6) if s is not None]
            break
        except OSError as e:
            if srv4 is not None:
                srv4.server_close()
            last_err = (port, e)
    if not servers:
        port, e = last_err
        tried = f" (tried {', '.join(str(p) for p in ports)})" if len(ports) > 1 else ""
        die(f"cannot listen on 127.0.0.1:{port} ({e.strerror or type(e).__name__}){tried}: another program, or another `mreg login`, "
            f"holds that port, and the sign-in service accepts only configured loopback ports; close it and run the command again")
    redirect = f"http://localhost:{servers[0].server_port}/callback"
    shared = {"result": None}
    cb_lock = threading.Lock()
    verifier = _b64u(os.urandom(48))
    state = _b64u(os.urandom(24))
    for s in servers:
        s._shared, s.result, s.lock, s.expected_state, s.timeout = shared, None, cb_lock, state, 0.25
    params = {"client_id": client, "response_type": "code", "scope": "openid email", "redirect_uri": redirect, "state": state,
              "code_challenge": _b64u(hashlib.sha256(verifier.encode("ascii")).digest()), "code_challenge_method": "S256"}
    if provider:
        params["identity_provider"] = PROVIDERS[provider]
    url = auth + "/oauth2/authorize?" + urllib.parse.urlencode(params)
    try:
        if no_browser:
            print("open this address in your browser to sign in:\n  " + url)
        elif _open_browser(url):
            print("opened your browser to sign in; if nothing appeared, open this address by hand:\n  " + url)
        else:
            print("could not open a browser; open this address by hand:\n  " + url)
        print(f"waiting for the sign-in (up to {timeout:g} s; Ctrl-C cancels) ...", flush=True)
        deadline = time.monotonic() + timeout
        while shared["result"] is None and time.monotonic() < deadline:
            rem = max(0.01, min(0.1, deadline - time.monotonic()))
            ready, _, _ = select.select(servers, [], [], rem)
            for s in ready:
                s.handle_request()
    except KeyboardInterrupt:
        print("mreg: cancelled; nothing was changed", file=sys.stderr)
        raise SystemExit(130)
    finally:
        for s in servers:
            s.server_close()
    r = shared["result"]
    if r is None:
        die(f"no sign-in response within {timeout:g} s (browser closed, or sign-in abandoned?); nothing was changed")
    if "error" in r:
        die("sign-in was not completed (%s); nothing was changed" % re.sub(r"[^A-Za-z0-9_ .-]", "", r["error"]))
    if not hmac.compare_digest(r["state"].encode("utf-8"), state.encode("ascii")):
        die("state mismatch: the response at the callback did not belong to this sign-in request; refused, nothing was changed")
    idt = _exchange(auth, client, redirect, r["code"], verifier)
    register_secret(idt)
    return idt


def _exchange(auth, client, redirect, code, verifier):
    body = urllib.parse.urlencode({"grant_type": "authorization_code", "client_id": client, "code": code,
                                   "redirect_uri": redirect, "code_verifier": verifier}).encode("ascii")
    req = urllib.request.Request(auth + "/oauth2/token", data=body, headers={
        "Content-Type": "application/x-www-form-urlencoded", "User-Agent": "mreg/" + VERSION})
    try:
        with _no_redirect_open(req, timeout=30) as r:
            doc = json.loads(r.read(1 << 20))
    except urllib.error.HTTPError as e:
        die(f"the sign-in service refused the code ({_err_code(e)}); nothing was changed")
    except (OSError, ValueError) as e:
        die(f"cannot get a token from the sign-in service ({type(e).__name__}); nothing was changed")
    tok = doc.get("id_token") if isinstance(doc, dict) else None
    if not isinstance(tok, str) or tok.count(".") != 2:
        die("the sign-in service returned no ID token; nothing was changed")
    return tok


def keys_call(method, path, id_token, body=None, keys_url=None):
    """(HTTP status, {"error": code} or the JSON answer) from the key service. Raises SystemExit if it cannot be reached."""
    base_url = _validate_endpoint_url("MREG_KEYS_URL", keys_url) if keys_url else (
        _endpoint("MREG_KEYS_URL", KEYS_URL) if os.environ.get("MREG_KEYS_URL") else discover_auth_config()["keys_url"]
    )
    req = urllib.request.Request(base_url + path, method=method,
                                 data=None if body is None else json.dumps(body).encode("utf-8"),
                                 headers={"Authorization": "Bearer " + id_token, "Content-Type": "application/json",
                                          "User-Agent": "mreg/" + VERSION})
    try:
        with _no_redirect_open(req, timeout=30) as r:
            return r.status, json.loads(r.read(1 << 20) or b"{}")
    except urllib.error.HTTPError as e:
        return e.code, {"error": _err_code(e)}
    except (OSError, ValueError) as e:
        die(f"cannot reach the key service ({type(e).__name__})")


def decode_key(tok):
    """The payload of a per-user key {v,k,o,s,i}, or None when `tok` is not one. The signature is NOT checked: only the
    registry holds the secret. Used by whoami, logout and the create check."""
    m = KEY_RE.match(tok or "")
    if not m:
        return None
    try:
        p = json.loads(base64.urlsafe_b64decode(m.group(1) + "=" * (-len(m.group(1)) % 4)))
    except ValueError:
        return None
    ok = (isinstance(p, dict) and p.get("v") == 1 and all(isinstance(p.get(k), str) for k in "kos")
          and isinstance(p.get("i"), int) and not isinstance(p.get("i"), bool))
    return p if ok else None


def create_key(id_token, label, auth_cfg=None):
    keys_url = auth_cfg["keys_url"] if auth_cfg else None
    account_page = auth_cfg["account_page"] if auth_cfg else ACCOUNT_PAGE
    st, doc = keys_call("POST", "/keys", id_token, {"label": label}, keys_url=keys_url)
    if st == 409 and doc.get("error") == "key_limit":
        die(f"you already have the most active keys the service allows ({doc.get('max', 10)}); revoke one at {account_page} "
            "and run `mreg login` again; nothing was changed")
    if st == 401:
        die("the key service refused the sign-in token (401); sign in again; nothing was changed")
    if st != 201 or not isinstance(doc, dict):
        die(f"the key service did not create a key (HTTP {st}, {doc.get('error') if isinstance(doc, dict) else '?'}); nothing was changed")
    key, kid, lab = doc.get("key"), doc.get("id"), doc.get("label")
    info = decode_key(key if isinstance(key, str) else "")
    if info is None or info["k"] != kid or not isinstance(kid, str) or not isinstance(lab, str):
        die("the key service answered with something that is not a key; nothing was changed")
    return key, kid, lab


def _win_security_apis():
    import ctypes
    from ctypes import wintypes
    k32 = ctypes.WinDLL("kernel32", use_last_error=True)
    adv = ctypes.WinDLL("advapi32", use_last_error=True)
    k32.GetCurrentProcess.restype = wintypes.HANDLE
    k32.LocalFree.argtypes = [ctypes.c_void_p]
    k32.LocalFree.restype = ctypes.c_void_p
    k32.CloseHandle.argtypes = [wintypes.HANDLE]
    k32.CloseHandle.restype = wintypes.BOOL
    adv.OpenProcessToken.argtypes = [wintypes.HANDLE, wintypes.DWORD, ctypes.POINTER(wintypes.HANDLE)]
    adv.OpenProcessToken.restype = wintypes.BOOL
    adv.GetTokenInformation.argtypes = [wintypes.HANDLE, wintypes.DWORD, ctypes.c_void_p, wintypes.DWORD, ctypes.POINTER(wintypes.DWORD)]
    adv.GetTokenInformation.restype = wintypes.BOOL
    adv.ConvertSidToStringSidW.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_void_p)]
    adv.ConvertSidToStringSidW.restype = wintypes.BOOL
    adv.ConvertStringSecurityDescriptorToSecurityDescriptorW.argtypes = [
        wintypes.LPCWSTR, wintypes.DWORD, ctypes.POINTER(ctypes.c_void_p), ctypes.POINTER(wintypes.ULONG),
    ]
    adv.ConvertStringSecurityDescriptorToSecurityDescriptorW.restype = wintypes.BOOL
    adv.GetSecurityDescriptorDacl.argtypes = [
        ctypes.c_void_p, ctypes.POINTER(wintypes.BOOL), ctypes.POINTER(ctypes.c_void_p), ctypes.POINTER(wintypes.BOOL),
    ]
    adv.GetSecurityDescriptorDacl.restype = wintypes.BOOL
    adv.SetNamedSecurityInfoW.argtypes = [
        wintypes.LPCWSTR, wintypes.DWORD, wintypes.DWORD, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p,
    ]
    adv.SetNamedSecurityInfoW.restype = wintypes.DWORD
    adv.GetNamedSecurityInfoW.argtypes = [
        wintypes.LPCWSTR, wintypes.DWORD, wintypes.DWORD,
        ctypes.POINTER(ctypes.c_void_p), ctypes.POINTER(ctypes.c_void_p),
        ctypes.POINTER(ctypes.c_void_p), ctypes.POINTER(ctypes.c_void_p),
        ctypes.POINTER(ctypes.c_void_p),
    ]
    adv.GetNamedSecurityInfoW.restype = wintypes.DWORD
    adv.ConvertSecurityDescriptorToStringSecurityDescriptorW.argtypes = [
        ctypes.c_void_p, wintypes.DWORD, wintypes.DWORD, ctypes.POINTER(ctypes.c_void_p), ctypes.POINTER(wintypes.ULONG),
    ]
    adv.ConvertSecurityDescriptorToStringSecurityDescriptorW.restype = wintypes.BOOL
    return ctypes, wintypes, k32, adv


def _win_set_owner_only_acl(path):
    if sys.platform != "win32":
        return False
    try:
        ctypes, wintypes, k32, adv = _win_security_apis()
        h_tok = wintypes.HANDLE()
        if not adv.OpenProcessToken(k32.GetCurrentProcess(), 0x0008, ctypes.byref(h_tok)):
            return False
        sid_ptr = ctypes.c_void_p()
        p_sd = ctypes.c_void_p()
        try:
            needed = wintypes.DWORD(0)
            adv.GetTokenInformation(h_tok, 1, None, 0, ctypes.byref(needed))
            if not needed.value:
                return False
            buf = ctypes.create_string_buffer(needed.value)
            if not adv.GetTokenInformation(h_tok, 1, buf, needed.value, ctypes.byref(needed)):
                return False
            user_sid = ctypes.c_void_p.from_buffer(buf).value
            if not user_sid or not adv.ConvertSidToStringSidW(user_sid, ctypes.byref(sid_ptr)) or not sid_ptr.value:
                return False
            sid_str = ctypes.wstring_at(sid_ptr.value)
            sddl = f"D:PAI(A;;FA;;;{sid_str})"
            if not adv.ConvertStringSecurityDescriptorToSecurityDescriptorW(sddl, 1, ctypes.byref(p_sd), None) or not p_sd.value:
                return False
            present, p_dacl, defaulted = wintypes.BOOL(0), ctypes.c_void_p(), wintypes.BOOL(0)
            if not adv.GetSecurityDescriptorDacl(p_sd, ctypes.byref(present), ctypes.byref(p_dacl), ctypes.byref(defaulted)):
                return False
            rc = adv.SetNamedSecurityInfoW(os.path.abspath(path), 1, 0x00000004 | 0x80000000, None, None, p_dacl, None)
            return rc == 0
        finally:
            if p_sd.value:
                k32.LocalFree(p_sd.value)
            if sid_ptr.value:
                k32.LocalFree(sid_ptr.value)
            k32.CloseHandle(h_tok)
    except Exception:
        return False


def _win_has_protected_acl(path):
    if sys.platform != "win32":
        return False
    try:
        ctypes, _wintypes, k32, adv = _win_security_apis()
        p_sd = ctypes.c_void_p()
        sddl_ptr = ctypes.c_void_p()
        try:
            rc = adv.GetNamedSecurityInfoW(os.path.abspath(path), 1, 0x00000004, None, None, None, None, ctypes.byref(p_sd))
            if rc != 0 or not p_sd.value:
                return False
            if not adv.ConvertSecurityDescriptorToStringSecurityDescriptorW(p_sd, 1, 0x00000004, ctypes.byref(sddl_ptr), None):
                return False
            if not sddl_ptr.value:
                return False
            return ctypes.wstring_at(sddl_ptr.value).startswith("D:P")
        finally:
            if sddl_ptr.value:
                k32.LocalFree(sddl_ptr.value)
            if p_sd.value:
                k32.LocalFree(p_sd.value)
    except Exception:
        return False


def registry_base():
    base = os.environ.get("MREG_REGISTRY", "https://mathregistry.com").rstrip("/")
    check_registry_url(base)
    if not base.startswith(("https://", "http://")):
        die(f"`mreg login` needs an http(s) registry, and MREG_REGISTRY is {base!r}")
    return _validate_endpoint_url("MREG_REGISTRY", base)


def registry_accepts(key):
    """None when one authenticated request to the registry succeeds with `key`, else a short reason. A path that does not
    exist answers 404 to a valid token (never 403), so a 404 counts as accepted."""
    req = urllib.request.Request(registry_base() + "/v1/index/trains.json", headers={
        "x-mreg-token": key, "User-Agent": "mreg/" + VERSION, "Accept-Encoding": "identity"})
    try:
        with _no_redirect_open(req, timeout=30):
            return None
    except urllib.error.HTTPError as e:
        return None if e.code == 404 else f"HTTP {e.code}"
    except (OSError, ValueError) as e:
        return f"cannot reach the registry ({type(e).__name__})"


def store_token(key):
    """Write ~/.mreg/token: a temporary file created owner-only (POSIX mode 0600, directory 0700; Windows protected owner-only DACL),
    then renamed over the old one."""
    p = token_path()
    d = os.path.dirname(p)
    os.makedirs(d, mode=0o700, exist_ok=True)
    tmp = _tmp_name(p)
    fd = os.open(tmp, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        with os.fdopen(fd, "w", encoding="ascii", newline="\n") as f:
            f.write(key + "\n")
            f.flush()
            os.fsync(f.fileno())
        if sys.platform == "win32":
            _win_set_owner_only_acl(tmp)
        os.replace(tmp, p)
    except BaseException:
        try:
            os.remove(tmp)
        except OSError:
            pass
        raise
    return p


def cmd_login(a):
    label = clean_label(a.label) if a.label is not None else default_label()
    if label is None:
        die("--label must be 1 to 64 characters without control characters or < >")
    base = registry_base()
    cfg = discover_auth_config(base)
    if os.environ.get("MREG_TOKEN"):
        print("note: MREG_TOKEN is set in this environment; it takes precedence over the stored key until you unset it")
    idt = signin(a.provider, a.timeout, a.no_browser, auth_cfg=cfg)
    register_secret(idt)
    key, kid, lab = create_key(idt, label, auth_cfg=cfg)
    register_secret(key)
    problem = registry_accepts(key)
    if problem:
        revoked = keys_call("DELETE", "/keys/" + kid, idt, keys_url=cfg["keys_url"])[0] == 200
        die(f"the registry did not accept the new key {kid} ({problem}); "
            + ("the key was revoked again; " if revoked else f"it could NOT be revoked: revoke it at {cfg['account_page']}; ")
            + "the stored key was not changed")
    try:
        path = store_token(key)
    except OSError as e:
        revoked = keys_call("DELETE", "/keys/" + kid, idt, keys_url=cfg["keys_url"])[0] == 200
        die(f"cannot write {token_path()} ({e.strerror or type(e).__name__}); "
            + ("the new key was revoked again" if revoked else f"the new key {kid} could NOT be revoked: revoke it at {cfg['account_page']}"))
    print(f"logged in: key {kid} (label {lab!r}) stored in {path}")
    if sys.platform == "win32":
        if _win_has_protected_acl(path):
            print("note: Windows: protected owner-only ACL applied on the token file")
        else:
            print("note: Windows: mreg could not restrict the ACL on that file; it has the access rules of your user profile folder")
    else:
        print("the file is readable by you only (mode 0600)")


def cmd_logout(a):
    p = token_path()
    if os.environ.get("MREG_TOKEN"):
        print("note: MREG_TOKEN is set in this environment; logout does not touch the environment")
    tok = open(p, encoding="ascii", errors="replace").read().strip() if os.path.exists(p) else None
    if not tok:
        if a.revoke:
            die(f"nothing to revoke: no key is stored in {p}")
        print(f"no stored key ({p}); nothing to do")
        return
    info = decode_key(tok)
    if a.revoke:
        if info is None:
            die("--revoke: the stored value is not a per-user key (the old shared token was retired on 2026-11-12 and cannot be revoked); "
                "run `mreg logout` without --revoke")
        cfg = discover_auth_config(registry_base() if os.environ.get("MREG_REGISTRY", "").startswith(("http://", "https://")) or not os.environ.get("MREG_REGISTRY") else None)
        # the key service accepts only a sign-in token, never the key itself, so revoking needs a fresh sign-in
        st, doc = keys_call("DELETE", "/keys/" + info["k"], signin(None, a.timeout, a.no_browser, auth_cfg=cfg), keys_url=cfg["keys_url"])
        if st != 200:
            die(f"the key service did not revoke key {info['k']} ({'not found under the account you just signed in with: ' if st == 404 else ''}"
                f"HTTP {st}, {doc.get('error')}); the stored file was kept. Revoke it at {cfg['account_page']}, or `mreg logout` to just delete the file")
        print(f"revoked key {info['k']} at the service; the registry stops accepting it within about a minute")
    os.remove(p)
    print(f"deleted {p}")
    if not a.revoke:
        if info:
            print(f"note: key {info['k']} still works until it is revoked: `mreg logout --revoke` (asks you to sign in) or {ACCOUNT_PAGE}")
        else:
            print("note: that was not a per-user key; if it was the old shared token, it was retired on 2026-11-12 and the registry refuses it")


def cmd_whoami(a):
    tok, src = read_token()
    if tok is None:
        print(f"no key stored: MREG_TOKEN is not set and {token_path()} does not exist or is empty; run `mreg login`")
        sys.exit(1)
    print("source: " + src)
    if tok.startswith("mreg_"):
        info = decode_key(tok)
        if info is None:
            print("kind: looks like a per-user key (mreg_...) but it is damaged and cannot be decoded; run `mreg login`")
            sys.exit(1)
        try:
            issued = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(info["i"]))
        except (OverflowError, OSError, ValueError):
            issued = "?"
        print(f"kind: per-user key\nkey id: {info['k']}\nowner: {info['o']}\nscope: {info['s']}\nissued: {issued}")
        _json_data["whoami"] = {"kind": "per_user_key", "source": src, "key_id": info["k"], "owner": info["o"], "scope": info["s"],
                                "issued": issued, "signature_checked": False}
        print("decoded locally: the signature is not checked (only the registry has the secret), and a revoked key still decodes")
    elif re.fullmatch(r"[\x21-\x7e]{1,128}", tok):
        print("kind: the old shared access token (retired on 2026-11-12: the registry refuses it with 403, as it refuses any stored value that is not a per-user key); `mreg login` replaces it")
    else:
        print("kind: not recognised (neither a per-user key nor the old shared token); run `mreg login`")
        sys.exit(1)


# ---------------------------------------------------------------- named import: declaration -> chunks (NAMED_IMPORT.md)
# `mreg add owner/pkg#Decl.name` resolves the declaration to its chunk with the build's index tables (no Lean), takes the
# transitive closure of the chunk graph, fetches only the chunks of that cone that the local content-addressed store does
# not hold, installs them where the module names `Mreg.X<2 hex>.C<id>` say, and writes mreg-chunks.lock.json.
# FINAL serving layout (agreed 2026-11-10, with a build number, objects never overwritten):
#   <registry>/x/decl/<train>/current.json                         pointer (short cache): build, variants, manifest_sha256,
#                                                                  index_sha256 of the three index files
#   <registry>/x/decl/<train>/<build>/{checking,full}/X<2 hex>/C<id>.olean.zst
#   <registry>/x/decl/<train>/<build>/index/{assignment,chunk_edges,manifest}.tsv.gz
# assignment: name, exact_name, module, kind, in_toolchain, chunk   (in_toolchain=1 rows have an empty chunk)
# chunk_edges: chunk, imports_chunk     manifest: variant, key, id, sha256_raw, bytes_raw, sha256_stored, bytes_stored, n_decls

import array as _array, gzip as _gzip, sqlite3 as _sqlite3, tempfile as _tempfile, pathlib as _pathlib, shutil, zlib

NI_SCHEMA = "mreg-named-import/1"
CHUNK_LOCK = "mreg-chunks.lock.json"
CHUNK_LOCK_SCHEMA = "mreg-chunks-lock/1"
POINTER_SCHEMA = "mreg-decl-store/1"
MARKER = ".mreg-chunks.json"
VARIANTS = ("checking", "full")
INDEX_FILES = ("assignment.tsv.gz", "chunk_edges.tsv.gz", "manifest.tsv.gz")
ASSIGN_COLUMNS = ("name", "exact_name", "module", "kind", "in_toolchain", "chunk")
EDGE_COLUMNS = ("chunk", "imports_chunk")
MANIFEST_COLUMNS = ("variant", "key", "id", "sha256_raw", "bytes_raw", "sha256_stored", "bytes_stored", "n_decls")
DEFAULT_MAX_REQUESTS = 2000
# One fixed statement of what a chunk bundle is for. It is in every JSON document of the named-import commands (field
# `supports`) and in the last line of their human output. Nothing here may suggest that proofs can be written against chunks.
SUPPORTS = ("kernel checking and reference to declarations by name (variant full adds compiled code, reducibility, structure and "
            "projection info, docstrings); neither carries instances, simp sets, notation, parsers, macros or tactics, so chunks "
            "alone are not a base for writing new proofs")
EXIT = {"ok": 0, "error": 1, "unknown_declaration": 10, "ambiguous_name": 11, "not_on_train": 12, "auth": 13,
        "hash_mismatch": 14, "forbidden_mix": 15, "network": 16, "missing_object": 17, "build_removed": 18,
        "index_unavailable": 19, "toolchain_mismatch": 20, "over_budget": 21,
        # added with `mreg check` / `why` (phase A): no existing code names these
        "unverified_refused": REFUSED_EXIT,
        "own_code": 22, "replay_failed": 23, "axiom_not_allowed": 24, "tool_missing": 25, "not_in_project": 26}
_NAME_OK = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*$")
_HEX32 = re.compile(r"^[0-9a-f]{32}$")
_HEX64 = re.compile(r"^[0-9a-f]{64}$")


class NIError(Exception):
    def __init__(self, kind, message, **extra):
        super().__init__(message)
        self.kind, self.message, self.extra = kind, message, extra
        self.code = EXIT[kind]


def _not_found(e):
    """A 404 from the registry. A 451 takedown also has kind `missing_object` (exit 17) but is never treated as "not found": the
    callers that fall back or translate on a 404 (no pointer, no train document, removed build) let a takedown through unchanged."""
    return e.kind == "missing_object" and e.extra.get("http_status") != 451


class RangeError(Exception):
    """One range request failed. kind: bad_range, status_200, status, content_range, missing, network, short, mismatch. `retry`: worth
    asking the same range again (network failure, short body, 429/5xx); the others fall back to per-chunk files at once."""
    def __init__(self, kind, message, retry=False, retry_after=None):
        super().__init__(message)
        self.kind, self.message, self.retry, self.retry_after = kind, message, retry, retry_after


class _Quiet(NIError):
    """The command already printed its own result document; exit with the code, print nothing more."""


def ni_path(train, build=None, *parts):
    p = f"/x/decl/{train}"
    if build is None:
        return p + "/current.json"
    return "/".join([p, build] + list(parts))


class Fetcher:
    """GET of registry paths with the error classes the named import reports: auth (403, or no token), missing (404),
    network (everything else, after retries). file:// registries read a directory. Counters are thread safe."""

    def __init__(self):
        self.base = os.environ.get("MREG_REGISTRY", "https://mathregistry.com").rstrip("/")
        why = registry_url_problem(self.base)
        if why:
            raise NIError("error", f"MREG_REGISTRY is refused: {why}. The registry address is an address only; the key goes in "
                          "MREG_TOKEN or ~/.mreg/token")
        self.kind = "file" if self.base.startswith("file:") else "http"
        if self.base.startswith("s3://"):
            raise NIError("error", "named import supports https and file:// registries only")
        self.requests, self.bytes, self._lock = 0, 0, threading.Lock()
        self._tl = threading.local()
        self.retries = int(os.environ.get("MREG_RETRIES", "3"))
        self.backoff = float(os.environ.get("MREG_BACKOFF", "1"))
        self.timeout = float(os.environ.get("MREG_TIMEOUT", "60"))
        if self.kind == "file":
            self.root = urllib.request.url2pathname(urllib.parse.urlparse(self.base).path)
            self.tok = None
        else:
            if not _url_is_https_or_loopback(self.base):
                raise NIError("error", "registry address must be https (http only for localhost) or file://")
            self.tok = read_token()[0]

    def _count(self, n):
        with self._lock:
            self.requests += 1
            self.bytes += n

    def _count_bytes(self, n):
        with self._lock:
            self.bytes += n

    # ---- single-range reads of an archive (the packed path) -------------------------------------------------------------
    # One connection per worker thread, kept alive. Only ever `Range: bytes=<s>-<e-1>` with 0 <= s < e <= the object's size (checked
    # BEFORE sending, so a reversed, empty, beyond-the-object or suffix form cannot be sent). A reply is accepted only as status 206
    # with a Content-Range equal to what was asked; anything else is a RangeError for that range and its body is NOT read (a 200
    # to a range request is the whole object).
    def _conn(self):
        c = getattr(self._tl, "conn", None)
        if c is None:
            u = urllib.parse.urlparse(self.base)
            cls = http.client.HTTPSConnection if u.scheme == "https" else http.client.HTTPConnection
            c = self._tl.conn = cls(u.hostname, u.port, timeout=self.timeout)
            self._tl.prefix = u.path.rstrip("/")
        return c

    def drop_conn(self):
        c = getattr(self._tl, "conn", None)
        self._tl.conn = None
        if c is not None:
            try:
                c.close()
            except Exception:
                pass

    def open_range(self, path, s, e, size):
        """A file-like object over bytes [s, e) of the object at `path` (whose size is `size`), or RangeError."""
        if not (isinstance(s, int) and isinstance(e, int) and isinstance(size, int) and 0 <= s < e <= size):
            raise RangeError("bad_range", f"refusing to send range [{s}, {e}) of an object of {size} bytes")
        if self.kind == "file":
            p = os.path.join(self.root, *[x for x in path.split("/") if x])
            try:
                with open(p, "rb") as fh:
                    if os.path.getsize(p) != size:
                        self._count(0)
                        raise RangeError("content_range", f"{path} has {os.path.getsize(p)} bytes, expected {size}")
                    fh.seek(s)
                    data = fh.read(e - s)
            except (FileNotFoundError, NotADirectoryError):
                self._count(0)
                raise RangeError("missing", f"404: {path}")
            except OSError as ex:
                self._count(0)
                raise RangeError("network", f"cannot read {path}: {ex}", retry=True)
            self._count(len(data))
            return io.BytesIO(data)
        if not self.tok:
            raise NIError("auth", "no access token: run `mreg login`, or set MREG_TOKEN or create ~/.mreg/token")
        h = {"x-mreg-token": self.tok, "User-Agent": "mreg/" + VERSION, "Accept-Encoding": "identity", "Range": f"bytes={s}-{e - 1}"}
        c = self._conn()
        try:
            c.request("GET", self._tl.prefix + path, headers=h)
            r = c.getresponse()
        except (OSError, http.client.HTTPException) as ex:
            self.drop_conn()
            self._count(0)
            raise RangeError("network", f"{type(ex).__name__}: {ex}", retry=True)
        self._count(0)
        st = r.status
        if st == 206:
            want = f"bytes {s}-{e - 1}/{size}"
            cr, cl = r.getheader("Content-Range"), r.getheader("Content-Length")
            if cr != want or (cl is not None and cl != str(e - s)):
                self.drop_conn()
                raise RangeError("content_range", f"asked bytes {s}-{e - 1} of {size}; the reply says Content-Range {cr!r}, "
                                 f"Content-Length {cl!r}")
            return r
        self.drop_conn()                  # the body is never read: for a 200 it would be the whole object
        if st == 451:
            raise NIError("missing_object", TAKEDOWN_MESSAGE.format(path=path), path=path, http_status=451)
        dn = denial_of(r.headers)
        if dn:
            raise NIError(DENIAL_KIND[dn], f"{st} from the registry for {path}: {DENIAL_MESSAGES[dn]}", http_status=st, denial=dn)
        if st == 403:
            raise NIError("auth", f"403 from the registry for {path}: the token is missing, wrong or revoked (`mreg whoami`, `mreg login`)")
        if st == 404:
            raise RangeError("missing", f"404: {path}")
        if st == 200:
            raise RangeError("status_200", f"HTTP 200 (the whole object) in answer to a range request for {path}")
        raise RangeError("status", f"HTTP {st} for a range of {path}", retry=st in (429, 500, 502, 503, 504),
                         retry_after=retry_after_of(r.headers) if st in (429, 503) else None)

    def get(self, path, max_bytes=None):
        # TEST ONLY: MREG_TEST_POINTER_FILE serves a local file in place of the pointer (`<registry>/x/decl/<train>/current.json`), so a
        # pointer can be tried through the real client before it is published. Everything else still goes to the registry.
        tp = os.environ.get("MREG_TEST_POINTER_FILE")
        if tp and path.startswith("/x/decl/") and path.endswith("/current.json") and path.count("/") == 4:
            try:
                with open(tp, "rb") as f:
                    body = f.read() if max_bytes is None else f.read(max_bytes + 1)
            except OSError as e:
                raise NIError("network", f"cannot read MREG_TEST_POINTER_FILE: {e}")
            self._count(len(body))
            return body
        if self.kind == "file":
            p = os.path.join(self.root, *[x for x in path.split("/") if x])
            try:
                with open(p, "rb") as f:
                    body = f.read() if max_bytes is None else f.read(max_bytes + 1)
            except (FileNotFoundError, NotADirectoryError):
                self._count(0)
                raise NIError("missing_object", f"404: {path}", path=path)
            except OSError as e:
                raise NIError("network", f"cannot read {path}: {e}")
            self._count(len(body))
            return body
        if not self.tok:
            raise NIError("auth", "no access token: run `mreg login`, or set MREG_TOKEN or create ~/.mreg/token")
        h = {"x-mreg-token": self.tok, "User-Agent": "mreg/" + VERSION, "Accept-Encoding": "identity"}
        err = None
        for attempt in range(self.retries + 1):
            try:
                with _safe_redirect_open(urllib.request.Request(self.base + path, headers=h), timeout=self.timeout) as r:
                    body = r.read() if max_bytes is None else r.read(max_bytes + 1)
                self._count(len(body))
                return body
            except urllib.error.HTTPError as e:
                self._count(0)
                if e.code in (301, 302, 303, 307, 308):
                    raise NIError("network", f"cannot fetch {path}: {e}")
                if e.code == 451:
                    # a takedown is final: no retry. Exit code 17 (missing_object, the existing code for "the registry no longer has it").
                    raise NIError("missing_object", TAKEDOWN_MESSAGE.format(path=path), path=path, http_status=451)
                dn = denial_of(e.headers)
                if dn:
                    raise NIError(DENIAL_KIND[dn], f"{e.code} from the registry for {path}: {DENIAL_MESSAGES[dn]}",
                                  http_status=e.code, denial=dn)
                if e.code == 403:
                    raise NIError("auth", f"403 from the registry for {path}: the token is missing, wrong or revoked "
                                  "(`mreg whoami`, `mreg login`)")
                if e.code == 404:
                    raise NIError("missing_object", f"404: {path}", path=path)
                err = e
                if e.code in (429, 503):
                    ra = retry_after_of(e.headers)
                    if ra is not None and attempt < self.retries:
                        time.sleep(ra)
                        continue
            except Exception as e:
                self._count(0)
                err = e
            if attempt < self.retries:
                time.sleep(self.backoff * (attempt + 1))
        raise NIError("network", f"cannot fetch {path}: {err}")

    def json(self, path):
        body = self.get(path)
        try:
            return json.loads(body)
        except ValueError:
            raise NIError("error", f"{path} is not JSON")


class Store:
    """The local content-addressed store: objects/<aa>/<sha256 of the stored bytes>, index/<train>/<build>/ (index cache)."""

    def __init__(self, root=None):
        self.root = root or os.environ.get("MREG_STORE") or os.path.join(os.path.expanduser("~"), ".mreg", "store")

    def obj(self, sha_stored):
        return os.path.join(self.root, "objects", sha_stored[:2], sha_stored)

    def index_dir(self, train, build):
        return os.path.join(self.root, "index", train, build)


# ---- index tables -> compact lookup ------------------------------------------------------------------------------

def _tsv_open(path):
    f = _gzip.open(path, "rb")
    hdr = f.readline().rstrip(b"\r\n").split(b"\t")
    return f, [h.decode() for h in hdr]


def _bad_index(msg):
    return NIError("index_unavailable", msg + "; no answer can be computed from this index (it is not a 'not found')")


def _header(path, want, what):
    f, hdr = _tsv_open(path)
    missing = [c for c in want if c not in hdr]
    if missing:
        f.close()
        raise _bad_index(f"{what} has columns {hdr}; the final layout needs {list(want)} (missing {missing})")
    return f, {c: hdr.index(c) for c in want}


def build_lookup(d):
    """From d/assignment.tsv.gz and d/chunk_edges.tsv.gz (FINAL columns, see the header comment) make decl.sqlite (names),
    ids.bin (sorted 16-byte chunk ids), off.bin and tgt.bin (the chunk graph as CSR, uint32 little endian).
    Rows with in_toolchain=1 have an empty chunk and are never in the graph; every other row has a 32-hex chunk. The edge table
    has no toolchain rows: an endpoint the assignment does not know is an error, never skipped. Any malformed row makes the
    whole index unusable (exit 19)."""
    t0 = time.time()
    ap, ep = os.path.join(d, "assignment.tsv.gz"), os.path.join(d, "chunk_edges.tsv.gz")
    f, ix = _header(ap, ASSIGN_COLUMNS, "assignment.tsv.gz")
    chunks = set()
    nrow = 0
    try:
        for line in f:
            p = line.rstrip(b"\r\n").split(b"\t")
            nrow += 1
            tcf, ch = p[ix["in_toolchain"]], p[ix["chunk"]]
            if tcf == b"1":
                if ch:
                    raise _bad_index(f"assignment row {nrow + 1}: in_toolchain=1 but chunk is {ch!r}")
            elif tcf == b"0":
                if not _HEX32.match(ch.decode("ascii", "replace")):
                    raise _bad_index(f"assignment row {nrow + 1}: in_toolchain=0 but chunk {ch!r} is not 32 lower-case hex digits")
                chunks.add(ch)
            else:
                raise _bad_index(f"assignment row {nrow + 1}: in_toolchain is {tcf!r}, expected 0 or 1")
    except IndexError:
        raise _bad_index("assignment.tsv.gz has a row with too few columns")
    finally:
        f.close()
    ids = sorted(chunks)
    idmap = {v: i for i, v in enumerate(ids)}
    n = len(ids)
    modules, kinds = {}, {}
    db_path = os.path.join(d, "decl.sqlite")
    if os.path.exists(db_path):
        os.unlink(db_path)
    db = _sqlite3.connect(db_path)
    db.executescript("PRAGMA journal_mode=OFF; PRAGMA synchronous=OFF; "
                     "CREATE TABLE decl(name TEXT NOT NULL, exact TEXT, mod INTEGER NOT NULL, kind INTEGER NOT NULL, "
                     "tc INTEGER NOT NULL, chunk INTEGER);"
                     "CREATE TABLE modules(id INTEGER PRIMARY KEY, name TEXT); CREATE TABLE kinds(id INTEGER PRIMARY KEY, name TEXT);"
                     "CREATE TABLE meta(k TEXT PRIMARY KEY, v TEXT);")
    f, ix = _header(ap, ASSIGN_COLUMNS, "assignment.tsv.gz")
    batch, ndecl, ntc = [], 0, 0
    for line in f:
        p = line.rstrip(b"\r\n").split(b"\t")
        name, exact, mod, kind = (p[ix[c]].decode("utf-8") for c in ("name", "exact_name", "module", "kind"))
        mid = modules.setdefault(mod, len(modules))
        kid = kinds.setdefault(kind, len(kinds))
        tcf = p[ix["in_toolchain"]] == b"1"
        ntc += tcf
        batch.append((name, None if exact == name else exact, mid, kid, 1 if tcf else 0, None if tcf else idmap[p[ix["chunk"]]]))
        ndecl += 1
        if len(batch) >= 50000:
            db.executemany("INSERT INTO decl VALUES (?,?,?,?,?,?)", batch)
            batch = []
    f.close()
    if batch:
        db.executemany("INSERT INTO decl VALUES (?,?,?,?,?,?)", batch)
    db.executemany("INSERT INTO modules VALUES (?,?)", [(i, m) for m, i in modules.items()])
    db.executemany("INSERT INTO kinds VALUES (?,?)", [(i, k) for k, i in kinds.items()])
    db.execute("CREATE INDEX decl_name ON decl(name)")
    db.execute("CREATE INDEX decl_exact ON decl(exact) WHERE exact IS NOT NULL")
    ef, ex = _header(ep, EDGE_COLUMNS, "chunk_edges.tsv.gz")
    ci, ii = ex["chunk"], ex["imports_chunk"]
    src, dst, mono, prev = _array.array("I"), _array.array("I"), True, 0
    sa, da = src.append, dst.append
    try:
        for line in ef:
            p = line.rstrip(b"\r\n").split(b"\t")
            s, t = idmap[p[ci]], idmap[p[ii]]
            if s < prev:
                mono = False
            prev = s
            sa(s)
            da(t)
    except KeyError as e:
        raise _bad_index(f"chunk_edges.tsv.gz names a chunk the assignment does not have: {e.args[0]!r}")
    except IndexError:
        raise _bad_index("chunk_edges.tsv.gz has a row with too few columns")
    finally:
        ef.close()
    ne = len(src)
    off = _array.array("I", bytes(4 * (n + 1)))
    for s in src:
        off[s + 1] += 1
    acc = 0
    for i in range(n + 1):
        acc += off[i]
        off[i] = acc
    if mono:
        tgt = dst
    else:
        tgt, fill = _array.array("I", bytes(4 * ne)), _array.array("I", off[:n])
        for k in range(ne):
            s = src[k]
            tgt[fill[s]] = dst[k]
            fill[s] += 1
    if sys.byteorder != "little":
        off.byteswap()
        tgt.byteswap()
    for nm, data in (("ids.bin", b"".join(bytes.fromhex(v.decode()) for v in ids)), ("off.bin", off.tobytes()),
                     ("tgt.bin", tgt.tobytes())):
        with open(os.path.join(d, nm), "wb") as g:
            g.write(data)
    meta = {"declarations": ndecl, "toolchain_declarations": ntc, "chunks": n, "edges": ne,
            "edges_sorted_by_source": mono, "built_seconds": round(time.time() - t0, 2)}
    db.executemany("INSERT INTO meta VALUES (?,?)", [(k, json.dumps(v)) for k, v in meta.items()])
    db.commit()
    db.close()
    return meta


def build_manifest_db(d):
    path = os.path.join(d, "manifest.sqlite")
    if os.path.exists(path):
        os.unlink(path)
    f, ix = _header(os.path.join(d, "manifest.tsv.gz"), MANIFEST_COLUMNS, "manifest.tsv.gz")
    db = _sqlite3.connect(path)
    db.executescript("PRAGMA journal_mode=OFF; PRAGMA synchronous=OFF; CREATE TABLE m(variant TEXT, id BLOB, sha_raw BLOB, "
                     "bytes_raw INTEGER, sha_stored BLOB, bytes_stored INTEGER, n_decls INTEGER, PRIMARY KEY(variant,id)) WITHOUT ROWID;")

    def row(p):
        g = {c: p[ix[c]] for c in MANIFEST_COLUMNS}
        return (g["variant"].decode(), bytes.fromhex(g["id"].decode()), bytes.fromhex(g["sha256_raw"].decode()), int(g["bytes_raw"]),
                bytes.fromhex(g["sha256_stored"].decode()), int(g["bytes_stored"]), int(g["n_decls"]))
    batch = []
    try:
        for line in f:
            if line.strip():
                batch.append(row(line.rstrip(b"\r\n").split(b"\t")))
            if len(batch) >= 50000:
                db.executemany("INSERT INTO m VALUES (?,?,?,?,?,?,?)", batch)
                batch = []
        if batch:
            db.executemany("INSERT INTO m VALUES (?,?,?,?,?,?,?)", batch)
    except (ValueError, IndexError, _sqlite3.IntegrityError) as e:
        raise _bad_index(f"manifest.tsv.gz is malformed: {e}")
    finally:
        f.close()
    db.commit()
    db.close()


class Lookup:
    """Read side of the compact lookup of one (train, build)."""

    def __init__(self, d):
        self.d = d
        self.db = _sqlite3.connect(_pathlib.Path(os.path.join(d, "decl.sqlite")).as_uri() + "?mode=ro", uri=True)
        mp = os.path.join(d, "manifest.sqlite")
        self.mdb = _sqlite3.connect(_pathlib.Path(mp).as_uri() + "?mode=ro", uri=True) if os.path.exists(mp) else None
        self.ids = None
        self.meta = {k: json.loads(v) for k, v in self.db.execute("SELECT k, v FROM meta")}

    def close(self):
        self.db.close()
        if self.mdb:
            self.mdb.close()

    def _load(self):
        if self.ids is None:
            rd = lambda n: open(os.path.join(self.d, n), "rb").read()
            self.ids = rd("ids.bin")
            self.off, self.tgt = _array.array("I"), _array.array("I")
            self.off.frombytes(rd("off.bin"))
            self.tgt.frombytes(rd("tgt.bin"))
            if sys.byteorder != "little":
                self.off.byteswap()
                self.tgt.byteswap()

    def chunk_hex(self, i):
        self._load()
        return self.ids[16 * i:16 * i + 16].hex()

    def find(self, name):
        q = ("SELECT d.rowid, d.name, COALESCE(d.exact, d.name), m.name, k.name, d.chunk, d.tc FROM decl d JOIN modules m ON m.id=d.mod "
             "JOIN kinds k ON k.id=d.kind WHERE ")
        rows = self.db.execute(q + "d.name=?", (name,)).fetchall() + self.db.execute(q + "d.exact=?", (name,)).fetchall()
        seen, out = set(), []
        for r in sorted(rows, key=lambda r: r[0]):
            if r[0] not in seen:
                seen.add(r[0])
                out.append({"name": r[1], "exact_name": r[2], "module": r[3], "kind": r[4], "in_toolchain": bool(r[6]),
                            "chunk": None if r[5] is None else self.chunk_hex(r[5]), "chunk_index": r[5]})
        return out

    def suggest(self, name, limit=5):
        last = name.rsplit(".", 1)[-1]
        esc = last.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_")
        return [r[0] for r in self.db.execute("SELECT name FROM decl WHERE name LIKE ? ESCAPE '\\' LIMIT ?", ("%." + esc, limit))]

    def cone(self, roots):
        """Sorted chunk indices of the transitive closure of `roots` in the chunk graph. The graph holds no toolchain chunks:
        a chunk imports the toolchain's modules by their ordinary names."""
        self._load()
        n = len(self.ids) // 16
        seen, stack, out = bytearray(n), [], []
        off, tgt = self.off, self.tgt
        for r in roots:
            if not seen[r]:
                seen[r] = 1
                stack.append(r)
        while stack:
            c = stack.pop()
            out.append(c)
            for j in range(off[c], off[c + 1]):
                t = tgt[j]
                if not seen[t]:
                    seen[t] = 1
                    stack.append(t)
        out.sort()
        return out

    def manifest(self, variant, hexid):
        r = self.mdb.execute("SELECT sha_raw, bytes_raw, sha_stored, bytes_stored, n_decls FROM m WHERE variant=? AND id=?",
                             (variant, bytes.fromhex(hexid))).fetchone()
        if r is None:
            return None
        return {"id": hexid, "sha256_raw": r[0].hex(), "bytes_raw": r[1], "sha256_stored": r[2].hex(), "bytes_stored": r[3],
                "n_decls": r[4]}


def read_pointer(f, train, path=None):
    """current.json of a train, validated. A missing pointer is `not_on_train` (the registry serves no declaration store: the
    caller may fall back to the module-level path). A pointer that exists but is unusable (not JSON, wrong schema, no index
    hashes) is `index_unavailable`, never a fallback."""
    path = path or ni_path(train)
    try:
        ptr = f.json(path)
    except NIError as e:
        if _not_found(e):
            raise NIError("not_on_train", f"train {train} has no declaration-level store on this registry "
                          f"({path} is absent)")
        if e.kind == "error":
            raise NIError("index_unavailable", f"{path} is not JSON")
        raise
    ix = ptr.get("index_sha256") if isinstance(ptr, dict) else None
    if (not isinstance(ptr, dict) or ptr.get("schema") != POINTER_SCHEMA or ptr.get("train") != train
            or not _NAME_OK.match(str(ptr.get("build", ""))) or not _HEX64.match(str(ptr.get("manifest_sha256", "")))
            or not isinstance(ptr.get("variants"), list)):
        raise NIError("index_unavailable", f"{path} is not a {POINTER_SCHEMA} pointer for train {train}; "
                      "no answer can be computed (not a 'not found')")
    if (not isinstance(ix, dict) or any(not _HEX64.match(str(ix.get(k, ""))) for k in INDEX_FILES)):
        raise NIError("index_unavailable", f"the pointer {ni_path(train)} carries no sha256 for each of {', '.join(INDEX_FILES)} "
                      "(`index_sha256`): the index hashes cannot be matched, so no answer is given (not a 'not found')")
    if ix["manifest.tsv.gz"] != ptr["manifest_sha256"]:
        raise NIError("index_unavailable", "the pointer's manifest_sha256 and index_sha256['manifest.tsv.gz'] differ; refused")
    ptr["index_sha256"] = {k: ix[k] for k in INDEX_FILES}
    return ptr


def source_route(f, train, train_doc, package, supplied_digest=None):
    if not all(_NAME_OK.fullmatch(part) for part in package.split("/")):
        raise NIError("error", "invalid package identity in declaration selection")
    record = (train_doc.get("packages") or {}).get(package, {})
    version, key = record.get("version"), record.get("build_key")
    if key is None and not supplied_digest:  # Older train catalogues predate exact source-build selection.
        return None
    if not supplied_digest and not all(isinstance(x, str) and _NAME_OK.fullmatch(x) for x in (version, key)):
        raise NIError("index_unavailable", f"invalid train source selection for {package}")
    try:
        doc = f.json(f"/v1/index/{package}.json")
    except NIError as ex:
        if _not_found(ex):
            raise NIError("index_unavailable", f"catalogue document for {package} on {train} is missing") from ex
        raise
    if not isinstance(doc, dict) or not isinstance(doc.get("versions"), dict):
        raise NIError("index_unavailable", f"invalid catalogue document for {package}")
    if supplied_digest:
        matches = [(v, b.get("build_key")) for v, release in doc["versions"].items()
                   if isinstance(release, dict) for b in release.get("builds", []) if isinstance(b, dict)
                   and isinstance(b.get("manifest"), dict) and b["manifest"].get("sha256") == supplied_digest]
        if len(matches) != 1 or not all(isinstance(x, str) and _NAME_OK.fullmatch(x) for x in matches[0]):
            raise NIError("hash_mismatch", f"expected one catalogue build for {package} at the requested manifest digest")
        version, key = matches[0]
    release = doc["versions"].get(version)
    builds = release.get("builds") if isinstance(release, dict) else None
    if not isinstance(builds, list) or not all(isinstance(b, dict) for b in builds):
        raise NIError("index_unavailable", f"invalid catalogue build list for {package}")
    matches = [b for b in builds if b.get("build_key") == key]
    if len(matches) != 1:
        raise NIError("hash_mismatch", f"train source build for {package} is absent or ambiguous in the catalogue")
    if release.get("yanked") or matches[0].get("yanked"):
        raise NIError("unverified_refused", f"the registry has withdrawn the requested version or build of {package}")
    digest = (matches[0].get("manifest") or {}).get("sha256")
    if not isinstance(digest, str) or not _HEX64.fullmatch(digest):
        raise NIError("hash_mismatch", f"missing source manifest digest for {package}")
    return {"id": package, "version": version, "build_key": key, "manifest_sha256": digest}


def discover_store(f, train, train_doc, entries, asked, supplied_digest=None):
    """Select one store whose admitted source identity matches the requested catalogue build."""
    packages = sorted({p[0] for entry in entries if (p := parse_decl(entry))})
    if asked and not _NAME_OK.fullmatch(asked):
        raise NIError("error", "invalid declaration store build")
    if supplied_digest is not None and (not _HEX64.fullmatch(supplied_digest) or len(packages) != 1):
        raise NIError("error", "--source-manifest-sha256 requires one named package and a SHA-256 digest")
    sources = [s for p in packages if (s := source_route(f, train, train_doc, p, supplied_digest))]
    explicit_release = None
    if asked:
        try:
            selected = read_pointer(f, train, ni_path(train, asked, "release.json"))
        except NIError as ex:
            if ex.kind != "not_on_train":
                raise
        else:
            if selected["build"] != asked or not receipt_pin(selected, None, asked, "checking"):
                raise NIError("hash_mismatch", "immutable store descriptor names another build or lacks a receipt")
            explicit_release = selected
        if explicit_release is None:
            current = read_pointer(f, train)
            if current["build"] != asked:
                raise NIError("not_on_train", f"no immutable release descriptor for requested build {asked} on {train}")
            return current, sources if receipt_pin(current, None, asked, "checking") else [], False
    selected = None
    routed = set()
    for source in sources:
        path = ni_path(train, "by-source", source["manifest_sha256"] + ".json")
        try:
            ptr = read_pointer(f, train, path)
        except NIError as ex:
            if ex.kind == "not_on_train":
                continue
            raise
        if not receipt_pin(ptr, None, ptr["build"], "checking"):
            raise NIError("unverified_refused", "by-source declaration store has no signed receipt")
        if explicit_release and ptr != explicit_release:
            raise NIError("hash_mismatch", "source alias differs from the requested immutable release descriptor")
        if selected and selected != ptr:
            raise NIError("forbidden_mix", "the requested declarations select different signed declaration stores")
        selected = ptr
        routed.add(source["id"])
    if selected or explicit_release:
        if routed != set(packages):
            raise NIError("hash_mismatch", "a requested package lacks its own source alias for this declaration store")
        return selected, sources, False
    current = read_pointer(f, train)
    if supplied_digest and not receipt_pin(current, None, current["build"], "checking"):
        raise NIError("unverified_refused", "exact source selection requires a signed declaration store")
    signed = receipt_pin(current, None, current["build"], "checking")
    return current, sources if signed else [], not supplied_digest


def verify_routed_sources(routes, admission, allow_unserved=False):
    if not isinstance(routes, list):
        raise NIError("hash_mismatch", "malformed exact source selection")
    owners = {s["id"]: s for s in admission["sources"]}
    missing = []
    for route in routes:
        keys = {"id", "version", "build_key", "manifest_sha256"}
        if not isinstance(route, dict) or set(route) != keys or not isinstance(route["id"], str):
            raise NIError("hash_mismatch", "malformed exact source selection")
        source = owners.get(route["id"])
        if source is None and allow_unserved:
            missing.append(route["id"])
        elif not source or any(source.get(k) != route[k] for k in keys):
            raise NIError("hash_mismatch", "requested catalogue source build differs from the signed declaration receipt")
    if missing:
        raise NIError("not_on_train", "the default declaration store does not serve " + ", ".join(missing),
                      verified_selection_unavailable=True)


def want_from_lock(lock):
    ix = lock.get("index") or {}
    if any(not _HEX64.match(str(ix.get(k, ""))) for k in INDEX_FILES) or not _HEX64.match(str(lock.get("manifest_sha256", ""))):
        raise NIError("index_unavailable", f"{CHUNK_LOCK} does not record the sha256 of all three index files")
    if ix["manifest.tsv.gz"] != lock["manifest_sha256"]:
        raise NIError("index_unavailable", f"{CHUNK_LOCK}: manifest_sha256 and index['manifest.tsv.gz'] differ")
    return {k: ix[k] for k in INDEX_FILES}


def ensure_index(f, store, train, build, want):
    """The index of one immutable build, cached under index/<train>/<build>/. Returns (dir, meta, fetched?).
    `want` = {file name: sha256 as stored} for all three index files (the pointer's or the lock's). Each file is checked
    against it as it arrives and the cache is written only when all three match; a cached index is re-checked against
    `want` (a different hash is exit 14). Nothing is ever answered from an index whose hashes were not matched."""
    d = store.index_dir(train, build)
    ready = os.path.join(d, "READY.json")

    def cached():
        if not os.path.exists(ready):
            return None
        meta = json.load(open(ready, encoding="utf-8"))
        for nm in INDEX_FILES:
            have = (meta.get("index") or {}).get(nm, {}).get("sha256")
            if have != want[nm]:
                raise NIError("hash_mismatch", f"the cached {nm} of build {build} has sha256 {have}, expected {want[nm]}", build=build)
        return d, meta, False

    hit = cached()
    if hit:
        return hit
    # One process at a time builds this index (T-C3): the others wait, then find READY.json and use it. The lock is next to the
    # directory it protects, and the check is made again once it is held.
    os.makedirs(os.path.dirname(d), exist_ok=True)
    sweep_stale_parts(os.path.dirname(d))
    try:
        with FileLock(d + ".lock"):
            hit = cached()
            if hit:
                return hit
            return _build_index(f, store, train, build, want, d)
    except TimeoutError as ex:
        raise NIError("error", str(ex))


def _build_index(f, store, train, build, want, d):
    files = {}
    for nm in ("manifest.tsv.gz", "assignment.tsv.gz", "chunk_edges.tsv.gz"):
        try:
            body = f.get(ni_path(train, build, "index", nm))
        except NIError as e:
            if _not_found(e):
                raise NIError("build_removed", f"{nm} of build {build} of train {train} is not on the registry ({e.message}); "
                              "no answer can be computed from this build", build=build)
            raise
        if sha256(body) != want[nm]:
            raise NIError("hash_mismatch", f"{nm} of build {build} has sha256 {sha256(body)}, expected {want[nm]}; nothing was cached",
                          build=build)
        files[nm] = body
    os.makedirs(os.path.dirname(d), exist_ok=True)
    tmp = _tempfile.mkdtemp(prefix=build + f".part-{os.getpid()}-", dir=os.path.dirname(d))
    try:
        for nm, b in files.items():
            with open(os.path.join(tmp, nm), "wb") as g:
                g.write(b)
        lk = build_lookup(tmp)
        build_manifest_db(tmp)
        meta = {"train": train, "build": build, "manifest_sha256": want["manifest.tsv.gz"], "lookup": lk,
                "index": {k: {"sha256": sha256(b), "bytes": len(b)} for k, b in files.items()}}
        with open(os.path.join(tmp, "READY.json"), "w", encoding="utf-8") as g:
            json.dump(meta, g, indent=1)
        if os.path.isdir(d):
            shutil.rmtree(d)       # only reached under the build lock, and only when READY.json was absent (an unfinished directory)
        _replace(tmp, d)
    except BaseException:
        shutil.rmtree(tmp, ignore_errors=True)
        raise
    return d, meta, True


# ---- forbidden mixes -----------------------------------------------------------------------------------------------

def _read_json(p):
    try:
        return json.load(open(p, encoding="utf-8"))
    except (OSError, ValueError):
        return None


def module_packages(d):
    """lake names of packages whose ORIGINAL module files could be on the search path of project d: lake-manifest.json,
    lakefile.toml requires, the module-level state and the module-level lock."""
    out = {}
    lm = _read_json(os.path.join(d, "lake-manifest.json")) or {}
    for p in lm.get("packages", []):
        out.setdefault(p.get("name"), "lake-manifest.json")
    lf = os.path.join(d, "lakefile.toml")
    if os.path.exists(lf):
        txt = open(lf, encoding="utf-8").read()
        for blk in txt.split("[[require]]")[1:]:
            m = re.search(r'name\s*=\s*"([^"]+)"', blk.split("[[", 1)[0])
            if m:
                out.setdefault(m.group(1), "lakefile.toml [[require]]")
    st = _read_json(os.path.join(d, STATE)) or {}
    for n in st.get("packages", {}):
        out.setdefault(n, STATE)
    lk = _read_json(os.path.join(d, "mreg.lock")) or {}
    for e in lk.get("packages", []):
        if e.get("from") == "registry":
            out.setdefault(e.get("lake_name"), "mreg.lock")
    return out


def reverse_mix(d, names):
    """A module-level install of `names` into a project that holds chunks of those packages."""
    lk = _read_json(os.path.join(d, CHUNK_LOCK))
    if lk and lk.get("schema") == CHUNK_LOCK_SCHEMA:
        hit = sorted(set(names) & set(lk.get("covers_packages", [])))
        if hit:
            raise NIError("forbidden_mix", f"this project holds chunks of train {lk['train']} build {lk['build']} that cover "
                          f"{', '.join(hit)}; installing their original module files as well would put both on the search path "
                          "(Lean refuses a definition that arrives under two module names)", packages=hit)


def check_mix(d, covers, train, build, variant, lock, chunk_dir, upgrade=False):
    if lock:
        if lock["train"] != train:
            raise NIError("forbidden_mix", f"chunks from two trains: the project holds train {lock['train']}, this asks for {train}")
        if lock["variant"] != variant:
            raise NIError("forbidden_mix", f"checking and full chunks in one project: the project holds {lock['variant']}, "
                          f"this asks for {variant}")
        if lock["build"] != build and not upgrade:
            raise NIError("forbidden_mix", f"chunks from two builds: the project holds build {lock['build']}, this asks for "
                          f"{build} (`mreg install --upgrade-build` moves the whole project)")
    mk = _read_json(os.path.join(chunk_dir, MARKER))
    if mk and not lock and (mk.get("train"), mk.get("variant"), mk.get("build")) != (train, variant, build):
        raise NIError("forbidden_mix", f"the chunk directory {chunk_dir} holds train {mk.get('train')} build {mk.get('build')} "
                      f"{mk.get('variant')} chunks; this asks for {train} {build} {variant}")
    mp = module_packages(d)
    hit = sorted((n, mp[n]) for n in covers if n in mp)
    if hit:
        raise NIError("forbidden_mix", "the original module files of " + ", ".join(f"{n} (from {w})" for n, w in hit) +
                      " and chunks of the same packages would both be on the search path; a project uses one or the other",
                      packages=[n for n, _ in hit])


# ---- the work ------------------------------------------------------------------------------------------------------

def chunk_rel(cid):
    return f"Mreg/X{cid[:2]}/C{cid}.olean"


def chunk_module(cid):
    return f"Mreg.X{cid[:2]}.C{cid}"


def ni_load_cfg(d):
    cfg = load_cfg(d)
    cc = dict(cfg.get("chunks") or {})
    lock = _read_json(os.path.join(d, CHUNK_LOCK))
    if lock and lock.get("schema") != CHUNK_LOCK_SCHEMA:
        raise NIError("error", f"{CHUNK_LOCK}: unknown schema {lock.get('schema')!r}")
    return cfg, cc, lock


def _root(module):
    return module.split(".", 1)[0]


def resolve_entry(lk, train_doc, entry):
    """One entry -> record. A name that only the toolchain defines (in_toolchain=1 rows) is `provided_by: toolchain`, no chunk,
    whatever package the entry names (the package must still be on the train). Otherwise the declaration must be in a module
    of the named package. Several rows with the same exact name AND chunk (a later copy points at the first owner's chunk)
    are one declaration; rows that differ in either are ambiguous."""
    pd = parse_decl(entry)
    if pd is None:
        raise NIError("error", f"{entry!r}: expected <owner/pkg>#<Decl.name>")
    pid, name = pd
    pkgs = train_doc.get("packages") or {}
    p = pkgs.get(pid)
    if p is None:
        raise NIError("not_on_train", f"{pid} is not on train {train_doc['train']}", package=pid)
    roots = set(p.get("module_roots") or [])
    modules = p.get("owned_modules")
    rows = lk.find(name)
    if not rows:
        sug = lk.suggest(name)
        raise NIError("unknown_declaration", f"{entry}: no declaration {name!r} in this train's index" +
                      (f"; did you mean {', '.join(sug)}" if sug else ""), suggestions=sug)
    mine = [r for r in rows if not r["in_toolchain"]
            and (r["module"] in modules if modules is not None else _root(r["module"]) in roots)]
    note = None
    if mine:
        keys = {(r["exact_name"], r["chunk"]) for r in mine}
        if len(keys) > 1:
            raise NIError("ambiguous_name", f"{entry}: {len(keys)} declarations have this name: " +
                          "; ".join(f"{r['exact_name']} in {r['module']}" for r in mine) + " (give the exact_name form)",
                          candidates=[{"exact_name": r["exact_name"], "module": r["module"], "chunk": r["chunk"]} for r in mine])
        if len(mine) > 1:
            note = (f"{entry}: the name appears in {len(mine)} modules ({', '.join(r['module'] for r in mine)}); "
                    "later copies point at the first owner's chunk, which is the one used")
        r = mine[0]
    else:
        tcr = [r for r in rows if r["in_toolchain"]]
        if not tcr:
            owner = next((q for q, pk in pkgs.items() if _root(rows[0]["module"]) in (pk.get("module_roots") or [])), None)
            raise NIError("unknown_declaration", f"{entry}: {name!r} is defined in module {rows[0]['module']}" +
                          (f", which belongs to {owner}; name it as {owner}#{name}" if owner else
                           f" (another package), not in {pid}"), suggestions=[])
        if len({r["exact_name"] for r in tcr}) > 1:
            raise NIError("ambiguous_name", f"{entry}: {len(tcr)} toolchain declarations have this name (give the exact_name form)",
                          candidates=[{"exact_name": r["exact_name"], "module": r["module"], "chunk": None} for r in tcr])
        r = tcr[0]
    tc = bool(r["in_toolchain"])
    return {"entry": entry, "package": pid, "name": r["name"], "exact_name": r["exact_name"], "module": r["module"],
            "kind": r["kind"], "chunk": r["chunk"], "chunk_index": r["chunk_index"], "in_toolchain": tc,
            "provided_by": "toolchain" if tc else "chunk", "_note": note}


class Progress:
    def __init__(self, total, enabled):
        self.total, self.done, self.bytes, self.on, self.t0 = total, 0, 0, enabled and total > 0, time.time()
        self.tty = sys.stderr.isatty()
        self.last = -1
        self.lock = threading.Lock()

    def tick(self, nbytes):
        with self.lock:
            self.done += 1
            self.bytes += nbytes
            if not self.on:
                return
            pct = 100 * self.done // self.total
            if self.tty:
                sys.stderr.write(f"\rmreg: fetched {self.done}/{self.total} chunks, {human_bytes(self.bytes)}, {time.time()-self.t0:.0f} s")
                sys.stderr.flush()
            elif pct // 25 != self.last // 25 or self.done == self.total:
                print(f"mreg: fetched {self.done}/{self.total} chunks, {human_bytes(self.bytes)}", file=sys.stderr)
            self.last = pct

    def end(self):
        if self.on and self.tty:
            sys.stderr.write("\n")


def verify_and_store(e, body, store):
    """Check the stored bytes and the decompressed bytes of one chunk against its manifest entry, then write the store object.
    Nothing is written on a difference (hash_mismatch)."""
    cid = e["id"]
    if len(body) != e["bytes_stored"] or sha256(body) != e["sha256_stored"]:
        raise NIError("hash_mismatch", f"chunk {cid}: the stored bytes do not match the manifest "
                      f"(got {len(body)} bytes, sha256 {sha256(body)}; manifest {e['bytes_stored']} bytes, {e['sha256_stored']}); "
                      "nothing of this object was written", chunk=cid)
    try:
        raw = unzstd(body)
    except Exception as ex:
        raise NIError("hash_mismatch", f"chunk {cid}: does not decompress ({ex}); nothing of this object was written", chunk=cid)
    if len(raw) != e["bytes_raw"] or sha256(raw) != e["sha256_raw"]:
        raise NIError("hash_mismatch", f"chunk {cid}: the decompressed bytes do not match the manifest "
                      f"(sha256 {sha256(raw)}, manifest {e['sha256_raw']}); nothing of this object was written", chunk=cid)
    store_put(store.obj(e["sha256_stored"]), body)     # shared by every project and process: never a partial file under the final name


def missing_from_store(store, entries):
    """(entries the local store lacks, number reused)."""
    todo, reused = [], 0
    for e in entries:
        p = store.obj(e["sha256_stored"])
        if os.path.exists(p) and os.path.getsize(p) == e["bytes_stored"]:
            reused += 1
        else:
            todo.append(e)
    return todo, reused


def fetch_chunks(f, store, train, build, variant, entries, jobs, progress=True, pr=None):
    """Make every chunk (dicts from the manifest or the lock) present in the store, hash-matched, one request per chunk file.
    Returns (fetched, reused). `pr`: a Progress shared with the caller (the packed path's fallbacks)."""
    todo, reused = missing_from_store(store, entries)
    own = pr is None
    if own:
        pr = Progress(len(todo), progress)
    stop = []

    def one(e):
        if stop:
            return
        cid = e["id"]
        path = ni_path(train, build, variant, f"X{cid[:2]}", f"C{cid}.olean.zst")
        try:
            body = f.get(path)
        except NIError as e2:
            if _not_found(e2):
                try:
                    f.get(ni_path(train, build, "index", "manifest.tsv.gz"))
                except NIError as e3:
                    if _not_found(e3):
                        raise NIError("build_removed", f"build {build} of train {train} is not on the registry any more", build=build)
                raise NIError("missing_object", f"the registry has no object for chunk {cid} ({path})", chunk=cid)
            raise
        verify_and_store(e, body, store)
        pr.tick(len(body))

    ex = ThreadPoolExecutor(max(1, jobs))
    futs = [ex.submit(one, e) for e in todo]
    try:
        for fu in futs:
            fu.result()
    except BaseException:
        stop.append(1)
        ex.shutdown(wait=True, cancel_futures=True)
        if own:
            pr.end()
        raise
    ex.shutdown(wait=True)
    if own:
        pr.end()
    return len(todo), reused


def write_in_place(dest, data):
    """Write a store object or an installed chunk file in place (no temporary file and rename): on Windows the rename of a just-written
    file waits for the virus scanner (measured 2026-11-11: 0.4 to 4 s per file against 1 ms for a direct write, which made installing a
    10,000-chunk cone take half an hour and a download of 433 chunks take 458 s). Safe because every use re-checks the bytes: `fetch_chunks`
    reuses a store object only when its size equals the manifest's, so a file cut short by a crash is fetched again; `install_chunks`
    re-hashes the store object and compares size and sha256 of an installed file with the manifest (and rewrites it on a difference);
    `verify` and `ci` do the same. A partial file is therefore repaired by the next run and never accepted. Since T-C3 this is used ONLY for
    the installed chunk files inside one project directory; the SHARED store objects, the lock, the entry file and the index cache use
    `atomic_write` (unique temporary name, flush, os.replace) because another process may read them while they are written.)"""
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    try:
        with open(dest, "wb") as f:
            f.write(data)
    except BaseException:
        try:
            os.unlink(dest)
        except OSError:
            pass
        raise


# ---- ranged archives ("packed"): the same chunks, concatenated, fetched by byte ranges -------------------------------------
# The registry may also serve, per build and variant, a few large archive objects holding every chunk's stored frame back to back
# in a fixed order (layout `dfs.deepfirst`: a chunk comes right after its imports, so a cone is a few long runs) and two tables:
# layout.tsv.gz (chunk, archive, offset, length, sha256_stored) and archives.tsv (name, bytes, sha256). The pointer names them
# (`packed.<variant>.path`, `.packed_sha256`); `packed.json` is checked against that hash, the tables against `packed.json`.
# An import then needs one range request per run of needed chunks instead of one request per chunk. A range reply is accepted
# only as 206 with the exact Content-Range; each chunk is cut out by its offsets and checked against the MANIFEST exactly as a
# per-chunk download is (the layout table is never trusted for integrity). Anything that goes wrong with a range, or with a chunk
# inside one, falls back to that chunk's own file and is counted. The per-chunk path is also the path when `packed` is absent
# or its tables do not verify (that is reported, not silent).
PACKED_SCHEMA = "mreg-decl-packed/1"
PACKED_CONNS = 8
PACKED_MIN_CHUNKS = 200          # below this many missing chunks the tables are not downloaded (they are used when already cached)
PACKED_DEFAULT_POLICY = {"gap_floor": 16384, "max_requests": 100}
_PACKED_PATH = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*(/[A-Za-z0-9][A-Za-z0-9._-]*)*/?$")
_ARCH_NAME = re.compile(r"^A[0-9]{4}\.bin$")
_FALLBACK_LIST_MAX = 50


def packed_info(ptr, variant):
    """The pointer's `packed` entry for a variant (a dict), or None. Shape is checked at use."""
    pk = (ptr or {}).get("packed")
    return pk.get(variant) if isinstance(pk, dict) and isinstance(pk.get(variant), dict) else None


def merge_ranges(items, gap_floor, max_requests):
    """items: dicts with a (archive), off, len, sorted by (a, off), no overlaps. Returns ranges {a, start, end, items}: runs of
    adjacent needed chunks, every gap <= gap_floor merged, then the smallest remaining gaps (inside one archive) merged until
    there are at most max_requests ranges (or no gap is left to merge: a range never crosses an archive)."""
    rs = []
    for it in items:
        end = it["off"] + it["len"]
        if rs and rs[-1]["a"] == it["a"] and it["off"] - rs[-1]["end"] <= gap_floor:
            rs[-1]["end"] = end
            rs[-1]["items"].append(it)
        else:
            rs.append({"a": it["a"], "start": it["off"], "end": end, "items": [it]})
    k = len(rs) - max(1, max_requests)
    if k > 0:
        gaps = sorted((rs[i + 1]["start"] - rs[i]["end"], i) for i in range(len(rs) - 1) if rs[i]["a"] == rs[i + 1]["a"])
        merge = {i for _, i in gaps[:k]}
        out = []
        for i, r in enumerate(rs):
            if out and (i - 1) in merge:
                out[-1]["end"] = r["end"]
                out[-1]["items"].extend(r["items"])
            else:
                out.append(r)
        rs = out
    return rs


class Packed:
    """The hash-matched packed tables of one (train, build, variant): `packed.json`, archives table, layout in a sqlite file."""

    def __init__(self, d, meta, archives):
        self.d, self.meta, self.archives = d, meta, archives
        self.db = _sqlite3.connect(_pathlib.Path(os.path.join(d, "layout.sqlite")).as_uri() + "?mode=ro", uri=True, check_same_thread=False)
        pol = dict(PACKED_DEFAULT_POLICY)
        for k in pol:
            v = (meta.get("policy") or {}).get(k)
            if isinstance(v, int) and not isinstance(v, bool) and v > 0:
                pol[k] = v
        self.policy = pol
        self.base = meta["_path"]            # path under /x/decl/<train>/, ends with "/"

    def close(self):
        self.db.close()

    def archive_path(self, train, a):
        return f"/x/decl/{train}/{self.base}{self.archives[a][0]}"

    def locate(self, hexid):
        r = self.db.execute("SELECT a, off, len, sha FROM l WHERE id=?", (bytes.fromhex(hexid),)).fetchone()
        return None if r is None else (r[0], r[1], r[2], r[3].hex())

    # -- opening: cached when possible, else fetched and hash-matched ---------------------------------------------------------
    @staticmethod
    def _dir(store, train, build, variant):
        return os.path.join(store.index_dir(train, build), "packed-" + variant)

    @staticmethod
    def check_info(info, build):
        if (not isinstance(info, dict) or not isinstance(info.get("path"), str) or not _PACKED_PATH.match(info["path"])
                or not info["path"].startswith(build + "/") or not _HEX64.match(str(info.get("packed_sha256", "")))):
            raise NIError("index_unavailable", f"the pointer's `packed` entry is malformed or names another build than {build}: {info!r}")
        return info["path"].rstrip("/") + "/", info["packed_sha256"]

    @staticmethod
    def cached(store, train, build, variant, info):
        try:
            _, sha = Packed.check_info(info, build)
            m = _read_json(os.path.join(Packed._dir(store, train, build, variant), "READY.json"))
            return bool(m) and m.get("packed_sha256") == sha
        except NIError:
            return False

    @staticmethod
    def open(f, store, train, build, variant, info, manifest_sha, download=True):
        base, psha = Packed.check_info(info, build)
        d = Packed._dir(store, train, build, variant)
        ready = _read_json(os.path.join(d, "READY.json"))
        if ready and ready.get("packed_sha256") == psha:
            files = {nm: os.path.join(d, nm) for nm in ("packed.json", "layout.tsv.gz", "archives.tsv")}
            try:
                got = {nm: sha256_file(p) for nm, p in files.items()}
            except OSError:
                got = {}
            if got.get("packed.json") == psha and got.get("layout.tsv.gz") == ready.get("layout_sha256") \
                    and got.get("archives.tsv") == ready.get("archives_sha256") and os.path.exists(os.path.join(d, "layout.sqlite")):
                meta = json.load(open(files["packed.json"], encoding="utf-8"))
                meta["_path"] = base
                return Packed(d, meta, Packed._read_archives(open(files["archives.tsv"], "rb").read(), meta))
        if not download:
            raise NIError("index_unavailable", "the packed tables are not cached")
        os.makedirs(os.path.dirname(d), exist_ok=True)
        sweep_stale_parts(os.path.dirname(d))
        try:
            with FileLock(d + ".lock"):
                again = Packed._cached_open(d, psha)       # another process may have built it while this one waited
                if again is not None:
                    again[0]["_path"] = base
                    return Packed(d, again[0], again[1])
                return Packed._download_open(f, d, base, psha, train, build, variant, manifest_sha)
        except TimeoutError as ex:
            raise NIError("error", str(ex))

    @staticmethod
    def _cached_open(d, psha):
        ready = _read_json(os.path.join(d, "READY.json"))
        if ready and ready.get("packed_sha256") == psha:
            files = {nm: os.path.join(d, nm) for nm in ("packed.json", "layout.tsv.gz", "archives.tsv")}
            try:
                got = {nm: sha256_file(p) for nm, p in files.items()}
            except OSError:
                return None
            if got.get("packed.json") == psha and got.get("layout.tsv.gz") == ready.get("layout_sha256") \
                    and got.get("archives.tsv") == ready.get("archives_sha256") and os.path.exists(os.path.join(d, "layout.sqlite")):
                meta = json.load(open(files["packed.json"], encoding="utf-8"))
                return meta, Packed._read_archives(open(files["archives.tsv"], "rb").read(), meta)
        return None

    @staticmethod
    def _download_open(f, d, base, psha, train, build, variant, manifest_sha):
        def get(nm):
            try:
                return f.get(f"/x/decl/{train}/{base}{nm}")
            except NIError as e:
                if _not_found(e):
                    raise NIError("missing_object", f"the registry has no {base}{nm} although the pointer names it")
                raise
        pj = get("packed.json")
        if sha256(pj) != psha:
            raise NIError("hash_mismatch", f"packed.json of {base} has sha256 {sha256(pj)}, the pointer says {psha}; nothing was cached")
        try:
            meta = json.loads(pj)
        except ValueError:
            raise NIError("index_unavailable", "packed.json is not JSON")
        if (not isinstance(meta, dict) or meta.get("schema") != PACKED_SCHEMA or meta.get("train") != train or meta.get("build") != build
                or meta.get("variant") != variant or not _HEX64.match(str(meta.get("layout_sha256", "")))
                or not _HEX64.match(str(meta.get("archives_sha256", "")))):
            raise NIError("index_unavailable", f"packed.json is not a {PACKED_SCHEMA} document for {train} {build} {variant}")
        if meta.get("manifest_sha256") not in (None, manifest_sha):
            raise NIError("hash_mismatch", f"packed.json was made for manifest {meta.get('manifest_sha256')}, this build's is {manifest_sha}")
        ab = get("archives.tsv")
        if sha256(ab) != meta["archives_sha256"]:
            raise NIError("hash_mismatch", f"archives.tsv has sha256 {sha256(ab)}, packed.json says {meta['archives_sha256']}; nothing was cached")
        archives = Packed._read_archives(ab, meta)
        lb = get("layout.tsv.gz")
        if sha256(lb) != meta["layout_sha256"]:
            raise NIError("hash_mismatch", f"layout.tsv.gz has sha256 {sha256(lb)}, packed.json says {meta['layout_sha256']}; nothing was cached")
        os.makedirs(os.path.dirname(d), exist_ok=True)
        tmp = _tempfile.mkdtemp(prefix=f"packed.part-{os.getpid()}-", dir=os.path.dirname(d))
        try:
            for nm, b in (("packed.json", pj), ("archives.tsv", ab), ("layout.tsv.gz", lb)):
                with open(os.path.join(tmp, nm), "wb") as g:
                    g.write(b)
            Packed._build_db(tmp, archives, meta)
            with open(os.path.join(tmp, "READY.json"), "w", encoding="utf-8") as g:
                json.dump({"packed_sha256": psha, "layout_sha256": meta["layout_sha256"], "archives_sha256": meta["archives_sha256"]}, g)
            if os.path.isdir(d):
                shutil.rmtree(d)
            _replace(tmp, d)
        except BaseException:
            shutil.rmtree(tmp, ignore_errors=True)
            raise
        meta["_path"] = base
        return Packed(d, meta, archives)

    @staticmethod
    def _read_archives(b, meta):
        lines = b.decode("utf-8").split("\n")
        if lines and lines[-1] == "":
            lines.pop()
        if not lines or lines[0].split("\t") != ["name", "bytes", "sha256"]:
            raise NIError("index_unavailable", "archives.tsv has the wrong header")
        out = {}
        for i, ln in enumerate(lines[1:]):
            p = ln.split("\t")
            if len(p) != 3 or not _ARCH_NAME.match(p[0]) or not p[1].isdigit() or not _HEX64.match(p[2]) or int(p[0][1:5]) != i:
                raise NIError("index_unavailable", f"archives.tsv line {i + 2} is malformed or out of order")
            out[i] = (p[0], int(p[1]), p[2])
        if meta.get("archive_count") not in (None, len(out)):
            raise NIError("index_unavailable", f"packed.json says {meta.get('archive_count')} archives, archives.tsv lists {len(out)}")
        return out

    @staticmethod
    def _build_db(d, archives, meta):
        path = os.path.join(d, "layout.sqlite")
        db = _sqlite3.connect(path)
        db.executescript("PRAGMA journal_mode=OFF; PRAGMA synchronous=OFF; CREATE TABLE l(id BLOB PRIMARY KEY, a INTEGER, off INTEGER, "
                         "len INTEGER, sha BLOB) WITHOUT ROWID;")
        f = _gzip.open(os.path.join(d, "layout.tsv.gz"), "rb")
        try:
            hdr = f.readline().rstrip(b"\r\n").split(b"\t")
            if hdr != [b"chunk", b"archive", b"offset", b"length", b"sha256_stored"]:
                raise NIError("index_unavailable", "layout.tsv.gz has the wrong header")
            batch, n = [], 0
            for line in f:
                p = line.rstrip(b"\r\n").split(b"\t")
                if len(p) != 5:
                    raise NIError("index_unavailable", f"layout.tsv.gz row {n + 2} is malformed")
                a, off, ln = int(p[1]), int(p[2]), int(p[3])
                if a not in archives or off < 0 or ln <= 0 or off + ln > archives[a][1]:
                    raise NIError("index_unavailable", f"layout.tsv.gz row {n + 2} lies outside its archive")
                batch.append((bytes.fromhex(p[0].decode()), a, off, ln, bytes.fromhex(p[4].decode())))
                n += 1
                if len(batch) >= 50000:
                    db.executemany("INSERT INTO l VALUES (?,?,?,?,?)", batch)
                    batch = []
            if batch:
                db.executemany("INSERT INTO l VALUES (?,?,?,?,?)", batch)
        except (ValueError, IndexError, _sqlite3.IntegrityError) as e:
            raise NIError("index_unavailable", f"layout.tsv.gz is malformed: {e}")
        finally:
            f.close()
        if meta.get("chunk_count") not in (None, n):
            raise NIError("index_unavailable", f"packed.json says {meta.get('chunk_count')} chunks, layout.tsv.gz has {n}")
        db.commit()
        db.close()

    # -- planning ------------------------------------------------------------------------------------------------------------
    def plan(self, todo, max_requests=None, gap_floor=None):
        """Plan the fetch of the manifest entries `todo` (missing from the local store). Returns
        {"ranges": [...], "direct": [(entry, reason)], "bytes_planned", "bytes_used", "cap", "gap_floor"}.
        A chunk whose layout row disagrees with the manifest (length, sha256), is absent from the layout, lies outside its archive or
        overlaps the previous one is fetched as a per-chunk file instead ("direct")."""
        gf = self.policy["gap_floor"] if gap_floor is None else gap_floor
        cap = self.policy["max_requests"] if max_requests is None else max_requests
        items, direct = [], []
        for e in todo:
            r = self.locate(e["id"])
            if r is None:
                direct.append((e, "not_in_layout"))
            elif r[2] != e["bytes_stored"] or r[3] != e["sha256_stored"]:
                direct.append((e, "layout_mismatch"))
            elif r[0] not in self.archives or r[1] + r[2] > self.archives[r[0]][1]:
                direct.append((e, "outside_archive"))
            else:
                items.append({"a": r[0], "off": r[1], "len": r[2], "e": e})
        items.sort(key=lambda it: (it["a"], it["off"]))
        clean = []
        for it in items:
            if clean and clean[-1]["a"] == it["a"] and it["off"] < clean[-1]["off"] + clean[-1]["len"]:
                direct.append((it["e"], "overlap"))
            else:
                clean.append(it)
        ranges = merge_ranges(clean, gf, cap)
        used = sum(it["len"] for it in clean)
        return {"ranges": ranges, "direct": direct, "bytes_used": used, "gap_floor": gf, "cap": cap,
                "bytes_planned": sum(r["end"] - r["start"] for r in ranges)}


def _read_exact(f, body, n):
    """Exactly n bytes of a range body (in pieces of 1 MiB at most), or RangeError('short')."""
    parts, left = [], n
    while left:
        try:
            b = body.read(min(left, 1 << 20))
        except (OSError, http.client.HTTPException) as ex:
            raise RangeError("short", f"the body broke off: {type(ex).__name__}: {ex}", retry=True)
        if not b:
            raise RangeError("short", f"the body ended {left} bytes early", retry=True)
        f._count_bytes(len(b))
        parts.append(b)
        left -= len(b)
    return parts[0] if len(parts) == 1 else b"".join(parts)


def _skip(f, body, n):
    while n:
        try:
            b = body.read(min(n, 1 << 20))
        except (OSError, http.client.HTTPException) as ex:
            raise RangeError("short", f"the body broke off: {type(ex).__name__}: {ex}", retry=True)
        if not b:
            raise RangeError("short", f"the body ended {n} bytes early", retry=True)
        f._count_bytes(len(b))
        n -= len(b)


def run_range(f, store, apath, asize, rng, pr):
    """Fetch one planned range and store its chunks. Returns (stored chunk count, bytes used, failed [(entry, reason)], error or None).
    A range error (not 206, wrong Content-Range, missing archive, a body that stays short after the retries) leaves the chunks not
    stored yet in `failed`; a chunk that does not match the manifest is `failed` alone."""
    remaining = list(rng["items"])
    failed, stored, used, attempts, err = [], 0, 0, 0, None
    while remaining:
        s = remaining[0]["off"]
        e = remaining[-1]["off"] + remaining[-1]["len"]
        try:
            body = f.open_range(apath, s, e, asize)
        except RangeError as ex:
            if ex.retry and attempts < f.retries:
                attempts += 1
                time.sleep(f.backoff * attempts if getattr(ex, "retry_after", None) is None else ex.retry_after)
                continue
            err = ex
            break
        try:
            pos = s
            while remaining:
                it = remaining[0]
                if it["off"] > pos:
                    _skip(f, body, it["off"] - pos)
                    pos = it["off"]
                data = _read_exact(f, body, it["len"])
                pos += it["len"]
                remaining.pop(0)
                try:
                    verify_and_store(it["e"], data, store)
                except NIError as ne:
                    if ne.kind != "hash_mismatch":
                        raise
                    failed.append((it["e"], "hash_mismatch"))
                    continue
                stored += 1
                used += it["len"]
                pr.tick(it["len"])
        except RangeError as ex:
            f.drop_conn()
            if ex.retry and attempts < f.retries:
                attempts += 1
                time.sleep(f.backoff * attempts if getattr(ex, "retry_after", None) is None else ex.retry_after)
                continue
            err = ex
            break
        finally:
            try:
                body.close()
            except Exception:
                pass
    if err is not None:
        failed.extend((it["e"], err.kind) for it in remaining)
    return stored, used, failed, err


def packed_empty_report(info=None, error=None, reason=None):
    return {"available": info is not None, "used": False, "error": error, "reason": reason, "ranges": 0, "ranges_planned": 0,
            "bytes_fetched": 0, "bytes_used": 0, "overfetch_ratio": None, "fallback_chunks": 0, "fallback_ranges": 0,
            "non_206": 0, "fallbacks": []}


def packed_prepare(f, store, train, build, variant, info, manifest_sha, todo, a, notes):
    """Decide whether the packed path serves this fetch and plan it. Returns (Packed or None, plan or None, report). Never raises
    for a table that is missing or fails verification: that is reported (`packed.error`, a note) and the per-chunk path is used.
    Auth errors propagate."""
    rep = packed_empty_report(info)
    rep["chunks_missing"] = len(todo)
    if info is None:
        rep["reason"] = "the pointer has no packed entry for this variant"
        return None, None, rep
    if getattr(a, "no_packed", False):
        rep["reason"] = "--no-packed"
        return None, None, rep
    if not todo:
        rep["reason"] = "nothing to fetch"
        return None, None, rep
    pmin = getattr(a, "packed_min", None)
    pmin = PACKED_MIN_CHUNKS if pmin is None else pmin
    if len(todo) < pmin and not Packed.cached(store, train, build, variant, info):
        rep["reason"] = f"only {len(todo)} chunks missing (below {pmin}) and the packed tables are not cached: per-chunk requests"
        return None, None, rep
    try:
        pk = Packed.open(f, store, train, build, variant, info, manifest_sha)
    except NIError as e:
        if e.kind == "auth":
            raise
        rep["error"] = f"{e.kind}: {e.message}"
        notes.append(f"packed archives NOT used ({e.message}); fell back to one request per chunk")
        return None, None, rep
    cap = getattr(a, "range_requests", None)
    mx = getattr(a, "max_requests", None)
    caps = [c for c in (cap if cap else pk.policy["max_requests"], mx) if c]
    plan = pk.plan(todo, max_requests=min(caps))
    rep.update({"layout": pk.meta.get("layout"), "packed_sha256": info["packed_sha256"], "policy": dict(pk.policy),
                "ranges_planned": len(plan["ranges"]), "bytes_planned": plan["bytes_planned"],
                "direct_planned": len(plan["direct"])})
    return pk, plan, rep


def planned_requests(plan, todo):
    return len(todo) if plan is None else len(plan["ranges"]) + len(plan["direct"])


def fetch_packed(f, store, train, build, variant, todo, pk, plan, rep, jobs, progress=True):
    """Execute a plan: ranges on PACKED_CONNS keep-alive connections, then the per-chunk fallbacks. Fills `rep`. Returns the number
    of chunks fetched."""
    pr = Progress(len(todo), progress)
    b0 = f.bytes
    lock = threading.Lock()
    fallback = list(plan["direct"])
    fb_ranges = []
    non206 = {}
    state = {"stored": 0, "used": 0, "ok_ranges": 0}

    def one(rng):
        a = rng["a"]
        name, size, _ = pk.archives[a]
        stored, used, failed, err = run_range(f, store, pk.archive_path(train, a), size, rng, pr)
        with lock:
            state["stored"] += stored
            state["used"] += used
            if err is None and not failed:
                state["ok_ranges"] += 1
            if err is not None:
                non206[err.kind] = non206.get(err.kind, 0) + 1
                fb_ranges.append({"archive": name, "start": rng["start"], "end": rng["end"], "chunks": len(failed),
                                  "reason": err.kind, "detail": err.message[:200]})
            for e, why in failed:
                fallback.append((e, why))

    ex = ThreadPoolExecutor(max(1, min(PACKED_CONNS, len(plan["ranges"]) or 1)))
    futs = [ex.submit(one, r) for r in plan["ranges"]]
    try:
        for fu in futs:
            fu.result()
    except BaseException:
        ex.shutdown(wait=True, cancel_futures=True)
        pr.end()
        raise
    ex.shutdown(wait=True)
    range_wire = f.bytes - b0
    if fallback:
        fetch_chunks(f, store, train, build, variant, [e for e, _ in fallback], jobs, False, pr=pr)
    pr.end()
    why_counts = {}
    for _, why in fallback:
        why_counts[why] = why_counts.get(why, 0) + 1
    rep.update({"used": True, "ranges": len(plan["ranges"]), "ranges_ok": state["ok_ranges"], "bytes_fetched": range_wire,
                "bytes_used": state["used"], "bytes_planned": plan["bytes_planned"],
                "overfetch_ratio": round(range_wire / state["used"], 4) if state["used"] else None,
                "fallback_chunks": len(fallback), "fallback_ranges": len(fb_ranges), "fallback_reasons": why_counts,
                "non_206": sum(non206.values()), "non_206_kinds": non206,
                "fallbacks": fb_ranges[:_FALLBACK_LIST_MAX] + [{"chunk": e["id"], "reason": why} for e, why in fallback
                                                              if why in ("not_in_layout", "layout_mismatch", "outside_archive", "overlap",
                                                                         "hash_mismatch")][:_FALLBACK_LIST_MAX]})
    return len(todo)


def install_chunks(store, chunk_dir, entries, jobs=8):
    """Write each chunk at chunk_dir/Mreg/X../C<id>.olean from the store, re-checking the raw hash (a hash check, not a check of proofs). Returns (written, present).
    The per-chunk work (read, hash, decompress, write) runs on `jobs` threads: on a busy disk it is latency bound, not CPU bound."""
    def one(e):
        dest = os.path.join(chunk_dir, *chunk_rel(e["id"]).split("/"))
        if os.path.exists(dest) and os.path.getsize(dest) == e["bytes_raw"] and sha256_file(dest) == e["sha256_raw"]:
            return 0
        try:
            body = read_file_retry(store.obj(e["sha256_stored"]))
            if sha256(body) != e["sha256_stored"]:
                raise ValueError("stored object changed")
            raw = unzstd(body)
        except Exception as ex:
            raise NIError("hash_mismatch", f"chunk {e['id']}: the local store object is damaged ({ex})", chunk=e["id"])
        if sha256(raw) != e["sha256_raw"] or len(raw) != e["bytes_raw"]:
            raise NIError("hash_mismatch", f"chunk {e['id']}: the local store object does not match the manifest", chunk=e["id"])
        write_in_place(dest, raw)
        return 1
    if len(entries) < 64 or jobs <= 1:
        written = sum(one(e) for e in entries)
    else:
        with ThreadPoolExecutor(jobs) as ex:
            written = sum(ex.map(one, entries))
    return written, len(entries) - written


def installed_chunk_files(chunk_dir):
    out = {}
    root = os.path.join(chunk_dir, "Mreg")
    if os.path.isdir(root):
        for xd in os.listdir(root):
            for fn in os.listdir(os.path.join(root, xd)):
                m = re.match(r"^C([0-9a-f]{32})\.olean$", fn)
                if m:
                    out[m.group(1)] = os.path.join(root, xd, fn)
    return out


def verified_project_path(project, path):
    """A dedicated local path inside the project, without symlink or junction traversal."""
    base = _pathlib.Path(project).absolute()
    dest = _pathlib.Path(os.path.abspath(path))
    if dest == base or not dest.is_relative_to(base):
        raise NIError("forbidden_mix", f"verified artifact path is outside the project: {path}")
    here = base
    for part in dest.relative_to(base).parts:
        if any(ord(c) < 32 for c in part):
            raise NIError("forbidden_mix", "a verified artifact path contains a control character")
        here = here / part
        if here.is_symlink() or getattr(os.path, "isjunction", lambda p: False)(here):
            raise NIError("forbidden_mix", f"verified artifact path traverses a link: {here}")
    return dest


def inspect_verified_tree(project, chunk_dir, entries):
    dest = verified_project_path(project, chunk_dir)
    if not dest.exists():
        return
    allowed = {chunk_rel(e["id"]) for e in entries}
    allowed.update({MARKER, "THIRD_PARTY_LICENSES.txt"})
    folders = {"Mreg"} | {p.rpartition("/")[0] for p in allowed}
    def unreadable(error):
        raise NIError("forbidden_mix", f"cannot inspect verified Lean search path: {error}")
    if not dest.is_dir():
        raise NIError("forbidden_mix", f"verified Lean search path is not a directory: {dest}")
    for base, dirs, files in os.walk(dest, onerror=unreadable):
        for name in dirs + files:
            p = _pathlib.Path(base, name)
            rel = p.relative_to(dest).as_posix()
            valid = rel in folders if name in dirs else rel in allowed and p.is_file() and p.stat().st_nlink == 1
            if not valid or p.is_symlink() or getattr(os.path, "isjunction", lambda path: False)(p):
                raise NIError("forbidden_mix", f"unexpected file, directory or link in the verified Lean search path: {p}")


def verified_entry(project, chunk_dir, rel):
    path = verified_project_path(project, os.path.join(project, rel))
    if (path.suffix != ".lean" or path.is_relative_to(_pathlib.Path(chunk_dir))
            or any(part.startswith(".") for part in path.relative_to(_pathlib.Path(project)).parts)):
        raise NIError("forbidden_mix", "verified entry must be a project Lean source outside the chunk directory")
    return path


def verified_entry_bytes(decls):
    modules = dict.fromkeys(chunk_module(r["chunk"]) for r in decls if r["chunk"] is not None)
    return ("-- Generated by mreg from the signed declaration selection.\n" +
            "".join(f"import {module}\n" for module in modules)).encode("utf-8")


def generated_entry_bytes(declarations, signed, train, build, variant, rel_dir):
    if signed:
        return verified_entry_bytes(declarations)
    lines = [f"-- generated by mreg ({CHUNK_LOCK}): train {train}, build {build}, {variant} chunks. Do not edit.",
             f"-- LEAN_PATH must contain {rel_dir} (`mreg env`).",
             "-- " + SUPPORTS]
    seen = set()
    for r in declarations:
        if r["chunk"] is None:
            lines.append(f"-- {r['entry']}: provided by the toolchain ({r['module']}), nothing to import")
        elif r["chunk"] not in seen:
            seen.add(r["chunk"])
            lines.append(f"import {chunk_module(r['chunk'])}  -- {r['entry']}")
    return ("\n".join(lines) + "\n").encode()


def update_generated_entry(path, desired, previous, *, write):
    """Update only a known generated file. Publish a new file without replacing a concurrent create."""
    if path.is_symlink() or (path.exists() and not path.is_file()):
        raise NIError("forbidden_mix", f"generated entry is not a regular file: {path}")
    try:
        current = path.read_bytes()
    except FileNotFoundError:
        if not write:
            return
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = _tmp_name(str(path))
        try:
            with open(tmp, "xb") as stream:
                stream.write(desired)
            try:
                if os.name == "nt":
                    os.rename(tmp, path)
                else:
                    os.link(tmp, path)
                return
            except FileExistsError:
                current = path.read_bytes()
        finally:
            _pathlib.Path(tmp).unlink(missing_ok=True)
    if current == desired:
        return
    if previous is None or current != previous:
        raise NIError("forbidden_mix", f"{path} contains existing or edited source. Choose a different --entry or use --no-entry.")
    if write:
        atomic_write(str(path), desired)


def ni_out(a, payload, human):
    payload.setdefault("supports", SUPPORTS)
    if getattr(a, "json", False):
        print(json.dumps(payload, indent=1))
    else:
        for l in human:
            print(l)
        print("supports: " + SUPPORTS)


def ni_error_out(a, cmd, e):
    if getattr(a, "json", False):
        d = {"schema": NI_SCHEMA, "ok": False, "command": cmd, "error": {"kind": e.kind, "exit_code": e.code, "message": e.message},
             "supports": SUPPORTS}
        d["error"].update(e.extra)
        print(json.dumps(d, indent=1))
    else:
        print(f"mreg: {e.kind}: {e.message}", file=sys.stderr)
    return e.code


def _req_fields(recs):
    return [{k: r[k] for k in ("entry", "package", "name", "exact_name", "module", "kind", "chunk", "in_toolchain", "provided_by")}
            for r in recs]


def norm_toolchain(t):
    t = (t or "").strip()
    return t if ":" in t or not t else "leanprover/lean4:" + t


def toolchain_state(d, train_toolchain):
    """{"project": the project's lean-toolchain or None, "train": the train's, "match": bool}. A project with no lean-toolchain
    file does not match (nothing says which Lean it uses)."""
    pth = os.path.join(d, "lean-toolchain")
    try:
        proj = open(pth, encoding="utf-8").read().strip() or None
    except OSError:
        proj = None
    return {"project": proj, "train": train_toolchain, "match": bool(proj) and norm_toolchain(proj) == norm_toolchain(train_toolchain)}


def toolchain_refusal(tc, where):
    if tc["project"] is None:
        return NIError("toolchain_mismatch", f"{where}: the project has no lean-toolchain file; chunks are compiled for {tc['train']} "
                       "and load only with that Lean. Nothing was fetched or installed", toolchain=tc)
    return NIError("toolchain_mismatch", f"{where}: the project's lean-toolchain is {tc['project']}, the chunks are compiled for "
                   f"{tc['train']}; a different Lean cannot load them. Nothing was fetched or installed", toolchain=tc)


def budget_check(a, missing, cone_chunks, bytes_stored, bytes_raw, dry):
    """requests_needed = the PLANNED request count: one per chunk object the local store lacks, or, when the packed archives serve the
    fetch, one per planned range plus one per chunk that must come as its own file (the index and pointer requests are made already).
    Over budget and not dry: refuse unless --allow-over-budget. Returns the budget record for the output."""
    mx = getattr(a, "max_requests", None)
    mx = DEFAULT_MAX_REQUESTS if mx is None else mx
    over = missing > mx
    b = {"max_requests": mx, "requests_needed": missing, "over_budget": over, "allowed": bool(getattr(a, "allow_over_budget", False))}
    if over and not dry and not b["allowed"]:
        raise NIError("over_budget", f"this needs {missing} requests ({cone_chunks} chunks in the cone, {human_bytes(bytes_stored)} "
                      f"stored), more than --max-requests {mx}; nothing was fetched. Pass --allow-over-budget to proceed, or name "
                      "a smaller declaration", cone_chunks=cone_chunks, bytes_stored=bytes_stored, bytes_raw=bytes_raw,
                      requests_needed=missing, max_requests=mx)
    return b


def chunk_refusal(what):
    return NIError("unverified_refused", f"{CHUNK_UNVERIFIED}; {what} refused before fetching declaration payloads. Use --module-level to install "
                   "the declaration's module from a checked build, or pass --allow-unverified to install the chunks anyway "
                   "(they stay marked UNVERIFIED)", experimental_chunks=True, proof_checked_under_policy=False)


def chunk_admission():
    """Admission record for an explicitly permitted legacy store without a receipt."""
    return {"policy": ADMISSION_POLICY, "proof_checked_under_policy": False, "experimental_chunks": True, "allowed_unverified": True,
            "problems": [CHUNK_UNVERIFIED]}


def compact_pin(pointer, lock, build, variant):
    values = []
    field = "compact_index_sha256"
    if pointer and pointer["build"] == build and field in pointer:
        pins = pointer[field]
        if not isinstance(pins, dict) or not pins or any(
                key not in pointer["variants"] or not isinstance(value, str) or not _HEX64.fullmatch(value)
                for key, value in pins.items()):
            raise NIError("hash_mismatch", "malformed compact index pins in the declaration pointer")
        if variant in pins:
            values.append(pins[variant])
    if lock and lock["build"] == build and field in lock:
        values.append(lock[field])
    if any(not isinstance(value, str) or not _HEX64.fullmatch(value) for value in values) or len(set(values)) > 1:
        raise NIError("hash_mismatch", "invalid or conflicting compact index digest for immutable declaration build")
    return values[0] if values else None


def receipt_pin(pointer, lock, build, variant):
    old = lock.get("receipt_sha256") if lock and lock["build"] == build else None
    pins = pointer.get("receipt_sha256", {}) if pointer and pointer["build"] == build else {}
    if not isinstance(pins, dict):
        raise NIError("hash_mismatch", "invalid receipt digests on declaration pointer")
    advertised = pins.get(variant)
    for value in (advertised, old):
        if value is not None and (not isinstance(value, str) or not _HEX64.fullmatch(value)):
            raise NIError("hash_mismatch", "invalid declaration receipt SHA-256")
    if old and advertised and old != advertised:
        raise NIError("hash_mismatch", "the receipt digest changed for an immutable declaration build")
    if compact_pin(pointer, lock, build, variant) and not (old or advertised):
        raise NIError("unverified_refused", "a compact index requires a signed declaration receipt")
    return old or advertised


def check_embedded_sources(reg, base, man, src, train, reserved_modules=None):
    """Bind a v2 receipt's embedded module selection to its authenticated parent build."""
    from types import SimpleNamespace
    def refuse(reason):
        raise NIError("unverified_refused", f"{src['id']}: {reason}")
    selected = src.get("embedded_dependencies", [])
    fields = {"lake_name", "build_key", "manifest_sha256", "index_sha256", "verify_sha256", "modules"}
    if not isinstance(selected, list) or ("embedded_dependencies" in src and not selected):
        refuse("invalid embedded dependency selection")
    if not man.get("path_dependencies") and not selected:
        return []
    if not re.fullmatch(r"[0-9a-f]{40}", str(man.get("commit", ""))) or not man.get("platform"):
        refuse("parent has no build platform or commit")
    build = SimpleNamespace(id=src["id"], version=src["version"], base=base, man=man)
    try:
        entries = {e["name"]: e for e in path_dep_entries(man, src["id"])}
        raw = reg.get(base + "shards/index.jsonl")
        if sha256(raw) != src["index_sha256"]:
            refuse("parent module index hash mismatch")
        own = set()
        for line in raw.splitlines():
            if line.strip():
                row = json.loads(line)
                mod = row.get("module")
                if isinstance(mod, str) and row["path"] == ".lake/build/lib/lean/" + mod.replace(".", "/") + ".olean":
                    own.add(mod)
        if not set(src["modules"]).issubset(own):
            refuse("claimed parent module is absent from its signed module index")
        seen_names = set()
        reserved = set() if reserved_modules is None else reserved_modules
        parent_closure = dict(man["closure"])
        if len(parent_closure) != len(man["closure"]):
            refuse("duplicate dependency in signed parent closure")
        nested_edges = {}
        for pin in selected:
            if not isinstance(pin, dict) or set(pin) != fields or not isinstance(pin["lake_name"], str):
                refuse("malformed embedded dependency")
            name, mods = pin["lake_name"], pin["modules"]
            e = entries.get(name)
            if (not e or name in seen_names or not isinstance(mods, list)
                    or not all(isinstance(m, str) and m and not any(c in m for c in "/\\\x00") for m in mods)
                    or mods != sorted(set(mods)) or own.intersection(mods)
                    or any(pin[k] != e.get(k) for k in ("build_key","manifest_sha256","index_sha256","verify_sha256"))
                    or not _HEX64.fullmatch(str(pin["verify_sha256"]))):
                refuse("embedded dependency differs from its signed parent")
            seen_names.add(name)
            dep = PathDep.for_checking(reg, build, e)
            all_nested = set(dep.mods)
            if (not all_nested or dep.man.get("package") != name or not man.get("source_repo")
                    or dep.man.get("source_repo") != man["source_repo"] or not set(mods).issubset(all_nested)):
                refuse("embedded module is absent from its authenticated compiled index")
            if own.intersection(all_nested) or reserved.intersection(all_nested):
                refuse("embedded modules overlap another signed source")
            reserved.update(all_nested)
            for row in dep.index.values():
                if row["path"].endswith(".olean"):
                    mod = row["module"]
                    if (mod not in all_nested or not all(mod.split(".")) or mod.split(".")[0] in {"Lean","Init","Std","Lake","Mreg"}
                            or any(c.isspace() or ord(c)<32 or c in "/\\" for c in mod)
                            or row["path"] != ".lake/build/lib/lean/" + mod.replace(".","/") + ".olean"):
                        refuse("invalid embedded compiled module path")
            closure = dict(dep.man["closure"])
            if (len(closure) != len(dep.man["closure"]) or closure.get(name) != "" or parent_closure.get(name) != ""
                    or any(parent_closure.get(k) != v or k == man.get("package")
                           or (k not in entries and not re.fullmatch(r"[a-f0-9]{40}",v)) for k,v in closure.items())):
                refuse("embedded dependency closure differs from its signed parent")
            nested_edges[name] = set(closure).intersection(entries) - {name}
            raw = reg.get(dep.base + "reports/verify.json")
            if sha256(raw) != pin["verify_sha256"]:
                refuse("embedded verification report hash mismatch")
            report = json.loads(raw)
            gates = {f"G{i}": "pass" for i in range(1,11)}
            identity = {"schema":"mreg-verify/1","package":name,"id":src["id"],"version":src["version"],
                        "build_key":pin["build_key"],"index_sha256":pin["index_sha256"],"modules":len(all_nested),
                        **{k:man[k] for k in ("commit","toolchain","platform")}}
            views = report["views"]
            if (any(report.get(k) != v for k,v in identity.items()) or e.get("gates") != gates
                    or any(report["gates"].get(k, {}).get("status") != v for k,v in gates.items())
                    or views.get("schema") != "mreg-views/1" or views.get("status") != "pass"
                    or views.get("problems") != 0 or views.get("lean") != train.removeprefix("lean-")
                    or views.get("modules_checked") != len(all_nested) or views.get("modules") != len(all_nested)
                    or views.get("index_sha256") != pin["index_sha256"]
                    or not all(_HEX64.fullmatch(str(views.get(k,""))) for k in ("sha256","checker_sha256","files_sha256"))):
                refuse("embedded gates, views or source identity differ from the signed build")
            views_raw = reg.get(dep.base + "reports/views.json")
            if sha256(views_raw) != views["sha256"] or report["reports"].get("reports/views.json") != views["sha256"]:
                refuse("embedded views report hash mismatch")
            census = json.loads(views_raw)
            if (any(census.get(k) != views[k] for k in ("schema","status","index_sha256","checker_sha256","files_sha256",
                                                         "lean","modules","modules_checked"))
                    or census.get("binding_problems") != [] or census.get("reasons") != []
                    or census["totals"].get("problem_count") != 0
                    or sorted(r["module"] for r in census["rows"]) != sorted(all_nested)):
                refuse("embedded views census differs from signed module index")
        if seen_names != set(entries):
            refuse("receipt omits a dependency bound by the signed parent manifest")
        resolved = set()
        while len(resolved) < len(nested_edges):
            ready = {n for n,deps in nested_edges.items() if n not in resolved and deps <= resolved}
            if not ready:
                refuse("cyclic embedded dependencies")
            resolved.update(ready)
    except (KeyError, AttributeError, TypeError, ValueError, UnicodeError, SystemExit) as ex:
        refuse("invalid signed embedded dependency metadata: " + str(ex))
    return selected


def admit_chunk_receipt(f, a, train, build, variant, toolchain, want, pin, receipt_report_pins=False):
    """Authenticate the derived product and recheck the admission of its exact source builds."""
    path = ni_path(train, build, variant, "chunk-receipt.json")
    raw = f.get(path)
    if sha256(raw) != pin:
        raise NIError("hash_mismatch", "declaration receipt differs from its SHA-256")
    reg = Registry()
    reg.accept_new_key = bool(getattr(a, "accept_new_key", False))
    sg, problems = check_signature(reg, "mreg/declaration-slices", train, build + "-" + variant, pin, f.get(path + ".sig"))
    if problems or sg["labels"] != ["verified-declarations"]:
        raise NIError("unverified_refused", "invalid declaration receipt signature: " + "; ".join(problems or ["wrong labels"]))
    receipt = json.loads(raw)
    schema = receipt.get("schema")
    if schema not in ("mreg-chunk-receipt/1", "mreg-chunk-receipt/2"):
        raise NIError("unverified_refused", "unknown declaration receipt schema")
    expected = {"train": train, "build": build, "variant": variant,
                "capability": "kernel-declarations", "toolchain": toolchain, "index_sha256": want,
                "manifest_sha256": want["manifest.tsv.gz"], "gates": {f"C{i}": "pass" for i in range(7)}}
    if variant != "checking" or any(receipt.get(k) != v for k, v in expected.items()):
        raise NIError("unverified_refused", "declaration receipt does not cover the selected indexes, policy, variant and toolchain")
    counts, kernels, exclusions = (receipt.get(k, {}) for k in ("counts", "kernels", "exclusions"))
    tool_hashes = receipt.get("tools_sha256", {})
    if (not all(isinstance(obj, dict) for obj in (counts, kernels, exclusions, tool_hashes))
            or counts.get("problems") != 0 or counts.get("uncovered") != 0
            or not isinstance(counts.get("constants"), int) or counts["constants"] < 1
            or not isinstance(counts.get("chunks"), int) or counts["chunks"] < 1
            or counts.get("chunks_read") != counts["chunks"] or kernels.get("status") != "pass"
            or kernels.get("modules") != counts["chunks"] or kernels.get("declarations") != counts["constants"]
            or not isinstance(kernels.get("second_kernel_checked"), int) or kernels["second_kernel_checked"] < counts["constants"]
            or not isinstance(exclusions.get("count"), int) or exclusions["count"] < 0 or exclusions["count"] != counts.get("excluded")
            or not re.fullmatch(r"[0-9a-f]{40}", str(receipt.get("toolchain_commit", "")))
            or not tool_hashes or not all(_HEX64.fullmatch(str(h)) for h in
                [receipt.get("files_sha256"), exclusions.get("sha256"), *tool_hashes.values()])):
        raise NIError("unverified_refused", "declaration receipt has incomplete verification coverage")
    sources = receipt.get("sources")
    dependencies = receipt.get("dependency_sources", [])
    if not isinstance(sources, list) or not sources or not isinstance(dependencies, list):
        raise NIError("unverified_refused", "declaration receipt has no source builds")
    embedded = any(isinstance(s, dict) and "embedded_dependencies" in s for s in sources + dependencies)
    if embedded != (schema == "mreg-chunk-receipt/2"):
        raise NIError("unverified_refused", "embedded dependencies require declaration receipt version 2")
    docs, packages, pins, dependency_pins, lake_names, contributing_modules = {}, {}, [], [], set(), set()
    source_ids, all_modules = set(), set()
    notices = bytearray()
    for position, src in enumerate(sources + dependencies):
        dependency = position >= len(sources)
        if not isinstance(src, dict):
            raise NIError("unverified_refused", "malformed source build in declaration receipt")
        pid, version, key = (src.get(k, "") for k in ("id", "version", "build_key"))
        lake_name, modules = src.get("lake_name"), src.get("modules")
        if (not isinstance(pid, str) or len(pid.split("/")) < 2
                or not all(isinstance(s, str) and _NAME_OK.fullmatch(s) for s in [*pid.split("/"), version, key])
                or not all(_HEX64.fullmatch(str(src.get(k, ""))) for k in ("manifest_sha256", "index_sha256"))
                or not isinstance(lake_name, str) or not lake_name or lake_name in lake_names or pid in source_ids
                or src.get("dependency_only", False) is not dependency
                or not isinstance(modules, list) or (not modules and not src.get("embedded_dependencies"))
                or not all(isinstance(m, str) and m for m in modules)
                or len(set(modules)) != len(modules) or all_modules.intersection(modules)):
            raise NIError("unverified_refused", "declaration receipt has invalid or conflicting source ownership")
        required = [g.strip() for g in getattr(a, "require", "").split(",") if g.strip()]
        row = audit_build(reg, pid, version, key, src["manifest_sha256"], required, docs, strict=True,
                         receipt_report_pins=receipt_report_pins)
        views = row.get("views")
        supplemental = src.get("supplemental_views") or {}
        verified_views = (isinstance(supplemental, dict) and supplemental.get("schema") == "mreg-views/1"
                          and supplemental.get("status") == "pass" and supplemental.get("problems") == 0
                          and supplemental.get("lean") == train.removeprefix("lean-")
                          and supplemental.get("modules") == supplemental.get("modules_checked") == len(modules)
                          and supplemental.get("index_sha256") == src["index_sha256"]
                          and supplemental.get("report_sha256") == supplemental.get("sha256")
                          and all(_HEX64.fullmatch(str(supplemental.get(k, "")))
                                  for k in ("sha256", "checker_sha256", "files_sha256")))
        if not row["ok"] or not (views == "pass" or (views in (None, "not run") and verified_views)):
            raise NIError("unverified_refused", f"{pid} no longer passes signed source admission and views")
        base = f"/v1/blobs/{pid}/-/{version}/{key}/"
        manraw = reg.get(base + "manifest.json")
        man = json.loads(manraw)
        index = man.get("aux_files", {}).get("shards/index.jsonl", {})
        if (sha256(manraw) != src["manifest_sha256"] or index.get("sha256") != src["index_sha256"]
                or norm_toolchain(man.get("toolchain")) != norm_toolchain(toolchain)):
            raise NIError("hash_mismatch", f"{pid}: source index or toolchain differs from its declaration receipt")
        source_notice = bytearray(f"\n{pid} {version} ({key})\n".encode("utf-8"))
        for name, field in (("LICENSE", "license_sha256"), ("NOTICE", "notice_sha256")):
            digest = man.get(field)
            if digest is None:
                continue
            body = reg.get(base + name, missing_ok=True)
            if body is None or sha256(body) != digest:
                raise NIError("hash_mismatch", f"{pid}: {name} is absent or differs from its signed source manifest")
            source_notice.extend(name.encode("ascii") + b"\n" + body + b"\n")
        lake_names.add(lake_name)
        source_ids.add(pid)
        all_modules.update(modules)
        exact = {k: src[k] for k in ("id", "lake_name", "version", "build_key", "manifest_sha256", "index_sha256")}
        if embedded:
            nested = check_embedded_sources(reg, base, man, src, train, all_modules)
            if not modules and (views != "pass" or not any(child["modules"] for child in nested)):
                raise NIError("unverified_refused", "empty source requires native views and selected embedded modules")
            if nested:
                exact["embedded_dependencies"] = nested
            for child in nested:
                if child["lake_name"] in lake_names:
                    raise NIError("unverified_refused", "conflicting embedded package or module in declaration receipt")
                lake_names.add(child["lake_name"])
                if not dependency:
                    contributing_modules.update(child["modules"])
        if dependency:
            dependency_pins.append(exact)
        else:
            notices.extend(source_notice)
            contributing_modules.update(modules)
            packages[pid] = {"lake_name": lake_name, "owned_modules": set(modules)}
            pins.append(exact)
    if counts.get("source_modules") != len(contributing_modules):
        raise NIError("unverified_refused", "receipt source module count differs from its ownership table")
    return {"train": train, "toolchain": toolchain, "packages": packages, "notices": bytes(notices)}, {
        "policy": ADMISSION_POLICY, "proof_checked_under_policy": True, "experimental_chunks": False,
        "allowed_unverified": False, "problems": [], "capability": "kernel-declarations", "sources": pins,
        "receipt_sha256": pin, "key_id": sg["key_id"], "exclusions": exclusions, "dependency_sources": dependency_pins,
        "source_report_verification": ("gate report bytes and signed report digests" if receipt_report_pins
                                       else "all listed report bytes")}


_COMPACT_META_LIMIT = 1 << 16
_COMPACT_BUCKET_LIMIT = 16 << 20
_COMPACT_JSON_LIMIT = 64 << 20


def compact_object(raw, limit, what):
    if len(raw) > limit:
        raise NIError("hash_mismatch", f"oversized compact index {what}")
    try:
        obj = json.loads(raw)
    except (ValueError, RecursionError) as ex:
        raise NIError("hash_mismatch", f"invalid compact index {what}") from ex
    if not isinstance(obj, dict):
        raise NIError("hash_mismatch", f"malformed compact index {what}")
    return obj


def verify_compact_root(raw, sigraw, pem, root_pin, receipt_pin, key_id, train, build, variant, want):
    """Validate a projection against an independently admitted receipt and its trusted public key."""
    if sha256(raw) != root_pin:
        raise NIError("hash_mismatch", "compact index root differs from its pin")
    root = compact_object(raw, _COMPACT_META_LIMIT, "root")
    sig = compact_object(sigraw, _COMPACT_META_LIMIT, "signature")
    pid, version_key, labels = "mreg/declaration-compact-index", build + "-" + variant, ["verified-declaration-index"]
    expected = {"schema": "mreg-sig/1", "alg": "ECDSA_P256_SHA256", "id": pid, "version": train,
                "build_key": version_key, "labels": labels, "manifest_sha256": root_pin, "key_id": key_id}
    try:
        valid = (all(sig.get(k) == v for k, v in expected.items()) and isinstance(sig["promoted_at"], str)
                 and sha256(pem_to_der(pem))[:16] == key_id
                 and ec_verify(pem, sig_message(pid, train, version_key, root_pin, labels, sig["promoted_at"]),
                               base64.b64decode(sig["signature"], validate=True)))
    except (ValueError, KeyError, TypeError):
        valid = False
    if not valid:
        raise NIError("unverified_refused", "invalid compact index signature for declaration receipt signer")
    fields = {"schema": "mreg-compact-declaration-index/1", "train": train, "build": build,
              "variant": variant, "receipt_sha256": receipt_pin, "index_sha256": want}
    groups = root.get("groups")
    if (any(root.get(k) != v for k, v in fields.items()) or not isinstance(groups, dict)
            or set(groups) != {"names", "chunks"}):
        raise NIError("hash_mismatch", "compact index root differs from signed receipt or group schema")
    for table in groups.values():
        if not isinstance(table, dict) or any(not re.fullmatch("[0-9a-f]{2}", k) or not isinstance(v, str)
                                              or not _HEX64.fullmatch(v) for k, v in table.items()):
            raise NIError("hash_mismatch", "invalid compact index directory digest")
    return root


class CompactLookup:
    def __init__(self, f, store, base, groups):
        import functools
        self.f, self.base, self.groups = f, base, groups
        self.cache = _pathlib.Path(store.root) / "compact-proofs"
        self.directory = functools.lru_cache(maxsize=512)(self._directory)
        self.bucket = functools.lru_cache(maxsize=16)(self._bucket)

    def _verified_bytes(self, digest, limit, fetch):
        path = self.cache / digest[:2] / digest
        try:
            with path.open("rb") as stream:
                data = stream.read(limit + 1)
        except FileNotFoundError:
            data = fetch()
            cached = False
        else:
            cached = True
        if len(data) > limit or sha256(data) != digest:
            raise NIError("hash_mismatch", "compact proof bytes differ from their authenticated digest")
        if not cached:
            atomic_write(str(path), data)
        return data

    def _directory(self, kind, aa):
        digest = self.groups[kind][aa]
        path = self.base + "/" + kind + "/" + aa + ".json"
        data = self._verified_bytes(digest, _COMPACT_META_LIMIT, lambda: self.f.get(path, _COMPACT_META_LIMIT))
        directory = compact_object(data, _COMPACT_META_LIMIT, "directory")
        total = 0
        for key, segment in sorted(directory.items()):
            if not (re.fullmatch("[0-9a-f]{2}", key) and isinstance(segment, list) and len(segment) == 3
                    and type(segment[0]) is int and segment[0] == total and type(segment[1]) is int
                    and 0 < segment[1] <= _COMPACT_BUCKET_LIMIT and isinstance(segment[2], str)
                    and _HEX64.fullmatch(segment[2])):
                raise NIError("hash_mismatch", "malformed compact proof range directory")
            total += segment[1]
        return directory, total

    def _bucket(self, kind, aa, bb):
        directory, total = self.directory(kind, aa)
        if bb not in directory:
            return {}
        start, size, digest = directory[bb]
        def fetch():
            path = self.base + "/" + kind + "/" + aa + ".bin"
            try:
                with self.f.open_range(path, start, start + size, total) as body:
                    raw = body.read(size)
                    if len(raw) != size or body.read(1):
                        raise NIError("hash_mismatch", "incorrect compact proof range length")
                    if self.f.kind != "file":
                        self.f._count_bytes(size)
                    return raw
            except (RangeError, OSError, http.client.HTTPException) as ex:
                raise NIError("index_unavailable", f"compact proof range unavailable: {ex}") from ex
        data = self._verified_bytes(digest, size, fetch)
        try:
            with _gzip.GzipFile(fileobj=io.BytesIO(data)) as source:
                raw = source.read(_COMPACT_JSON_LIMIT + 1)
        except (OSError, EOFError, zlib.error) as ex:
            raise NIError("hash_mismatch", "invalid compressed compact index bucket") from ex
        return compact_object(raw, _COMPACT_JSON_LIMIT, "bucket")

    def _value(self, kind, route, key):
        aa = route[:2]
        if aa in self.groups[kind]:
            bucket = self.bucket(kind, aa, route[2:4])
            if key in bucket:
                if bucket[key] is None:
                    raise NIError("hash_mismatch", "invalid null compact proof record")
                return bucket[key]
        return None

    def find(self, name):
        rows = self._value("names", sha256(name.encode("utf-8")), name)
        if rows is None:
            return []
        if not isinstance(rows, list) or not rows:
            raise NIError("hash_mismatch", "malformed compact declaration rows")
        found = []
        for row in rows:
            if not (isinstance(row, list) and len(row) == 6 and all(isinstance(x, str) for x in row[:4])
                    and name in row[:2] and type(row[4]) is int and row[4] in (0, 1) and isinstance(row[5], str)
                    and (row[5] == "" if row[4] else _HEX32.fullmatch(row[5]))):
                raise NIError("hash_mismatch", "malformed compact declaration")
            found.append(dict(name=row[0], exact_name=row[1], module=row[2], kind=row[3], in_toolchain=bool(row[4]),
                              chunk=row[5] or None, chunk_index=row[5] or None))
        return found

    def suggest(self, name):
        return []

    def cone(self, roots):
        self.selected = {}
        stack = list(roots)
        while stack:
            cid = stack.pop()
            if cid in self.selected:
                continue
            row = self._value("chunks", cid, cid)
            if not (isinstance(row, list) and len(row) == 6
                    and all(isinstance(row[i], str) and _HEX64.fullmatch(row[i]) for i in (0, 2))
                    and all(type(row[i]) is int and row[i] > 0 for i in (1, 3, 4))
                    and isinstance(row[5], list) and all(isinstance(x, str) and _HEX32.fullmatch(x) for x in row[5])
                    and row[5] == sorted(set(row[5]))):
                raise NIError("hash_mismatch", f"missing or malformed compact closure record {cid}")
            self.selected[cid] = dict(id=cid, sha256_raw=row[0], bytes_raw=row[1],
                                      sha256_stored=row[2], bytes_stored=row[3], n_decls=row[4])
            stack.extend(row[5])
        return sorted(self.selected)

    def chunk_hex(self, cid):
        return cid

    def manifest(self, variant, cid):
        return self.selected[cid]


@contextlib.contextmanager
def selection_lookup(f, store, train, build, variant, want, admission, receipt, compact):
    if compact:
        base = ni_path(train, build, variant, "compact")
        key_id = admission["key_id"]
        pem, problem = key_pem(Registry(), key_id)
        if problem:
            raise NIError("unverified_refused", problem)
        root = verify_compact_root(f.get(base + "/root.json", _COMPACT_META_LIMIT),
                                   f.get(base + "/root.json.sig", _COMPACT_META_LIMIT), pem, compact,
                                   receipt, key_id, train, build, variant, want)
        lookup = CompactLookup(f, store, base, root["groups"])
        try:
            yield lookup
        finally:
            lookup.directory.cache_clear()
            lookup.bucket.cache_clear()
    else:
        idir, _, _ = ensure_index(f, store, train, build, want)
        with chunk_lookup(idir, want, bool(receipt)) as lookup:
            yield lookup


@contextlib.contextmanager
def chunk_lookup(idir, want, verified):
    # The sqlite and CSR caches are derived files. Rebuild them from authenticated
    # compressed indexes for a verification decision, including on lock restore.
    with contextlib.ExitStack() as stack:
        if verified:
            tmp = stack.enter_context(_tempfile.TemporaryDirectory())
            for filename in INDEX_FILES:
                data = read_file_retry(os.path.join(idir, filename))
                if sha256(data) != want[filename]:
                    raise NIError("hash_mismatch", f"cached {filename} differs from signed receipt")
                with open(os.path.join(tmp, filename), "wb") as out:
                    out.write(data)
            build_lookup(tmp)
            build_manifest_db(tmp)
            idir = tmp
        lookup = Lookup(idir)
        stack.callback(lookup.close)
        yield lookup


_CHUNK_APACHE_2_0_TEXT = """Apache License
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

"Derivative Works" shall mean any work, whether in Source or
Object form, that is based on (or derived from) the Work and for which the
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
Derivative Works a copy of the License; and

(b) You must cause any modified files to carry prominent notices
stating that You changed the files; and

(c) You must retain, in the Source form of any Derivative Works
that You distribute, all copyright, patent, trademark, and
attribution notices from the Source form of the Work,
excluding those notices that do not pertain to any part of the
Derivative Works; and

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


def _ensure_chunk_licenses(f, store, train, chunk_dir):
    """Write THIRD_PARTY_LICENSES.txt inside `chunk_dir`, using store cache or optional registry notice without perturbing request counters."""
    out_path = os.path.join(chunk_dir, "THIRD_PARTY_LICENSES.txt")
    cache_path = os.path.join(store.root, "licenses", f"{train}.txt")
    data = None
    if os.path.isfile(cache_path):
        try:
            with open(cache_path, "rb") as fh:
                data = fh.read() or None
        except OSError:
            data = None
    if data is None:
        if f.kind == "file":
            p = os.path.join(f.root, "x", "decl", train, "THIRD_PARTY_LICENSES.txt")
            try:
                with open(p, "rb") as fh:
                    data = fh.read() or None
            except OSError:
                data = None
        elif f.kind == "http" and f.tok:
            req = urllib.request.Request(
                f.base + f"/x/decl/{train}/THIRD_PARTY_LICENSES.txt",
                headers={"x-mreg-token": f.tok, "User-Agent": "mreg/" + VERSION, "Accept-Encoding": "identity"},
            )
            try:
                with _safe_redirect_open(req, timeout=5) as r:
                    data = r.read(1 << 20) or None
            except (urllib.error.HTTPError, urllib.error.URLError, OSError, ValueError):
                data = None
        if data is not None:
            try:
                atomic_write(cache_path, data)
            except OSError:
                pass
    if data is None:
        data = (
            "# Third-Party Licences and Notices for Declaration Chunks\n\n"
            f"Train: {train}\n\n"
            "These compiled Lean 4 declaration chunks are repackaged builds of upstream\n"
            "packages on the stated train (including leanprover/lean4 and\n"
            "leanprover-community/mathlib4 and its pinned dependencies).\n"
            "Upstream repositories, commits, and SPDX licence metadata are recorded per\n"
            "package under `/v1/index/<owner>/<repo>.json` (Apache-2.0).\n\n"
            "mathregistry is unofficial and unaffiliated with the upstream authors.\n\n"
            + _CHUNK_APACHE_2_0_TEXT
        ).encode("utf-8")
    try:
        atomic_write(out_path, data)
    except OSError:
        pass


def ni_run(cmd, a, entries, record=False):
    """resolve | add | install by declaration. Returns 0 or raises NIError.
    Order (each step before any chunk is fetched): pointer -> train document -> toolchain gate -> hash-matched index -> resolution
    (an unknown name is answered only from the hash-matched index and names it) -> cone -> request budget -> fetch."""
    t0 = time.time()
    d = os.path.abspath(a.dir)
    cfg, cc, lock = ni_load_cfg(d)
    variant = getattr(a, "variant", None) or (lock or {}).get("variant") or cc.get("variant") or "checking"
    if variant not in VARIANTS:
        raise NIError("error", f"--variant must be one of {', '.join(VARIANTS)}")
    f, store = Fetcher(), Store()
    train = getattr(a, "train", None) or (lock or {}).get("train") or cc.get("train") or cfg.get("train")
    if not train:
        ts = f.json("/v1/index/trains.json").get("trains") or []
        if not ts:
            raise NIError("not_on_train", "the registry lists no train")
        train = ts[-1]["train"]
    if not _NAME_OK.match(train):
        raise NIError("error", f"bad train name {train!r}")
    upgrade = bool(getattr(a, "upgrade_build", False))
    if lock and lock["train"] != train:
        raise NIError("forbidden_mix", f"chunks from two trains: the project holds train {lock['train']}, this asks for {train}")
    if lock and lock["variant"] != variant:
        raise NIError("forbidden_mix", f"checking and full chunks in one project: the project holds {lock['variant']}, this asks for {variant}")
    notes = []
    try:
        td = f.json(f"/v1/index/trains/{train}.json")
    except NIError as e:
        if _not_found(e):
            raise NIError("not_on_train", f"no train document for {train}")
        raise
    if not td.get("toolchain"):
        raise NIError("error", f"the train document of {train} names no toolchain; refusing to install chunks")
    asked_build = getattr(a, "build", None)
    supplied_digest = getattr(a, "source_manifest_sha256", None)
    routes = (lock or {}).get("source_routes", [])
    using_default = False
    try:
        if lock and not upgrade:
            ptr = read_pointer(f, train)
        else:
            requested = [*cc.get("declarations", []), *entries]
            ptr, routes, using_default = discover_store(f, train, td, requested, asked_build, supplied_digest)
    except NIError as e:
        if lock and not upgrade and e.kind in ("not_on_train", "network"):
            ptr = None
            notes.append(f"pointer unavailable ({e.message}); staying on locked build {lock['build']}")
        else:
            raise
    if lock and not upgrade:
        build, want = lock["build"], want_from_lock(lock)
        if routes:
            old_packages = {r["id"] for r in routes}
            added = [e for e in entries if (p := parse_decl(e)) and p[0] not in old_packages]
            if added:
                added_ptr, added_routes, _ = discover_store(f, train, td, added, build, supplied_digest)
                if receipt_pin(added_ptr, lock, build, variant) != lock.get("receipt_sha256"):
                    raise NIError("hash_mismatch", "additional package selects another signed declaration receipt")
                routes = routes + added_routes
        if asked_build and asked_build != build:
            raise NIError("forbidden_mix", f"chunks from two builds: the project holds build {build}, --build asks for {asked_build}")
        if ptr and ptr["build"] != build:
            notes.append(f"the registry's current build is {ptr['build']}; this project stays on {build} "
                         "(`mreg install --upgrade-build` moves it)")
        elif ptr and ptr["index_sha256"] != want:
            raise NIError("hash_mismatch", f"build {build} is immutable, but the pointer's index hashes differ from the ones in "
                          f"{CHUNK_LOCK}; refused", build=build)
    else:
        build, want = ptr["build"], ptr["index_sha256"]
        if asked_build and asked_build != build:
            raise NIError("not_on_train", f"--build {asked_build}: the registry's current build of {train} is {build}; "
                          "only the current build (or the locked one) can be chosen")
        if variant not in ptr["variants"]:
            raise NIError("not_on_train", f"train {train} build {build} serves {ptr['variants']}, not {variant}")
    pin = receipt_pin(ptr, lock, build, variant)
    if supplied_digest and not pin:
        raise NIError("unverified_refused", "exact source selection requires a signed declaration receipt")
    compact = compact_pin(ptr, lock, build, variant)
    dry = cmd == "resolve" or bool(getattr(a, "dry_run", False))
    if not pin and not dry and not allow_unverified(a):
        raise chunk_refusal(f"`mreg {cmd}` by declaration")
    chunk_dir = os.path.abspath(os.path.join(d, *(getattr(a, "chunk_dir", None) or (lock or {}).get("chunk_dir") or cc.get("dir") or
                                                  f".lake/mreg-chunks/{train}").split("/")))
    admission = chunk_admission()
    if pin:
        if lock and lock.get("receipt_sha256") and lock.get("registry") != f.base:
            raise NIError("forbidden_mix", "the declaration lock belongs to a different registry")
        td, admission = admit_chunk_receipt(f, a, train, build, variant, td["toolchain"], want, pin,
                                           receipt_report_pins=bool(compact))
        verify_routed_sources(routes, admission, allow_unserved=using_default)
        if supplied_digest and lock and not upgrade:
            requested = {p[0] for entry in (entries or cc.get("declarations", [])) if (p := parse_decl(entry))}
            if len(requested) != 1 or not any(s["id"] in requested and s["manifest_sha256"] == supplied_digest
                                             for s in admission["sources"]):
                raise NIError("hash_mismatch", "requested source manifest differs from the locked declaration store")
        if compact:
            notes.append("Checked source gate reports and signed supporting report digests. "
                         "Run mreg audit --strict to recheck every report body.")
    tcs = toolchain_state(d, td["toolchain"])
    if not tcs["match"]:
        if not dry:
            raise toolchain_refusal(tcs, f"train {train}")
        notes.append(f"the project's lean-toolchain ({tcs['project'] or 'none'}) is not the train's ({tcs['train']}): "
                     "add and install would be refused")
    covers = sorted(p["lake_name"] for p in (td.get("packages") or {}).values() if p.get("lake_name"))
    check_mix(d, covers, train, build, variant, lock, chunk_dir, upgrade)
    req_before = f.requests
    answered = {"train": train, "build": build, "manifest_sha256": want["manifest.tsv.gz"], "index_sha256": dict(want)}
    known = [x["entry"] for x in (lock or {}).get("declarations", [])]
    known += [e for e in (cc.get("declarations") or []) if e not in known]
    allent = list(dict.fromkeys(known + list(entries)))
    with selection_lookup(f, store, train, build, variant, want, admission, pin, compact) as lk:
        try:
            recs = [resolve_entry(lk, td, e) for e in allent]
        except NIError as e:
            if pin and (not routes or using_default) and not asked_build and e.kind in ("unknown_declaration", "not_on_train"):
                e.extra["verified_selection_unavailable"] = True
            if e.kind in ("unknown_declaration", "ambiguous_name"):
                e.extra["answered_from"] = answered
                if e.kind == "unknown_declaration":
                    e.message += (f" [answered from train {train} build {build} only, index assignment.tsv.gz sha256 "
                                  f"{want['assignment.tsv.gz']}; a name this index does not hold may exist in another build or train]")
            raise
        notes += [r["_note"] for r in recs if r.get("_note")]
        cone = lk.cone([r["chunk_index"] for r in recs if not r["in_toolchain"]])
        chunks, missing = [], []
        for i in cone:
            m = lk.manifest(variant, lk.chunk_hex(i))
            if m:
                chunks.append(m)
            else:
                missing.append(lk.chunk_hex(i))
    idx_requests = f.requests - req_before
    if missing:
        raise NIError("missing_object", f"{len(missing)} chunks of the cone are not in the {variant} manifest of build {build}, "
                      f"for example {missing[0]}", chunks=missing[:5])
    totals = {"chunks": len(chunks), "bytes_raw": sum(c["bytes_raw"] for c in chunks),
              "bytes_stored": sum(c["bytes_stored"] for c in chunks)}
    locked_entry = (lock or {}).get("entry", cc.get("entry", "MregChunks.lean"))
    ef = None if getattr(a, "no_entry", False) else (getattr(a, "entry", None) or locked_entry)
    rel_dir = os.path.relpath(chunk_dir, d).replace(os.sep, "/")
    if pin:
        prior = (lock or {}).get("chunks", []) if upgrade else []
        inspect_verified_tree(d, chunk_dir, [*chunks, *prior])
    if ef:
        entry_path = verified_entry(d, chunk_dir, ef) if pin else _pathlib.Path(d, ef)
        desired = generated_entry_bytes(recs, pin, train, build, variant, rel_dir)
        previous = None
        if lock and locked_entry and _pathlib.Path(d, locked_entry).absolute() == entry_path.absolute():
            previous = generated_entry_bytes(lock["declarations"], lock.get("receipt_sha256"), lock["train"],
                                             lock["build"], lock["variant"], lock["chunk_dir"])
        if cmd != "resolve":
            update_generated_entry(entry_path, desired, previous, write=False)
    todo_entries, _r = missing_from_store(store, chunks)
    would = len(todo_entries)
    pinfo = packed_info(ptr, variant) if (ptr and ptr["build"] == build) else None
    if pinfo is None and lock and lock.get("build") == build and isinstance(lock.get("packed"), dict):
        pinfo = lock["packed"]
    pk, pplan, prep = packed_prepare(f, store, train, build, variant, pinfo, want["manifest.tsv.gz"], todo_entries, a, notes)
    planned = planned_requests(pplan, todo_entries)
    try:
        budget = budget_check(a, planned, totals["chunks"], totals["bytes_stored"], totals["bytes_raw"], dry)
    except BaseException:
        if pk:
            pk.close()
        raise
    if budget["over_budget"] and dry:
        notes.append(f"over budget: {planned} requests needed, --max-requests is {budget['max_requests']}; "
                     "add and install refuse unless --allow-over-budget is given")
    payload = {"schema": NI_SCHEMA, "ok": True, "command": cmd, "registry": f.base, "train": train, "build": build,
               "variant": variant, "manifest_sha256": want["manifest.tsv.gz"], "index_sha256": dict(want),
               "requested": _req_fields(recs), "cone": dict(totals), "dry_run": dry, "toolchain": tcs, "budget": budget,
               "packed": prep, "notes": notes}
    head = [f"{r['entry']}: {r['kind']} in {r['module']}, " +
            ("provided by the toolchain; nothing to fetch" if r["in_toolchain"] else f"chunk {r['chunk']}") for r in recs]
    if pin:
        payload["admission"] = admission
    if dry:
        if pk:
            pk.close()
        payload.update({"fetched": 0, "reused": 0, "installed": 0, "already_installed": 0, "bytes_fetched": 0, "would_fetch": would,
                        "requests": f.requests, "requests_index": idx_requests, "requests_objects": 0,
                        "seconds": round(time.time() - t0, 3), "lock": None, "chunk_dir": chunk_dir, "entry_file": None})
        ni_out(a, payload, head + [f"cone: {len(chunks)} chunks ({human_bytes(totals['bytes_stored'])} stored, "
                                   f"{human_bytes(totals['bytes_raw'])} raw); {would} not in the local store "
                                   f"(= {planned} requests, --max-requests {budget['max_requests']}); train {train} build {build} {variant}"]
               + ([f"packed archives: {prep['ranges_planned']} ranges planned, {human_bytes(prep.get('bytes_planned') or 0)} to read"]
                  if prep.get("ranges_planned") else []) + notes)
        return 0
    req0, bytes0, tf0 = f.requests, f.bytes, time.time()
    show = not getattr(a, "json", False) and not getattr(a, "quiet", False)
    try:
        if pk:
            nf = fetch_packed(f, store, train, build, variant, todo_entries, pk, pplan, prep, getattr(a, "jobs", None) or 16, show)
            nr = len(chunks) - nf
        else:
            nf, nr = fetch_chunks(f, store, train, build, variant, chunks, getattr(a, "jobs", None) or 16, show)
    finally:
        if pk:
            pk.close()
    req_objects, bytes_fetched, seconds_fetch = f.requests - req0, f.bytes - bytes0, round(time.time() - tf0, 3)
    if prep.get("fallback_chunks"):
        notes.append(f"packed archives: {prep['fallback_chunks']} chunks and {prep['fallback_ranges']} ranges fell back to per-chunk files "
                     f"({prep.get('fallback_reasons')}); see `packed.fallbacks`")
    if upgrade and os.path.isdir(os.path.join(chunk_dir, "Mreg")):
        if _read_json(os.path.join(chunk_dir, MARKER)) is None:
            raise NIError("error", f"{chunk_dir} has no {MARKER}; refusing to clear a directory mreg did not make")
        shutil.rmtree(os.path.join(chunk_dir, "Mreg"))
    wr, pre = install_chunks(store, chunk_dir, chunks)
    if pin:
        atomic_write(os.path.join(chunk_dir, "THIRD_PARTY_LICENSES.txt"), td["notices"])
    else:
        _ensure_chunk_licenses(f, store, train, chunk_dir)
    atomic_write(os.path.join(chunk_dir, MARKER), (json.dumps({"schema": "mreg-chunk-dir/1", "train": train, "build": build,
                                                                "variant": variant}) + "\n").encode())
    published = (ptr or {}).get("published_at") if (ptr and ptr["build"] == build) else (lock or {}).get("published_at")
    lockd = {"schema": CHUNK_LOCK_SCHEMA, "registry": f.base, "train": train, "build": build, "variant": variant,
             "toolchain": td["toolchain"], "manifest_sha256": want["manifest.tsv.gz"], "published_at": published,
             "index": dict(want), "chunk_dir": rel_dir, "covers_packages": covers,
             "declarations": [{k: r[k] for k in ("entry", "package", "name", "exact_name", "module", "kind", "chunk")} for r in recs],
             "admission": dict(admission, downloaded=True, hash_matched=True, compatible="not checked"),
             "counts": {"declarations": len(recs), "chunks": len(chunks)},
             "bytes": {"raw": totals["bytes_raw"], "stored": totals["bytes_stored"]},
             "chunks": [{k: c[k] for k in ("id", "sha256_raw", "bytes_raw", "sha256_stored", "bytes_stored")} for c in chunks]}
    lockd["entry"] = ef
    if pin:
        lockd["receipt_sha256"] = pin
    if compact:
        lockd["compact_index_sha256"] = compact
    if routes:
        lockd["source_routes"] = routes
    if pinfo:
        lockd["packed"] = {"path": pinfo["path"], "packed_sha256": pinfo["packed_sha256"]}
    lock_path = os.path.join(d, CHUNK_LOCK)
    if ef:
        update_generated_entry(entry_path, desired, previous, write=True)
    atomic_write(lock_path, (json.dumps(lockd, indent=1) + "\n").encode())
    if record:
        cfg = dict(cfg)
        cfg.setdefault("registry", f.base)
        cfg.setdefault("train", train)
        cc.update({"train": train, "build": build, "variant": variant, "dir": rel_dir, "declarations": allent})
        cc["entry"] = ef
        cfg["chunks"] = cc
        atomic_write(os.path.join(d, "mreg.json"), (json.dumps(cfg, indent=1) + "\n").encode())
    payload.update({"fetched": nf, "reused": nr, "installed": wr, "already_installed": pre, "bytes_fetched": bytes_fetched,
                    "requests": f.requests, "requests_index": idx_requests, "requests_objects": req_objects,
                    "seconds_fetch": seconds_fetch, "seconds": round(time.time() - t0, 3), "lock": lock_path, "chunk_dir": chunk_dir,
                    "entry_file": os.path.join(d, ef) if ef else None, "lean_path": chunk_dir})
    payload["admission"] = lockd["admission"]
    if not pin:
        notice(a, f"UNVERIFIED: declaration chunks of train {train} build {build} are installed without passing the registry's proof policy: "
                  f"{CHUNK_UNVERIFIED}", err=False)
    ni_out(a, payload, head + [
        f"cone {len(chunks)} chunks ({human_bytes(totals['bytes_stored'])} stored); fetched {nf}, reused {nr} from the local store; "
        f"{wr} written, {pre} already installed; {f.requests} requests, {human_bytes(bytes_fetched)}, {payload['seconds']} s",
        *([f"packed archives: {prep['ranges']} ranges, {human_bytes(prep['bytes_fetched'])} read for {human_bytes(prep['bytes_used'])} used "
           f"(overfetch {prep['overfetch_ratio']}), {prep['fallback_chunks']} chunks by fallback"] if prep.get("used") else []),
        f"train {train} build {build} {variant}; wrote {CHUNK_LOCK}" + (f" and {ef}" if ef else ""),
        f"LEAN_PATH must include {chunk_dir}"] + notes)
    return 0


def validate_chunk_lock(f, store, a, lock, pin, full_reports=False):
    train, build, variant = lock["train"], lock["build"], lock["variant"]
    if not (_NAME_OK.fullmatch(train) and _NAME_OK.fullmatch(build) and variant == "checking"):
        raise NIError("error", "invalid verified declaration lock selection")
    ents = lock["chunks"]
    if f.base != lock.get("registry"):
        raise NIError("forbidden_mix", "the declaration lock belongs to a different registry")
    want = want_from_lock(lock)
    compact = compact_pin(None, lock, build, variant)
    source_train, admission = admit_chunk_receipt(f, a, train, build, variant, lock.get("toolchain"), want, pin,
                                                 receipt_report_pins=bool(compact) and not full_reports)
    verify_routed_sources(lock.get("source_routes", []), admission)
    covers = sorted(p["lake_name"] for p in source_train["packages"].values())
    if covers != lock.get("covers_packages"):
        raise NIError("hash_mismatch", "locked package ownership differs from the signed receipt")
    with selection_lookup(f, store, train, build, variant, want, admission, pin, compact) as lk:
        requested = [resolve_entry(lk, source_train, r["entry"]) for r in lock["declarations"]]
        declarations = [{k: r[k] for k in ("entry", "package", "name", "exact_name", "module", "kind", "chunk")}
                        for r in requested]
        if declarations != lock["declarations"]:
            raise NIError("hash_mismatch", "locked declarations differ from the signed assignment")
        cone = lk.cone([r["chunk_index"] for r in requested if not r["in_toolchain"]])
        selected = []
        for i in cone:
            m = lk.manifest(variant, lk.chunk_hex(i))
            if m is None:
                raise NIError("hash_mismatch", "a required chunk is missing from the signed manifest")
            selected.append({k: m[k] for k in ("id", "sha256_raw", "bytes_raw", "sha256_stored", "bytes_stored")})
        if ents != selected:
            raise NIError("hash_mismatch", "locked chunks differ from the complete signed dependency closure")
    if lock.get("admission", {}).get("sources") != admission["sources"]:
        raise NIError("hash_mismatch", "locked source pins differ from the signed receipt")
    old = lock.get("admission", {})
    embedded_dependency = any("embedded_dependencies" in s for s in admission["dependency_sources"])
    if ("dependency_sources" in old or embedded_dependency) and old.get("dependency_sources") != admission["dependency_sources"]:
        raise NIError("hash_mismatch", "locked dependency source pins differ from the signed receipt")
    project = os.path.abspath(a.dir)
    chunk_dir = verified_project_path(project, os.path.join(project, lock["chunk_dir"]))
    inspect_verified_tree(project, chunk_dir, ents)
    if "entry" not in lock:
        raise NIError("hash_mismatch", "the verified lock has no generated entry selection")
    if lock["entry"] is not None:
        entry = verified_entry(project, chunk_dir, lock["entry"])
        if entry.exists() and entry.read_bytes() != verified_entry_bytes(declarations):
            raise NIError("hash_mismatch", f"{entry}: imports differ from the signed declaration selection")
    return admission, source_train["notices"]


def ni_ci(a):
    t0 = time.time()
    d = os.path.abspath(a.dir)
    lock = _read_json(os.path.join(d, CHUNK_LOCK))
    if lock is None or lock.get("schema") != CHUNK_LOCK_SCHEMA:
        raise NIError("error", f"no valid {CHUNK_LOCK} here")
    pin = receipt_pin(None, lock, lock["build"], lock["variant"])
    if not pin and not allow_unverified(a):
        raise chunk_refusal("`mreg ci` of the chunk lock")
    ents = [dict(c) for c in lock["chunks"]]
    for c in ents:
        if not (_HEX32.match(c["id"]) and _HEX64.match(c["sha256_raw"]) and _HEX64.match(c["sha256_stored"])):
            raise NIError("error", f"{CHUNK_LOCK}: malformed chunk entry {c.get('id')}")
    if [c["id"] for c in ents] != sorted(c["id"] for c in ents):
        raise NIError("error", f"{CHUNK_LOCK}: chunk ids are not sorted")
    train, build, variant = lock["train"], lock["build"], lock["variant"]
    if not (_NAME_OK.match(train) and _NAME_OK.match(build) and variant in VARIANTS):
        raise NIError("error", f"{CHUNK_LOCK}: bad train, build or variant")
    hit = sorted(n for n in lock.get("covers_packages", []) if n in module_packages(d))
    if hit:
        raise NIError("forbidden_mix", "the original module files of " + ", ".join(hit) +
                      " and the locked chunks of the same packages would both be on the search path")
    f, store = Fetcher(), Store()      # the pointer is NOT read: ci restores the locked build even if the pointer moved on
    admission, notices = validate_chunk_lock(f, store, a, lock, pin) if pin else (chunk_admission(), None)
    chunk_dir = os.path.abspath(os.path.join(d, *lock["chunk_dir"].split("/")))
    mk = _read_json(os.path.join(chunk_dir, MARKER))
    if mk and (mk.get("train"), mk.get("build"), mk.get("variant")) != (train, build, variant):
        raise NIError("forbidden_mix", f"{chunk_dir} holds {mk.get('train')} {mk.get('build')} {mk.get('variant')} chunks, the lock says "
                      f"{train} {build} {variant}")
    if lock.get("toolchain"):          # locks written by this client carry the train's toolchain
        tcs = toolchain_state(d, lock["toolchain"])
        if not tcs["match"]:
            raise toolchain_refusal(tcs, f"{CHUNK_LOCK} (train {train})")
    else:
        tcs = None
    would = sum(1 for c in ents if not (os.path.exists(store.obj(c["sha256_stored"])) and
                                        os.path.getsize(store.obj(c["sha256_stored"])) == c["bytes_stored"]))
    todo_entries, _r = missing_from_store(store, ents)
    cnotes = []
    pinfo = lock.get("packed") if isinstance(lock.get("packed"), dict) else None
    pk, pplan, prep = packed_prepare(f, store, train, build, variant, pinfo, lock["manifest_sha256"], todo_entries, a, cnotes)
    try:
        budget = budget_check(a, planned_requests(pplan, todo_entries), len(ents), lock["bytes"]["stored"], lock["bytes"]["raw"], False)
        show = not getattr(a, "json", False) and not getattr(a, "quiet", False)
        if pk:
            nf = fetch_packed(f, store, train, build, variant, todo_entries, pk, pplan, prep, getattr(a, "jobs", None) or 16, show)
            nr = len(ents) - nf
        else:
            nf, nr = fetch_chunks(f, store, train, build, variant, ents, getattr(a, "jobs", None) or 16, show)
    finally:
        if pk:
            pk.close()
    wr, pre = install_chunks(store, chunk_dir, ents)
    keep, removed = {c["id"] for c in ents}, 0
    for cid, p in installed_chunk_files(chunk_dir).items():
        if cid not in keep:
            os.unlink(p)
            removed += 1
    atomic_write(os.path.join(chunk_dir, MARKER), (json.dumps({"schema": "mreg-chunk-dir/1", "train": train, "build": build,
                                                                "variant": variant}) + "\n").encode())
    if pin:
        atomic_write(os.path.join(chunk_dir, "THIRD_PARTY_LICENSES.txt"), notices)
    else:
        _ensure_chunk_licenses(f, store, train, chunk_dir)
    if pin and lock["entry"]:
        entry = verified_entry(d, chunk_dir, lock["entry"])
        update_generated_entry(entry, verified_entry_bytes(lock["declarations"]), None, write=True)
    payload = {"schema": NI_SCHEMA, "ok": True, "command": "ci", "registry": f.base, "train": train, "build": build,
               "variant": variant, "manifest_sha256": lock["manifest_sha256"], "index_sha256": want_from_lock(lock),
               "requested": [dict(r, in_toolchain=r["chunk"] is None, provided_by="toolchain" if r["chunk"] is None else "chunk")
                             for r in lock["declarations"]],
               "cone": {"chunks": len(ents), "bytes_raw": lock["bytes"]["raw"], "bytes_stored": lock["bytes"]["stored"]},
               "dry_run": False, "toolchain": tcs, "budget": budget, "packed": prep, "notes": cnotes, "fetched": nf, "reused": nr, "installed": wr, "already_installed": pre,
               "removed_extra": removed, "bytes_fetched": f.bytes, "requests": f.requests, "requests_index": 0,
               "requests_objects": f.requests, "seconds": round(time.time() - t0, 3), "lock": os.path.join(d, CHUNK_LOCK),
               "chunk_dir": chunk_dir, "lean_path": chunk_dir}
    payload["admission"] = admission
    if not pin:
        notice(a, f"UNVERIFIED: declaration chunks of train {train} build {build} are restored without passing the registry's proof policy: "
                  f"{CHUNK_UNVERIFIED}", err=False)
    ni_out(a, payload, [f"ci: restored {len(ents)} locked chunks of train {train} build {build} {variant}: fetched {nf}, reused {nr}, "
                        f"{wr} written, {pre} already installed, {removed} extra removed; {f.requests} requests; every hash matched"])
    return 0


def installed_chunk_admission(a, lock, full_reports=False):
    d = os.path.abspath(a.dir)
    pin = receipt_pin(None, lock, lock["build"], lock["variant"])
    if not pin and (lock.get("admission") or {}).get("proof_checked_under_policy"):
        raise NIError("unverified_refused", "the lock claims verification without a pinned declaration receipt")
    admission, notices = validate_chunk_lock(Fetcher(), Store(), a, lock, pin, full_reports=full_reports) if pin else (None, None)
    if pin and lock["entry"] and not os.path.isfile(os.path.join(d, lock["entry"])):
        raise NIError("hash_mismatch", "the generated declaration entry is missing")
    chunk_dir = os.path.abspath(os.path.join(d, *lock["chunk_dir"].split("/")))
    notice_file = _pathlib.Path(chunk_dir, "THIRD_PARTY_LICENSES.txt")
    if pin and (not notice_file.is_file() or notice_file.read_bytes() != notices):
        raise NIError("hash_mismatch", "installed notices differ from the signed source documents")
    return admission


def ni_verify(a):
    d = os.path.abspath(a.dir)
    lock = _read_json(os.path.join(d, CHUNK_LOCK))
    if lock is None or lock.get("schema") != CHUNK_LOCK_SCHEMA:
        raise NIError("error", f"no valid {CHUNK_LOCK} here")
    admission = installed_chunk_admission(a, lock)
    pin = bool(admission)
    chunk_dir = os.path.abspath(os.path.join(d, *lock["chunk_dir"].split("/")))
    bad, missing = [], []
    def check(c):
        p = os.path.join(chunk_dir, *chunk_rel(c["id"]).split("/"))
        if not os.path.exists(p):
            return c["id"], "missing"
        if os.path.getsize(p) != c["bytes_raw"] or sha256_file(p) != c["sha256_raw"]:
            return c["id"], "bad"
        return c["id"], None
    with ThreadPoolExecutor(8) as ex:
        for cid, st in ex.map(check, lock["chunks"]):
            if st == "missing":
                missing.append(cid)
            elif st == "bad":
                bad.append(cid)
    extra = sorted(set(installed_chunk_files(chunk_dir)) - {c["id"] for c in lock["chunks"]})
    ok = not (bad or missing or (pin and extra))
    verify_note = ("Revalidated the signature, source builds and complete signed dependency closure."
                   if pin else
                   "this is a hash check, not a check of proofs; declaration chunks are experimental and unverified")
    if pin and lock.get("compact_index_sha256"):
        verify_note += " Checked source gate reports and signed supporting report digests."
    payload = {"schema": NI_SCHEMA, "ok": ok, "command": "verify", "train": lock["train"], "build": lock["build"],
               "variant": lock["variant"], "checked": len(lock["chunks"]), "mismatched": bad, "missing": missing,
               "extra": extra, "chunk_dir": chunk_dir,
               "note": verify_note}
    if admission:
        payload["admission"] = admission
    ni_out(a, payload, [f"hashes matched: {len(lock['chunks']) - len(bad) - len(missing)} of {len(lock['chunks'])} chunks of build {lock['build']} equal the lock's SHA-256 (not a check of proofs): {len(bad)} mismatched, {len(missing)} missing, "
                        f"{len(extra)} extra",
                        verify_note] + [f"MISMATCH {c}" for c in bad] + [f"MISSING {c}" for c in missing])
    if not ok:
        raise _Quiet("hash_mismatch", "installed chunks differ from the lock")
    return 0


def ni_env(a):
    d = os.path.abspath(a.dir)
    lock = _read_json(os.path.join(d, CHUNK_LOCK))
    cc = load_cfg(d).get("chunks") or {}
    rel = (lock or {}).get("chunk_dir") or cc.get("dir")
    if not rel:
        raise NIError("error", "no chunk directory recorded here (run `mreg add owner/pkg#Decl` first)")
    cd = os.path.abspath(os.path.join(d, *rel.split("/")))
    rel_entry = (lock or {}).get("entry", cc.get("entry"))
    entry = os.path.join(d, rel_entry) if rel_entry else None
    payload = {"schema": NI_SCHEMA, "ok": True, "command": "env", "chunk_dir": cd, "lean_path": cd, "path_separator": os.pathsep,
               "entry_file": entry}
    ni_out(a, payload, [f"LEAN_PATH={cd}{os.pathsep}$LEAN_PATH   (chunk modules are Mreg.X<2 hex>.C<id>)"] +
           ([f"entry file: {entry}"] if entry else []))
    return 0


def ni_guard(cmd, a, fn):
    try:
        return fn()
    except _Quiet as e:
        sys.exit(e.code)
    except NIError as e:
        sys.exit(ni_error_out(a, cmd, e))
    except KeyboardInterrupt:
        print("mreg: interrupted; chunks whose hashes matched stay in the local store, rerun to resume", file=sys.stderr)
        sys.exit(130)


def cmd_resolve(a):
    sys.exit(ni_guard("resolve", a, lambda: ni_run("resolve", a, list(a.entries))))


def cmd_env(a):
    sys.exit(ni_guard("env", a, lambda: ni_env(a)))


def ni_probe(a):
    """True when the registry serves a declaration-level store for the train (a pointer exists). NIError for auth/network."""
    d = os.path.abspath(a.dir)
    cfg, cc, lock = ni_load_cfg(d)
    train = getattr(a, "train", None) or (lock or {}).get("train") or cc.get("train") or cfg.get("train")
    f = Fetcher()
    if not train:
        try:
            ts = f.json("/v1/index/trains.json").get("trains") or []
        except NIError as e:
            if _not_found(e):
                return False
            raise
        if not ts:
            return False
        train = ts[-1]["train"]
    try:
        read_pointer(f, train)
        return True
    except NIError as e:
        if e.kind != "not_on_train":
            raise
    # A train can publish package-specific stores before it has a default store.
    entries = getattr(a, "ids", None) or getattr(a, "modules", None) or cc.get("declarations", [])
    asked = getattr(a, "build", None)
    try:
        td = f.json(f"/v1/index/trains/{train}.json")
        discover_store(f, train, td, entries, asked, getattr(a, "source_manifest_sha256", None))
    except NIError as e:
        if not asked and not getattr(a, "source_manifest_sha256", None) and (e.kind == "not_on_train" or _not_found(e)):
            return False
        raise
    return True


def ni_index(a):
    """`mreg index`: make sure the hash-matched index of the train's current (or the locked) build is in the local cache and say where
    it is. For tools that read the assignment table themselves (the end-to-end harness); the tables are the ones the pointer's
    hashes cover."""
    t0 = time.time()
    d = os.path.abspath(a.dir)
    cfg, cc, lock = ni_load_cfg(d)
    f, store = Fetcher(), Store()
    train = getattr(a, "train", None) or (lock or {}).get("train") or cc.get("train") or cfg.get("train")
    if not train:
        ts = f.json("/v1/index/trains.json").get("trains") or []
        if not ts:
            raise NIError("not_on_train", "the registry lists no train")
        train = ts[-1]["train"]
    if not _NAME_OK.match(train):
        raise NIError("error", f"bad train name {train!r}")
    ptr = read_pointer(f, train)
    build, want = ptr["build"], ptr["index_sha256"]
    asked = getattr(a, "build", None)
    if asked and asked != build:
        raise NIError("not_on_train", f"--build {asked}: the registry's current build of {train} is {build}")
    idir, meta, fresh = ensure_index(f, store, train, build, want)
    pvariant = getattr(a, "variant", None) or "checking"
    pinfo = packed_info(ptr, pvariant)
    prep = packed_empty_report(pinfo)
    if pinfo is not None and not getattr(a, "no_packed", False):
        try:
            Packed.open(f, store, train, build, pvariant, pinfo, want["manifest.tsv.gz"]).close()
            prep.update({"reason": "tables cached", "tables_cached": True})
        except NIError as e:
            if e.kind == "auth":
                raise
            prep["error"] = f"{e.kind}: {e.message}"
    payload = {"schema": NI_SCHEMA, "ok": True, "command": "index", "packed": prep, "registry": f.base, "train": train, "build": build,
               "variants": ptr["variants"], "published_at": ptr.get("published_at"), "manifest_sha256": want["manifest.tsv.gz"],
               "index_sha256": dict(want), "index_dir": idir, "fetched": fresh, "lookup": meta["lookup"], "requests": f.requests,
               "seconds": round(time.time() - t0, 3)}
    ni_out(a, payload, [f"index of train {train} build {build}: {meta['lookup']['declarations']} declarations, "
                        f"{meta['lookup']['chunks']} chunks, {meta['lookup']['edges']} edges; hashes matched the pointer's recorded SHA-256 "
                        f"({'fetched' if fresh else 'already cached'}, {f.requests} requests) in {idir}"])
    return 0


def cmd_index(a):
    sys.exit(ni_guard("index", a, lambda: ni_index(a)))


def ni_flags(p, install=False, ci=False):
    p.add_argument("--json", action="store_true", help="one JSON document on stdout (schema mreg-named-import/1)")
    p.add_argument("--jobs", type=int, default=16, help="parallel requests (default 16)")
    p.add_argument("--quiet", action="store_true", help="no progress line")
    p.add_argument("--max-requests", type=int, default=DEFAULT_MAX_REQUESTS, metavar="N",
                   help=f"refuse (exit 21) before fetching when the cone needs more than N chunk requests (default {DEFAULT_MAX_REQUESTS})")
    p.add_argument("--allow-over-budget", action="store_true", help="proceed although the cone needs more than --max-requests requests")
    p.add_argument("--no-packed", action="store_true", help="never use the ranged archives: one request per chunk file")
    p.add_argument("--range-requests", type=int, metavar="N", help="at most N range requests per import (default: the store's policy, 100)")
    p.add_argument("--packed-min", type=int, metavar="N", default=None,
                   help=f"use the archives only when at least N chunks are missing, or their tables are cached (default {PACKED_MIN_CHUNKS})")
    if install or ci:
        p.add_argument("--allow-unverified", action="store_true",
                       help="install builds that fail the strict audit (unsigned, a gate not passing) and declaration chunks (experimental, "
                            "no proof check); they stay marked UNVERIFIED in the output, mreg.lock and `mreg audit`")
    if ci:
        p.add_argument("--chunks-only", action="store_true", help="restore mreg-chunks.lock.json only")
        return
    p.add_argument("--variant", choices=VARIANTS, help="checking (default) or full; one per project")
    p.add_argument("--build", help="the exact declaration store build on this train")
    p.add_argument("--source-manifest-sha256", help="pin one declaration package to an exact signed source manifest")
    p.add_argument("--chunk-dir", help="chunk directory relative to the project (default .lake/mreg-chunks/<train>)")
    p.add_argument("--entry", help="generated entry file (default MregChunks.lean)"); p.add_argument("--no-entry", action="store_true")
    p.add_argument("--chunks", action="store_true", help="require the declaration-level store (no module-level fallback)")
    p.add_argument("--module-level", "--preserve-behavior", action="store_true",
                   help="install original modules including instances, tactics, initializers and runtime code")
    if install:
        p.add_argument("--upgrade-build", action="store_true", help="move the project to the registry's current build")


# ---------------------------------------------------------------- doctor (T-C5)
DOCTOR_SCHEMA = "mreg-doctor/0"        # a working id, NOT frozen: fields may be added, renamed or removed until it is frozen
ADDRESS_SPACE_NOTE = ("Lean maps every .olean, so a large cone needs 8.1 to 9.2 GiB of address space for 2.5 to 4.1 GB resident memory. "
                      "Never cap address space (for example with `ulimit -v`); cap resident memory instead.")
DOCTOR_PROBE_TRAIN = "lean-4.35.0"


def _tool_version(name):
    """{"found": path or None, "version": first output line of `<name> --version` or None}. Nothing else is ever run."""
    path = shutil.which(name)
    out = {"found": path, "version": None}
    if path:
        try:
            r = subprocess.run([path, "--version"], capture_output=True, text=True, timeout=20, stdin=subprocess.DEVNULL)
            line = ((r.stdout or "").strip() or (r.stderr or "").strip()).splitlines()
            out["version"] = line[0][:120] if line else None
        except (OSError, subprocess.SubprocessError):
            pass
    return out


def _zstd_support():
    out = {"module_compression_zstd": False, "module_zstandard": False, "cli": None, "usable": False, "used": None}
    try:
        from compression import zstd as _z      # noqa: F401
        out["module_compression_zstd"] = True
    except ImportError:
        pass
    try:
        import zstandard as _zs                 # noqa: F401
        out["module_zstandard"] = True
    except ImportError:
        pass
    out["cli"] = shutil.which("zstd")
    out["used"] = ("compression.zstd" if out["module_compression_zstd"] else "zstandard" if out["module_zstandard"]
                   else "zstd program" if out["cli"] else None)
    out["usable"] = out["used"] is not None
    return out


def _address_space():
    out = {"note": ADDRESS_SPACE_NOTE, "limit_bytes": None, "limited": False, "checked": False}
    try:
        import resource
        soft, _hard = resource.getrlimit(resource.RLIMIT_AS)
        out["checked"] = True
        if soft != resource.RLIM_INFINITY:
            out["limit_bytes"], out["limited"] = soft, True
    except (ImportError, ValueError, OSError):
        pass
    return out


def _credential_state():
    """Kind and source of the stored credential, never its value or its owner. Returns (report, value for the probe)."""
    out = {"present": False, "source": None, "kind": "none", "note": None, "file": None}
    p = token_path()
    out["file"] = {"path": p, "exists": os.path.isfile(p), "mode": None, "permission_note": None}
    if out["file"]["exists"]:
        if sys.platform == "win32":
            if _win_has_protected_acl(p):
                out["file"]["permission_note"] = "Windows: protected ACL (owner-only)"
            else:
                out["file"]["permission_note"] = ("Windows: mode bits are not enforced and mreg does not read or change ACLs; the file has "
                                                  "the access rules of your profile folder")
        else:
            try:
                m = os.stat(p).st_mode & 0o777
                out["file"]["mode"] = oct(m)
                out["file"]["permission_note"] = ("readable by you only" if not m & 0o077
                                                  else "readable by other users: run `chmod 600` on it")
            except OSError:
                pass
    try:
        tok, src = read_token()
    except SystemExit:
        out["kind"] = "unreadable"
        return out, None
    if not tok:
        return out, None
    out["present"] = True
    out["source"] = "environment" if src.startswith("environment") else "file"
    if tok.startswith("mreg_"):
        out["kind"] = "per_user_key" if decode_key(tok) is not None else "damaged_key"
    else:
        out["kind"] = "not_a_per_user_key"
    out["note"] = {"per_user_key": "a per-user key (judged by shape only: the registry checks the signature)",
                   "damaged_key": "looks like a per-user key but is damaged: run `mreg login`",
                   "not_a_per_user_key": "not a per-user key: will be refused (the old shared token was retired on 2026-11-12); "
                                         "run `mreg login`"}[out["kind"]]
    return out, tok


def _store_state():
    root = os.environ.get("MREG_STORE") or os.path.join(os.path.expanduser("~"), ".mreg", "store")
    out = {"path": root, "exists": os.path.isdir(root), "writable": False, "free_bytes": None, "note": None}
    probe, blocked = root, False
    while probe and not os.path.isdir(probe):
        if os.path.exists(probe):
            blocked = True          # a file where a directory is needed
        parent = os.path.dirname(probe)
        if parent == probe:
            break
        probe = parent
    try:
        out["free_bytes"] = shutil.disk_usage(probe).free
    except OSError:
        pass
    if os.path.isdir(root):
        try:
            fd, tmp = _tempfile.mkstemp(prefix=".doctor-", dir=root)
            os.close(fd)
            os.remove(tmp)
            out["writable"] = True
        except OSError:
            pass
    else:
        out["writable"] = os.access(probe, os.W_OK) and not blocked     # it would be created below the nearest existing directory
        out["note"] = (f"a file is in the way below {probe}" if blocked else f"does not exist yet; would be created below {probe}")
    return out


def _registry_probe(train, tok):
    """One request: bytes 0-63 of the declaration store pointer. Returns a dict; never raises; never shows the key."""
    base = os.environ.get("MREG_REGISTRY", "https://mathregistry.com").rstrip("/")
    path = f"/x/decl/{train}/current.json"
    out = {"base_kind": None, "path": path, "requests": 0, "status": None, "denial": None, "bytes": None, "ok": False, "error": None}
    why = registry_url_problem(base)
    if why:
        out["error"] = f"registry address refused: {why}"
        return out
    if base.startswith("file:"):
        out["base_kind"] = "file"
        p = os.path.join(urllib.request.url2pathname(urllib.parse.urlparse(base).path), *[x for x in path.split("/") if x])
        out["ok"] = os.path.isfile(p)
        out["status"] = "present" if out["ok"] else "absent"
        return out
    if base.startswith("s3://"):
        out["base_kind"], out["error"] = "s3", "not checked (s3 registry)"
        return out
    out["base_kind"] = "http"
    if not (base.startswith("https://") or re.match(r"^http://(localhost|127\.0\.0\.1|\[::1\])(:|/|$)", base)):
        out["error"] = "registry address must be https (http only for localhost) or file://"
        return out
    if not tok:
        out["error"] = "not sent: no credential"
        return out
    u = urllib.parse.urlparse(base)
    cls = http.client.HTTPSConnection if u.scheme == "https" else http.client.HTTPConnection
    c = None
    try:
        c = cls(u.hostname, u.port, timeout=20)
        out["requests"] = 1
        c.request("GET", u.path.rstrip("/") + path, headers={"x-mreg-token": tok, "User-Agent": "mreg/" + VERSION,
                                                              "Accept-Encoding": "identity", "Range": "bytes=0-63"})
        r = c.getresponse()
        out["status"] = r.status
        dn = (r.getheader(DENIAL_HEADER) or "").strip()
        out["denial"] = re.sub(r"[^A-Za-z0-9_.-]", "?", dn)[:40] or None
        out["bytes"] = len(r.read(64))
        out["ok"] = r.status in (200, 206)
    except (OSError, http.client.HTTPException, ValueError) as e:
        out["error"] = f"cannot reach the registry ({type(e).__name__})"
    finally:
        if c is not None:
            try:
                c.close()
            except Exception:
                pass
    return out


def doctor_report(train=DOCTOR_PROBE_TRAIN):
    problems, warnings = [], []
    py = sys.version_info
    rep = {"schema": DOCTOR_SCHEMA, "schema_frozen": False, "mreg_version": VERSION}
    rep["python"] = {"version": ".".join(map(str, py[:3])), "executable": sys.executable, "ok": py >= (3, 10),
                     "platform": platform_triple()}
    if not rep["python"]["ok"]:
        problems.append("Python 3.10 or newer is needed")
    rep["tools"] = {n: _tool_version(n) for n in ("git", "lake", "lean")}
    for n in ("git", "lake"):
        if not rep["tools"][n]["found"]:
            warnings.append(f"{n} was not found on PATH (needed by install, add and ci of modules)")
    if not rep["tools"]["lean"]["found"]:
        warnings.append("lean was not found on PATH (needed to use the installed modules, not to fetch them)")
    rep["zstd"] = _zstd_support()
    if not rep["zstd"]["usable"]:
        problems.append("no zstd support: Python 3.14, the zstandard module or the zstd program is needed")
    rep["address_space"] = _address_space()
    if rep["address_space"]["limited"] and rep["address_space"]["limit_bytes"] < 10 * 2 ** 30:
        warnings.append("this shell caps address space below 10 GiB: Lean will fail on large cones")
    rep["credential"], tok = _credential_state()
    kind = rep["credential"]["kind"]
    http_registry = os.environ.get("MREG_REGISTRY", "https://mathregistry.com").startswith(("http://", "https://"))
    if http_registry and kind != "per_user_key":
        problems.append({"none": "no credential: run `mreg login`, or set MREG_TOKEN",
                         "unreadable": "the credential file cannot be read",
                         "damaged_key": "the stored key is damaged: run `mreg login`",
                         "not_a_per_user_key": "the stored value is not a per-user key and will be refused: run `mreg login`"}[kind])
    if os.environ.get("MREG_TOKEN") and rep["credential"]["file"]["exists"]:
        warnings.append("MREG_TOKEN is set and takes precedence over the file")
    rep["store"] = _store_state()
    if not rep["store"]["writable"]:
        problems.append("the local store is not writable")
    rep["registry"] = _registry_probe(train, tok)
    rp = rep["registry"]
    if rp["base_kind"] == "http":
        if rp["requests"] and not rp["ok"]:
            problems.append((f"the registry answered {rp['status']}" + (f" ({rp['denial']})" if rp["denial"] else ""))
                            if rp["status"] is not None else (rp["error"] or "the registry request failed"))
        elif rp["error"] and not rp["requests"] and kind == "per_user_key":
            problems.append(rp["error"])
    elif rp["base_kind"] is None and rp["error"]:
        problems.append(rp["error"])
    rep["problems"], rep["warnings"] = problems, warnings
    rep["ok"] = not problems
    return rep


def cmd_doctor(a):
    rep = doctor_report(a.train)
    if a.json:
        print(json.dumps(rep, indent=1))
    else:
        py, t, z, cr, st, rg = rep["python"], rep["tools"], rep["zstd"], rep["credential"], rep["store"], rep["registry"]
        print(f"mreg {VERSION} doctor ({DOCTOR_SCHEMA}, not frozen)")
        print(f"python: {py['version']} on {py['platform']} ({'ok' if py['ok'] else 'too old'})")
        for n in ("git", "lake", "lean"):
            print(f"{n}: " + (f"{t[n]['version'] or 'found'} ({t[n]['found']})" if t[n]["found"] else "not found on PATH"))
        print("zstd: " + (z["used"] if z["usable"] else "NOT available"))
        print("address space: " + rep["address_space"]["note"])
        if rep["address_space"]["limited"]:
            print(f"  this shell limits address space to {rep['address_space']['limit_bytes']} bytes")
        print("credential: " + (f"{cr['kind']} from the {cr['source']}; {cr['note']}" if cr["present"] else cr["kind"]))
        if cr["file"]["permission_note"]:
            print(f"  token file {cr['file']['path']}: {cr['file']['permission_note']}")
        print(f"store: {st['path']} ({'writable' if st['writable'] else 'NOT writable'}"
              + (f", {st['free_bytes']} bytes free" if st["free_bytes"] is not None else "") + ")")
        if rg["requests"] and rg["status"] is not None:
            res = f"status {rg['status']}" + (f", denial {rg['denial']}" if rg["denial"] else "") + f", {rg['bytes']} bytes"
        else:
            res = str(rg["status"] or rg["error"] or "no request")
        print(f"registry ({rg['base_kind']}): {rg['path']}: {res}")
        for w in rep["warnings"]:
            print("warning: " + w)
        for pr in rep["problems"]:
            print("problem: " + pr)
        print("result: " + ("ok" if rep["ok"] else f"{len(rep['problems'])} problem(s)"))
    return 0 if rep["ok"] else EXIT["error"]


REPLAY_SECONDS_PER_MODULE_DEFAULT = 2.1     # seconds of leanchecker time per module; see REPLAY_FIGURE_SOURCE
REPLAY_FIGURE_SOURCE = ("measured 2026-11-13: 106 modules of a Mathlib/Batteries/ImportGraph closure of 106 modules, 220 s, 4 modules per leanchecker process, "
                        "ext4 in WSL on a shared machine; modules with larger import closures take longer")
# ---------------------------------------------------------------- user lifecycle, phase A (PHASE_A.md): check, info, why, search, one train, --json
# Every command here answers with ONE JSON document on stdout when --json is given (text goes to stderr then) and uses the EXIT table above.
# Schemas: mreg-check/1, mreg-info/1, mreg-why/1, mreg-search/1; the existing commands that had no --json get mreg-<command>/1.

BASELINE_TRAIN = "lean-4.35.0"
LC_SCHEMAS = {"check": "mreg-check/1", "info": "mreg-info/1", "why": "mreg-why/1", "search": "mreg-search/1"}
BASELINE_PREFIX = "leanprover-community/"      # Mathlib and its dependencies: the packages the baseline train holds from the community
PUBLIC_OLEAN_SENTENCE = ("The public .olean content of dependencies is not checked until the registry's public-file gate exists; "
                         "the re-hash pins the bytes to the registry's record, it does not make them right.")
STATEMENT_SENTENCE = ("No kernel checks that a theorem says what its author meant: read the statements and the definitions they use "
                      "before you rely on a result.")
ACCEPTED_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
LC_NOT_REPLAYED = ("not replayed here; relies on registry gates G2-G10 (label {label}) and the re-hash of step 1")


def _printable(s):
    """Text that the current stdout encoding can show (a Windows console cannot show every Lean symbol): other characters become ?."""
    enc = getattr(sys.stdout, "encoding", None) or "utf-8"
    try:
        return str(s).encode(enc, "replace").decode(enc, "replace")
    except (LookupError, ValueError):
        return str(s)


def _die_to_error(e):
    """A NIError for the text of a SystemExit that a legacy helper raised with die()."""
    msg = str(e.code)
    if msg.startswith("mreg: "):
        msg = msg[6:]
    low = msg.lower()
    if "403 from the registry" in low or low.startswith("no access token"):
        kind = "auth"
    elif "takedown" in low or "taken down" in low or low.startswith("404") or "404 from the registry" in low:
        kind = "missing_object"
    elif low.startswith("cannot fetch") or low.startswith("cannot read"):
        kind = "network"
    else:
        kind = "error"
    return NIError(kind, msg)


def lc_error_out(cmd, a, e):
    """Print the failure of a lifecycle command (a JSON document on stdout with --json, else a line on stderr); returns the exit code."""
    if getattr(a, "json", False):
        d = {"schema": LC_SCHEMAS.get(cmd, f"mreg-{cmd}/1"), "ok": False, "command": cmd, "exit_code": e.code,
             "error": {"kind": e.kind, "exit_code": e.code, "message": e.message}}
        d["error"].update({k: v for k, v in e.extra.items() if k not in d["error"]})
        print(json.dumps(d, indent=1))
    print(f"mreg: {e.kind}: {_printable(e.message)}", file=sys.stderr)
    return e.code


def lc_guard(cmd, a, fn):
    try:
        return fn()
    except NIError as e:
        sys.exit(lc_error_out(cmd, a, e))
    except SystemExit as e:
        if isinstance(e.code, str):
            sys.exit(lc_error_out(cmd, a, _die_to_error(e)))
        raise
    except KeyboardInterrupt:
        print("mreg: interrupted", file=sys.stderr)
        sys.exit(130)


JSON_WRAPPED = ("install", "ci", "add", "view", "train", "init", "whoami", "login", "logout")
_json_data = {}            # structured fields a text command leaves for its --json document (view, train, init, whoami)


def run_json_wrapped(a, cmd, fn, extra=None):
    """--json for a command that prints text only: run fn() with its text on stderr and print ONE document mreg-<cmd>/1 on stdout.
    A document that fn itself printed on stdout (the named-import commands print their own) is passed through unchanged.
    `extra` (optional callable) returns more fields for the document after fn finished."""
    cap, code, msg = io.StringIO(), 0, None
    with contextlib.redirect_stdout(cap):
        try:
            fn()
        except SystemExit as e:
            if isinstance(e.code, str):
                code, msg = 1, e.code
            elif e.code is None:
                code = 0
            else:
                code = int(e.code)
    if code == 130:                  # interrupted: as before, nothing on stdout
        sys.exit(130)
    out = scrub(cap.getvalue())
    pos = 0
    for line in out.splitlines(keepends=True):       # a document the command printed itself, perhaps after some text lines
        if line.startswith("{"):
            try:
                if isinstance(json.loads(out[pos:]), dict):
                    if out[:pos].strip():
                        print(out[:pos], end="", file=sys.stderr)
                    print(out[pos:].strip())
                    sys.exit(code)
            except ValueError:
                pass
        pos += len(line)
    if out:
        print(out, end="" if out.endswith("\n") else "\n", file=sys.stderr)
    if msg:
        print(scrub(msg), file=sys.stderr)
    d = {"schema": f"mreg-{cmd}/1", "ok": code == 0, "command": cmd, "exit_code": code,
         "messages": [l for l in out.splitlines() if l.strip()]}
    if msg:
        d["error"] = {"kind": "error", "exit_code": code, "message": scrub(msg.replace("mreg: ", "", 1))}
    if extra:
        try:
            d.update(extra() or {})
        except Exception:
            pass
    print(json.dumps(d, indent=1))
    sys.exit(code)


# ---- the project: its train, its own modules, what is installed

def lc_project_train(d, asked=None):
    """(train name, where it came from). Order: --train, the chunk lock, mreg.json, the train whose toolchain is the project's
    (a registry train document is not read here: the answer is the recorded one), else the baseline."""
    cl = _read_json(os.path.join(d, CHUNK_LOCK))
    rec, rec_from = (cl["train"], CHUNK_LOCK) if cl and cl.get("train") else (None, None)
    if rec is None:
        t = load_cfg(d).get("train")
        rec, rec_from = (t, "mreg.json") if t else (None, None)
    if asked:
        if rec and asked != rec:
            raise NIError("forbidden_mix", f"--train {asked} differs from the project's recorded train {rec} ({rec_from}); a project has one train, "
                          "and --train never overrides it: start a new project for the other train", train=rec, asked=asked)
        return asked, "--train"
    if rec:
        return rec, rec_from
    return BASELINE_TRAIN, "baseline"


def lc_toolchain(d):
    try:
        return open(os.path.join(d, "lean-toolchain"), encoding="utf-8").read().strip() or None
    except OSError:
        return None


def lc_lib_roots(d):
    """Module roots of the project's own libraries (lakefile.toml `[[lean_lib]]`: name or roots); None = unknown (a lakefile.lean)."""
    p = os.path.join(d, "lakefile.toml")
    if not os.path.exists(p):
        return None
    txt = open(p, encoding="utf-8", errors="replace").read()
    roots = []
    for blk in txt.split("[[lean_lib]]")[1:]:
        blk = blk.split("[[", 1)[0]
        m = re.search(r'^\s*roots\s*=\s*\[([^\]]*)\]', blk, re.M)
        if m:
            roots += re.findall(r'"([^"]+)"', m.group(1))
            continue
        m = re.search(r'^\s*name\s*=\s*"([^"]+)"', blk, re.M)
        if m:
            roots.append(m.group(1))
    return roots or None


def lc_own_modules(d):
    """[(module name, source path)] of the project's own Lean files that belong to its libraries."""
    roots = lc_lib_roots(d)
    out = []
    for p in sorted(own_sources(d)):
        rel = os.path.relpath(p, d)[:-5].split(os.sep)
        if any(not x or x.startswith(".") for x in rel):
            continue
        mod = ".".join(rel)
        if roots is not None and rel[0] not in roots:
            continue
        out.append((mod, p))
    return out


def lc_strip_lean(text):
    """The text with comments (nested block comments, line comments), string and character literals replaced by spaces
    (line structure kept), so a scan sees only code."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        c = text[i]
        two = text[i:i + 2]
        if depth:
            if two == "/-":
                depth += 1; out.append("  "); i += 2
            elif two == "-/":
                depth -= 1; out.append("  "); i += 2
            else:
                out.append("\n" if c == "\n" else " "); i += 1
        elif two == "/-":
            depth = 1; out.append("  "); i += 2
        elif two == "--":
            while i < n and text[i] != "\n":
                out.append(" "); i += 1
        elif c == '"':
            out.append(" "); i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\" and i + 1 < n:
                    out.append(" "); i += 1
                out.append("\n" if text[i] == "\n" else " "); i += 1
            out.append(" "); i += 1
        else:
            out.append(c); i += 1
    return "".join(out)


UNSOUND_TOKENS = [("sorry", r"(?<![\w.'])sorry(?![\w'])"), ("admit", r"(?<![\w.'])admit(?![\w'])"),
                  ("native_decide", r"(?<![\w.'])native_decide(?![\w'])"), ("decide +native", r"(?<![\w.'])decide\s*\+native(?![\w'])"),
                  ("bv_decide", r"(?<![\w.'])bv_decide(?![\w'])"), ("axiom", r"(?<![\w.'])axiom(?![\w'])"),
                  ("debug.skipKernelTC", r"(?<![\w'])debug\.skipKernelTC(?![\w'])")]


def lc_scan_sources(d, modules, allow=(), allowed_out=None):
    """[{file, line, token}] for every sorry, admit, native_decide, decide +native, bv_decide, axiom and skipKernelTC in the code of the
    project's own modules (comments and strings are ignored)."""
    found = []
    for mod, p in modules:
        try:
            text = open(p, encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        code = lc_strip_lean(text)
        rel = os.path.relpath(p, d).replace(os.sep, "/")
        for tok, rx in UNSOUND_TOKENS:
            for m in re.finditer(rx, code):
                if tok == "axiom" and allow:
                    nm = re.match(r"\s+([^\s:({\[]+)", code[m.end():])
                    if nm and nm.group(1) in allow:         # `axiom NAME` named by --allow-axiom: not a failure, but reported
                        if allowed_out is not None:
                            allowed_out.append({"file": rel, "line": code.count("\n", 0, m.start()) + 1, "name": nm.group(1)})
                        continue
                found.append({"file": rel, "line": code.count("\n", 0, m.start()) + 1, "token": tok, "module": mod})
    found.sort(key=lambda r: (r["file"], r["line"], r["token"]))
    return found


# ---------------------------------------------------------------- mreg check

REPLAY_THRESHOLD_S = 600            # a dependency package whose estimated replay time is below this is replayed by default


def replay_seconds_per_module():
    return float(os.environ.get("MREG_REPLAY_SECONDS_PER_MODULE") or REPLAY_SECONDS_PER_MODULE_DEFAULT)


REPLAY_BATCH = int(os.environ.get("MREG_REPLAY_BATCH") or 4)   # modules per leanchecker process: it replays them as concurrent tasks, each with its own copy of the imports (55 Mathlib modules in one process took the memory of a 24 GB machine)
STEP_NAMES = {1: "integrity", 2: "one train", 3: "own modules", 4: "kernel replay", 5: "axioms", 6: "second kernel", 7: "statements"}
FAST_STEPS = (1, 2, 3, 5)
LAKE_BUILD_LINE = re.compile(r"\[\d+/\d+\]\s+(Building|Compiling)\s+([A-Za-z0-9_.«»']+)")
LEAN_MSG = re.compile(r"^(?:warning|error|info):\s+(?P<file>.+?\.lean):(?P<line>\d+):(?P<col>\d+):\s+(?P<msg>.*)$")

# Lean script run by steps 5 and 7: the axioms, the statement and the constants the statement uses, per theorem of the own modules.
COLLECT_LEAN = r'''import Lean
open Lean Meta

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

/-- Direct dependencies of a constant and whether it is itself an axiom: its type; the value of a definition, theorem or opaque;
an inductive's constructors and the mutual types of its block; a constructor's inductive (the same rule as registry-soundness's
`exact_axioms.py`). -/
def depsOf (env : Environment) (c : Name) : Array Name × Bool :=
  match env.find? c with
  | some ci =>
    let isAx := match ci with | .axiomInfo _ => true | _ => false
    let ds := ci.type.getUsedConstants ++ (match ci with
      | .defnInfo v => v.value.getUsedConstants
      | .thmInfo v => v.value.getUsedConstants
      | .opaqueInfo v => v.value.getUsedConstants
      | .inductInfo v => v.ctors.toArray ++ v.all.toArray          -- constructors and the mutual types of the block
      | .ctorInfo v => #[v.induct]                                   -- a constructor's inductive
      | _ => #[])
    (ds, isAx)
  | none => (#[], false)

/-- State of the axiom walk: Tarjan's strongly connected components. Constants that reach each other (a mutual or `partial`
definition, an inductive and its constructors and recursors) form one component and get ONE axiom set, the union over the
component, whatever the visit order. Only finished components are cached (`done`); the walk never answers from a constant that is
still being visited. Before 0.5.1 a constant under visit was cached as `#[]`, so a member of a cycle could get too few axioms, which
could hide an omission in the stored list (main session's review, 2026-11-13). -/
structure AxWalk where
  next : Nat := 0
  index : Std.HashMap Name Nat := {}
  low : Std.HashMap Name Nat := {}
  onStack : Std.HashSet Name := {}
  stack : Array Name := #[]
  acc : Std.HashMap Name (Std.HashSet Name) := {}
  done : Std.HashMap Name (Array Name) := {}

partial def axVisit (env : Environment) (st : IO.Ref AxWalk) (c : Name) : IO Unit := do
  let s ← st.get
  if s.done.contains c || s.index.contains c then return
  let (deps, isAx) := depsOf env c
  st.modify fun s => { s with next := s.next + 1, index := s.index.insert c s.next, low := s.low.insert c s.next,
                              onStack := s.onStack.insert c, stack := s.stack.push c,
                              acc := s.acc.insert c (if isAx then ({} : Std.HashSet Name).insert c else {}) }
  for d in deps do
    if !(← st.get).index.contains d && !(← st.get).done.contains d then
      axVisit env st d
    let s ← st.get
    match s.done.get? d with
    | some ax =>                                      -- d is finished (before, or as its own component just now)
      st.modify fun s => { s with acc := s.acc.insert c (ax.foldl (·.insert ·) (s.acc.getD c {})) }
    | none =>
      if s.onStack.contains d then                    -- d is in c's component, still open: link it
        let lowD := if s.index.get! d < s.low.get! d then s.index.get! d else s.low.get! d
        let lc := s.low.get! c
        st.modify fun s => { s with low := s.low.insert c (if lowD < lc then lowD else lc) }
  let s ← st.get
  if s.low.get! c == s.index.get! c then              -- c is the root of a component: pop it, union the members' sets
    let mut members : Array Name := #[]
    let mut stk := s.stack
    repeat
      let m := stk.back!
      stk := stk.pop
      members := members.push m
      if m == c then break
    let mut all : Std.HashSet Name := {}
    for m in members do
      for a in s.acc.getD m {} do
        all := all.insert a
    let r := all.toArray.qsort Name.lt
    st.modify fun s => members.foldl (fun s m => { s with done := s.done.insert m r, onStack := s.onStack.erase m,
                                                          acc := s.acc.erase m }) { s with stack := stk }

/-- The axioms a constant depends on, computed from the types and values in the loaded environment. Lean's own `collectAxioms` reads
the axiom list STORED in the olean of an imported declaration and does not look at its proof; this one never does. -/
def axiomsOf (env : Environment) (st : IO.Ref AxWalk) (c : Name) : IO (Array Name) := do
  axVisit env st c
  return (← st.get).done.getD c #[]

unsafe def main (args : List String) : IO UInt32 := do
  let [modsCsv, thmsCsv] := args | do IO.eprintln "usage: Collect MODULES_CSV THEOREMS_CSV"; return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mods := ((modsCsv.splitOn ",").filter (· != "")).map String.toName
  let wanted := ((thmsCsv.splitOn ",").filter (· != "")).map String.toName
  let env ← importModules (mods.toArray.map fun m => ({ module := m } : Import)) {} (loadExts := true)
  let ctx : Core.Context := { fileName := "<mreg-check>", fileMap := default }
  let seen ← IO.mkRef ({} : AxWalk)
  let modName (n : Name) : String :=
    match env.getModuleIdxFor? n with
    | some i => (env.header.moduleNames[i.toNat]!).toString
    | none => ""
  let mut names : Array Name := #[]
  let mut missingModule := false
  for m in mods do
    match env.header.moduleNames.findIdx? (· == m) with
    | some i =>
      for n in env.header.moduleData[i]!.constNames do
        match env.find? n with
        | some (.thmInfo _) => if wanted.isEmpty || wanted.contains n then names := names.push n
        | _ => pure ()
    | none =>
      IO.eprintln s!"mreg-check: module {m} not found in the imported environment"
      missingModule := true
  for w in wanted do
    unless names.contains w do
      IO.println (Json.mkObj [("name", Json.str w.toString), ("missing", Json.bool true)]).compress
  for n in names do
    let some ci := env.find? n | continue
    let (stored, _) ← (collectAxioms n : CoreM (Array Name)).toIO ctx { env }
    let axs ← axiomsOf env seen n
    let stmt ← do
      try
        let (s, _) ← ((Meta.MetaM.run' (do return toString (← ppExpr ci.type)) : CoreM String)).toIO ctx { env }
        pure (s, "pp")
      catch _ => pure (toString ci.type, "raw")
    let uses := (ci.type.getUsedConstants).filterMap fun u =>
      match env.find? u with
      | some c => some (Json.mkObj [("name", Json.str u.toString), ("module", Json.str (modName u)), ("kind", Json.str (kindOf c))])
      | none => none
    IO.println (Json.mkObj [("name", Json.str n.toString), ("module", Json.str (modName n)),
      ("axioms", Json.arr (axs.map fun a => Json.str a.toString)),
      ("axioms_stored", Json.arr ((stored.qsort Name.lt).map fun a => Json.str a.toString)),
      ("statement", Json.str stmt.1), ("statement_form", Json.str stmt.2), ("uses", Json.arr uses)]).compress
  return (if missingModule then 3 else 0)
'''


class CheckCtx:
    def __init__(self, a):
        self.a = a
        self.dir = os.path.abspath(a.dir)
        self.t0 = time.time()
        self._reg = None
        self.has_state = os.path.exists(os.path.join(self.dir, STATE))
        self.chunk_admission = None
        self.chunk_lock = _read_json(os.path.join(self.dir, CHUNK_LOCK))
        self.lock = _read_json(os.path.join(self.dir, "mreg.lock"))
        self.modules = lc_own_modules(self.dir)
        self.train, self.train_from = lc_project_train(self.dir, getattr(a, "train", None))
        self.audit_rows = []
        self.lean_path = None
        self.tools = {}
        self.built = False
        self.notes = []

    def registry(self):
        if self._reg is None:
            self._reg = Registry()
            self._reg.accept_new_key = bool(getattr(self.a, "accept_new_key", False))
        return self._reg

    def log(self, msg):
        print(_printable(msg), file=sys.stderr)


def _step(n, verdict, t0, failures=None, kind=None, **details):
    complete = details.pop("step_complete", verdict == "pass")
    return {"step": n, "name": STEP_NAMES[n], "verdict": verdict, "complete": bool(complete), "seconds": round(time.time() - t0, 2),
            "failures": failures or [], "failure_kind": kind, "details": details}


def lc_lock_packages(ctx):
    """[{lake_name, id, version, build_key, manifest_sha256, signed, from}] of the module-level lock."""
    return [e for e in ((ctx.lock or {}).get("packages") or []) if e.get("from") == "registry"]


def lc_pkg_doc(ctx, pid, cache={}):
    key = (id(ctx), pid)
    if key not in cache:
        cache[key] = ctx.registry().json(f"/v1/index/{pid}.json", missing_ok=True)
    return cache[key]


def lc_build_entry(doc, version, key):
    return next((b for b in (((doc or {}).get("versions") or {}).get(version) or {}).get("builds", []) if b.get("build_key") == key), None)


# ---- step 1

def step_integrity(ctx):
    t0, fails, det, kind = time.time(), [], {}, None
    if not ctx.has_state and not ctx.chunk_lock:
        return _step(1, "fail", t0, [f"nothing installed: no {STATE.replace(os.sep, '/')} and no {CHUNK_LOCK} (`mreg install` writes them)"], "error")
    if ctx.has_state:
        proj = Project(ctx.dir)
        reg = ctx.registry()
        state = load_state(proj)
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            n, bad, book, names_bad = rehash_installed(proj, reg, state)
        det["module_level"] = {"files": n, "matched": n - bad - book, "mismatched": names_bad, "bookkeeping_rewritten": book,
                               "packages": len(state["packages"])}
        if n == 0:
            fails.append("the module-level state lists no installed files")
            kind = kind or "error"
        for line in names_bad:
            fails.append("MISMATCH " + line)
            kind = "hash_mismatch"
        docs, rows = {}, []
        locked = lc_lock_packages(ctx)
        if ctx.lock is not None:
            st_keys = {n: v.get("build_key") for n, v in state["packages"].items()}
            lk_keys = {e["lake_name"]: e.get("build_key") for e in locked}
            diffs = ([f"in {STATE.replace(os.sep, '/')} only: {n} (build {st_keys[n]})" for n in sorted(set(st_keys) - set(lk_keys))] +
                     [f"in mreg.lock only: {n} (build {lk_keys[n]})" for n in sorted(set(lk_keys) - set(st_keys))] +
                     [f"{n}: state says build {st_keys[n]}, mreg.lock says {lk_keys[n]}" for n in sorted(set(st_keys) & set(lk_keys)) if st_keys[n] != lk_keys[n]])
            det["state_vs_lock"] = {"differences": diffs}
            for x in diffs:
                fails.append("state and lock differ: " + x)
                kind = kind or "hash_mismatch"
        if not locked and ctx.lock is None:
            fails.append("no mreg.lock: the installed builds cannot be audited (`mreg install` writes it)")
            kind = kind or "error"
        for e in locked:
            row = audit_build(reg, e["id"], e["version"], e["build_key"], e.get("manifest_sha256"), [], docs, True)
            rows.append(row)
            for p in row["problems"]:
                fails.append(f"audit {e['id']} {e['version']}: {p}")
                kind = kind or "error"
        ctx.audit_rows = rows
        det["audit"] = [{"id": r["id"], "version": r["version"], "build_key": r["build_key"], "ok": r["ok"], "labels": r["labels"],
                         "signature": r["signature"], "problems": r["problems"]} for r in rows]
    if ctx.chunk_lock:
        cl = ctx.chunk_lock
        if cl.get("schema") != CHUNK_LOCK_SCHEMA:
            raise NIError("error", f"unknown declaration lock schema in {CHUNK_LOCK}")
        ctx.chunk_admission = installed_chunk_admission(ctx.a, cl, full_reports=True)
        chunk_dir = os.path.abspath(os.path.join(ctx.dir, *cl["chunk_dir"].split("/")))
        bad, missing = [], []
        for c in cl.get("chunks", []):
            p = os.path.join(chunk_dir, *chunk_rel(c["id"]).split("/"))
            if not os.path.exists(p):
                missing.append(c["id"])
            elif os.path.getsize(p) != c["bytes_raw"] or sha256_file(p) != c["sha256_raw"]:
                bad.append(c["id"])
        det["chunks"] = {"checked": len(cl.get("chunks", [])), "mismatched": bad, "missing": missing, "train": cl.get("train"),
                         "build": cl.get("build"), "variant": cl.get("variant")}
        if ctx.chunk_admission:
            det["chunks"]["admission"] = ctx.chunk_admission
        for c in bad:
            fails.append(f"MISMATCH chunk {c}")
            kind = "hash_mismatch"
        for c in missing:
            fails.append(f"MISSING chunk {c}")
            kind = kind or "hash_mismatch"
    return _step(1, "fail" if fails else "pass", t0, fails, kind, **det)


# ---- step 2

def step_one_train(ctx):
    t0, fails, kinds, det = time.time(), [], [], {"train": ctx.train, "train_from": ctx.train_from}
    tc = lc_toolchain(ctx.dir)
    det["lean_toolchain"] = tc
    if ctx.chunk_lock and ctx.chunk_lock.get("train") != ctx.train:
        fails.append(f"chunks are from train {ctx.chunk_lock.get('train')}, the project is on train {ctx.train} ({ctx.train_from})")
        kinds.append("forbidden_mix")
    td = None
    try:
        td = ctx.registry().json(f"/v1/index/trains/{ctx.train}.json", missing_ok=True)
    except SystemExit as e:
        raise _die_to_error(e)
    if td is None:
        fails.append(f"the registry has no train {ctx.train}")
        kinds.append("not_on_train")
    else:
        det["train_toolchain"] = td.get("toolchain")
        if tc is None:
            fails.append("the project has no lean-toolchain file")
            kinds.append("toolchain_mismatch")
        elif norm_toolchain(tc) != norm_toolchain(td.get("toolchain")):
            fails.append(f"lean-toolchain is {tc}, train {ctx.train} is {td.get('toolchain')}")
            kinds.append("toolchain_mismatch")
    pk = []
    for e in lc_lock_packages(ctx):
        doc = lc_pkg_doc(ctx, e["id"])
        ent = lc_build_entry(doc, e["version"], e["build_key"])
        trains = (ent or {}).get("trains") or []
        pk.append({"id": e["id"], "version": e["version"], "trains": trains})
        if ent is None:
            fails.append(f"{e['id']} {e['version']}: the registry has no such build, so its train is unknown")
            kinds.append("missing_object")
        elif ctx.train not in trains:
            fails.append(f"{e['id']} {e['version']} is on train(s) {', '.join(trains) or 'none'}, the project is on train {ctx.train}: it does not belong in this project")
            kinds.append("forbidden_mix")
    det["packages"] = pk
    return _step(2, "fail" if fails else "pass", t0, fails, ("forbidden_mix" if "forbidden_mix" in kinds else kinds[0] if kinds else "error") if fails else None, **det)


# ---- step 3

def lc_lean_env(ctx):
    """LEAN_PATH for running lean tools directly: the project's own build directory and every package's."""
    if ctx.lean_path is not None:
        return ctx.lean_path
    parts, root = [], read_manifest(ctx.dir) or {}
    bl = os.path.join(".lake", "build", "lib", "lean")
    parts.append(os.path.join(ctx.dir, bl))
    for p in root.get("packages", []):
        parts.append(os.path.join(package_dir(ctx.dir, root, p["name"]), bl))
    cl = ctx.chunk_lock
    if cl:
        parts.append(os.path.abspath(os.path.join(ctx.dir, *cl["chunk_dir"].split("/"))))
    ctx.lean_path = os.pathsep.join(x for x in parts if os.path.isdir(x))
    return ctx.lean_path


def lc_run(cmd, cwd, env=None, timeout=None):
    try:
        r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, errors="replace", env=env, timeout=timeout, stdin=subprocess.DEVNULL)
        return r.returncode, r.stdout, r.stderr
    except FileNotFoundError:
        return 127, "", f"{cmd[0]}: not found"
    except subprocess.TimeoutExpired as e:
        return 124, (e.stdout or "") if isinstance(e.stdout, str) else "", f"timeout after {timeout} s"


def lc_tool(ctx, name):
    """Path of a Lean tool of the project's toolchain: `lean --print-prefix` run in the project (elan picks the project's toolchain), else PATH."""
    if name in ctx.tools:
        return ctx.tools[name]
    path, resolved = None, False
    lean = shutil.which("lean")
    if lean:
        rc, out, _ = lc_run([lean, "--print-prefix"], ctx.dir, timeout=120)
        if rc == 0 and out.strip():
            resolved = True                  # the project's toolchain is known: a tool it does not have is NOT taken from another one on PATH
            for ext in (("", ".exe", ".cmd", ".bat") if sys.platform == "win32" else ("",)):
                cand = os.path.join(out.strip().splitlines()[0], "bin", name + ext)
                if os.path.exists(cand):
                    path = cand
                    break
    ctx.tools[name] = path if resolved else shutil.which(name)
    return ctx.tools[name]


def lc_tool_versions(ctx):
    out = {}
    for n in ("lean", "lake", "leanchecker"):
        p = lc_tool(ctx, n) if n != "lake" else shutil.which("lake")
        v = None
        if p and n != "leanchecker":
            rc, o, e = lc_run([p, "--version"], ctx.dir, timeout=60)
            v = ((o or e).strip().splitlines() or [None])[0]
        out[n] = {"found": p, "version": v}
    return out


def step_own_modules(ctx):
    t0, fails, det = time.time(), [], {}
    mods = [m for m, _ in ctx.modules]
    det["modules"] = mods
    allow = set(getattr(ctx.a, "allow_axiom", None) or [])
    ctx.allowed_decls = []
    scan = lc_scan_sources(ctx.dir, ctx.modules, allow, ctx.allowed_decls)
    det["source_scan"] = scan
    det["allowed_axiom_declarations"] = ctx.allowed_decls
    for r in scan:
        fails.append(f"{r['file']}:{r['line']}: {r['token']}")
    kind = "own_code" if scan else None
    if not mods:
        fails.append("no Lean module of the project's own libraries was found (lakefile.toml [[lean_lib]] roots)")
        kind = kind or "own_code"
        return _step(3, "fail", t0, fails, kind, **det)
    lake = shutil.which("lake")
    if not lake:
        fails.append("lake was not found on PATH: the project's own modules cannot be built")
        return _step(3, "fail", t0, fails, "tool_missing", **det)
    env = dict(os.environ, MATHLIB_NO_CACHE_ON_UPDATE="1")
    own_roots = {m.split(".")[0] for m in mods}
    proc = subprocess.Popen([lake, "build"] + (getattr(ctx.a, "target", None) or []), cwd=ctx.dir, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, errors="replace", env=env, stdin=subprocess.DEVNULL)
    lines, rebuilt = [], []
    for line in proc.stdout:
        lines.append(line.rstrip("\n"))
        m = LAKE_BUILD_LINE.search(line)
        if m and m.group(2).split(".")[0].split(":")[0] not in own_roots and m.group(2) not in rebuilt:
            rebuilt.append(m.group(2))
            proc.kill()
            break
    proc.wait()
    det["lake_exit"] = proc.returncode
    det["lake_output_lines"] = len(lines)
    if rebuilt:
        fails.append(f"Lake began compiling {rebuilt[0]}, which is not one of the project's own modules: the installed build does not "
                     "match what Lake expects (`mreg ci` restores it); stopped, nothing was compiled from a dependency")
        det["dependency_rebuild"] = rebuilt
        return _step(3, "fail", t0, fails, "own_code", **det)
    sorries = []
    for line in lines:
        m = LEAN_MSG.match(line)
        if m and re.search(r"uses ['`]?sorry", m.group("msg")):
            sorries.append({"file": m.group("file"), "line": int(m.group("line")), "message": m.group("msg")})
    det["sorry_warnings"] = sorries
    for r in sorries:
        fails.append(f"{r['file']}:{r['line']}: {r['message']}")
    if sorries:
        kind = "own_code"
    if proc.returncode != 0:
        errs = [l for l in lines if l.startswith("error")][:20]
        fails.append(f"lake build failed (exit {proc.returncode})" + ("".join("\n  " + e for e in errs)))
        kind = "own_code"
        det["lake_errors"] = errs
    ctx.built = proc.returncode == 0
    return _step(3, "fail" if fails else "pass", t0, fails, kind, **det)


# ---- steps 5 and 7: one Lean run over the own modules (axioms of each theorem, its statement, the constants it uses)

def lc_collect(ctx):
    """Run COLLECT_LEAN once; cached. Returns (records, error message or None)."""
    if getattr(ctx, "_collect", None) is not None:
        return ctx._collect
    lean = lc_tool(ctx, "lean")
    if not lean:
        ctx._collect = ([], "lean was not found: the axioms and statements of the own theorems cannot be computed")
        return ctx._collect
    sdir = os.path.join(ctx.dir, ".lake", "mreg-check")
    os.makedirs(sdir, exist_ok=True)
    script = os.path.join(sdir, "Collect.lean")
    atomic_write_text(script, COLLECT_LEAN)
    mods = [m for m, _ in ctx.modules]
    theorems = list(getattr(ctx.a, "theorem", None) or [])
    env = dict(os.environ, LEAN_PATH=lc_lean_env(ctx))
    rc, out, err = lc_run([lean, "--run", script, ",".join(mods), ",".join(theorems)], ctx.dir, env=env, timeout=3600)
    recs = []
    for line in out.splitlines():
        line = line.strip()
        if line.startswith("{"):
            try:
                recs.append(json.loads(line))
            except ValueError:
                pass
    if rc != 0:
        ctx._collect = (recs, f"the Lean script exited {rc}: {(err or out).strip().splitlines()[-1][:300] if (err or out).strip() else 'no output'}")
    else:
        ctx._collect = (recs, None)
    return ctx._collect


def step_axioms(ctx):
    t0, fails, det = time.time(), [], {}
    if not ctx.built:
        return _step(5, "not_run", t0, [], None, reason="the own modules were not built (step 3 did not pass), so there is nothing to import")
    recs, err = lc_collect(ctx)
    if err:
        return _step(5, "fail", t0, [err], "tool_missing" if "not found" in err else "error", **det)
    allowed = set(ACCEPTED_AXIOMS) | set(getattr(ctx.a, "allow_axiom", None) or [])
    thms, bad = [], []
    for r in recs:
        if r.get("missing"):
            fails.append(f"theorem {r['name']} was named with --theorem but is not a theorem of the project's own modules")
            continue
        extra = [x for x in r.get("axioms", []) if x not in allowed]
        stored = r.get("axioms_stored")
        differs = stored is not None and sorted(stored) != sorted(r.get("axioms", []))
        thms.append({"name": r["name"], "module": r.get("module"), "axioms": r.get("axioms", []), "axioms_stored": stored,
                     "outside_accepted": extra, "stored_list_differs": differs})
        if extra:
            bad.append(r["name"])
            fails.append(f"{r['name']} depends on " + ", ".join(extra))
        if differs:
            bad.append(r["name"])
            fails.append(f"{r['name']}: the axiom list stored in the compiled files ({', '.join(stored) or 'none'}) differs from the axioms its proofs "
                         f"use ({', '.join(r.get('axioms', [])) or 'none'}): a changed or stale compiled file")
    det["step_complete"] = bool(thms)
    if not thms and not fails:
        det["incomplete_reason"] = "no theorem of the own modules was checked (0 theorems in the targets)"
    det.update({"theorems": len(thms), "accepted": list(ACCEPTED_AXIOMS), "allowed_extra": sorted(set(getattr(ctx.a, "allow_axiom", None) or [])),
                "per_theorem": thms})
    return _step(5, "fail" if fails else "pass", t0, fails, "axiom_not_allowed" if bad else "error" if fails else None, **det)


def lc_module_package(ctx, module):
    """Package (Lake name) a module belongs to: by the file under each package's build directory; the project itself for its own."""
    root = read_manifest(ctx.dir) or {}
    rel = module.replace(".", os.sep) + ".olean"
    bl = os.path.join(".lake", "build", "lib", "lean")
    if os.path.exists(os.path.join(ctx.dir, bl, rel)):
        return root.get("name") or "(project)"
    for p in root.get("packages", []):
        if os.path.exists(os.path.join(package_dir(ctx.dir, root, p["name"]), bl, rel)):
            return p["name"]
    if module.split(".")[0] in ("Init", "Std", "Lean", "Lake"):
        return "(toolchain)"
    if module.startswith("Mreg."):
        return "(chunks)"
    return None


def step_statements(ctx):
    t0 = time.time()
    if not ctx.built:
        return _step(7, "not_run", t0, [], None, reason="the own modules were not built (step 3 did not pass)", sentence=STATEMENT_SENTENCE)
    recs, err = lc_collect(ctx)
    if err:
        return _step(7, "fail", t0, [err], "tool_missing" if "not found" in err else "error", sentence=STATEMENT_SENTENCE)
    labels = {}
    for r in ctx.audit_rows:
        labels[r["id"]] = r["labels"]
    lake_to_id = {e["lake_name"]: e["id"] for e in lc_lock_packages(ctx)}
    out = []
    for r in recs:
        if r.get("missing"):
            continue
        uses = []
        for u in r.get("uses", []):
            pkg = lc_module_package(ctx, u["module"]) if u.get("module") else None
            pid = lake_to_id.get(pkg)
            uses.append({"name": u["name"], "kind": u["kind"], "module": u["module"], "package": pkg, "package_id": pid,
                         "labels": labels.get(pid, []) if pid else []})
        out.append({"name": r["name"], "module": r.get("module"), "statement": r.get("statement"),
                    "statement_form": r.get("statement_form"), "uses": uses})
    return _step(7, "pass", t0, [], None, theorems=out, sentence=STATEMENT_SENTENCE, step_complete=bool(out),
                 **({} if out else {"incomplete_reason": "no theorem of the own modules was printed (0 theorems in the targets)"}))


# ---- the command

def lc_dep_groups(ctx):
    """[{key, label, id, modules, baseline}] the dependency packages that are installed, with the modules that are installed."""
    groups = []
    if ctx.has_state:
        proj = Project(ctx.dir)
        state = load_state(proj)
        ids = {e["lake_name"]: e for e in lc_lock_packages(ctx)}
        for name, st in sorted(state["packages"].items()):
            e = ids.get(name, {})
            pid = st.get("id") or e.get("id") or name
            groups.append({"key": pid, "lake_name": name, "id": pid, "modules": sorted(st.get("modules", [])),
                           "baseline": pid.startswith(BASELINE_PREFIX), "version": st.get("version"), "build_key": st.get("build_key")})
    if ctx.chunk_lock:
        groups.append({"key": "chunks", "lake_name": None, "id": "chunks", "baseline": True, "version": None,
                       "modules": [chunk_module(c["id"]) for c in ctx.chunk_lock.get("chunks", [])], "build_key": ctx.chunk_lock.get("build")})
    return groups


def lc_trust_basis(ctx, g):
    """The statement of what a package that is NOT replayed rests on (text), plus the sample-recompile figures when the build records them."""
    row = next((r for r in ctx.audit_rows if r["id"] == g["id"]), None)
    labels = (row or {}).get("labels") or []
    label = "/".join(labels) if labels else "none"
    if g["id"] == "chunks":
        if ctx.chunk_admission:
            return {"text": "Step 1 validated the signed kernel-declaration receipt, its source builds and the selected dependency closure.",
                    "label": "verified-declarations", "sample_recompile": None}
        if ctx.chunk_lock and ctx.chunk_lock.get("receipt_sha256"):
            return {"text": "Step 1 could not validate the signed declaration receipt.", "label": None, "sample_recompile": None}
        return {"text": "unverified experimental chunks: not replayed here, and no registry gate (axiom audit, kernel replay, second kernel) has checked them; "
                        "step 1 only shows the bytes equal the store's index", "label": None, "sample_recompile": None}
    txt = LC_NOT_REPLAYED.format(label=label)
    sample = None
    if "imported" in labels:
        n_s = n_t = None
        try:
            base = f"/v1/blobs/{g['id']}/-/{g['version']}/{g['build_key']}/"
            man = json.loads(ctx.registry().get(base + "manifest.json"))
            sr = man.get("sample_recompile") or {}
            n_s, n_t = sr.get("modules_sampled"), sr.get("modules_total")
        except (SystemExit, ValueError, OSError):
            pass
        if n_s is not None and n_t is not None:
            sample = {"modules_sampled": n_s, "modules_total": n_t}
            txt += f"; sample recompile {n_s} of {n_t} modules"
        else:
            txt += "; sample size not recorded"
    return {"text": txt, "label": label, "sample_recompile": sample}


def lc_replay_plan(ctx):
    """Which modules step 4 replays and which packages it does not, with the reason for each."""
    a = ctx.a
    want = set(getattr(a, "replay", None) or [])
    full = bool(getattr(a, "full_replay", False))
    own = [m for m, _ in ctx.modules]
    groups = lc_dep_groups(ctx)
    plan, skipped = [{"package": "(own modules)", "modules": own, "why": "the project's own modules"}], []
    for g in groups:
        est = len(g["modules"]) * replay_seconds_per_module()
        names = {g["id"], g.get("lake_name"), g["key"]}
        if full:
            why = "--full-replay"
        elif names & want:
            why = "--replay"
        elif not g["baseline"] and est < REPLAY_THRESHOLD_S:
            why = f"estimated {est:.0f} s is under {REPLAY_THRESHOLD_S} s and it is not a baseline (leanprover-community) package"
        else:
            reason = "baseline" if g["baseline"] else f"over threshold (estimated {est:.0f} s, limit {REPLAY_THRESHOLD_S} s)"
            skipped.append({"package": g["id"], "modules": len(g["modules"]), "reason": reason if not g["baseline"] else "baseline: not replayed unless requested (--replay or --full-replay)",
                            "reason_kind": "baseline" if g["baseline"] else "over_threshold", "estimated_seconds": round(est),
                            "trust_basis": lc_trust_basis(ctx, g)})
            continue
        plan.append({"package": g["id"], "modules": g["modules"], "why": why})
    for w in want:
        if not any(w in {g["id"], g.get("lake_name"), g["key"]} for g in groups):
            raise NIError("error", f"--replay {w}: no installed package or group with that name")
    return plan, skipped


def step_replay(ctx):
    t0 = time.time()
    if not ctx.built:
        return _step(4, "not_run", t0, [], None, reason="the own modules were not built (step 3 did not pass)", sentence=PUBLIC_OLEAN_SENTENCE)
    plan, skipped = lc_replay_plan(ctx)
    total = sum(len(p["modules"]) for p in plan)
    est = sum(len(p["modules"]) for p in plan if p["package"] != "(own modules)") * replay_seconds_per_module()
    ctx.log(f"step 4: kernel replay of {total} modules ({len(plan[0]['modules'])} own); estimated {est:.0f} s for the dependency modules "
            f"({replay_seconds_per_module()} s per module: {REPLAY_FIGURE_SOURCE})")
    checker = lc_tool(ctx, "leanchecker")
    det = {"estimate": {"seconds_per_module": replay_seconds_per_module(), "source": REPLAY_FIGURE_SOURCE, "dependency_modules_estimated_seconds": round(est)},
           "replayed": [{"package": p["package"], "why": p["why"], "modules": p["modules"]} for p in plan],
           "not_replayed": skipped, "checker": checker, "sentence": PUBLIC_OLEAN_SENTENCE}
    if not checker:
        return _step(4, "fail", t0, ["leanchecker was not found in the project's toolchain"], "tool_missing", **det)
    env = dict(os.environ, LEAN_PATH=lc_lean_env(ctx))
    fails = []
    for p in plan:
        mods = p["modules"]
        for i in range(0, len(mods), REPLAY_BATCH):
            batch = mods[i:i + REPLAY_BATCH]
            rc, out, err = lc_run([checker] + batch, ctx.dir, env=env, timeout=None)
            if rc != 0:
                msg = ((err or "") + (out or "")).strip().splitlines()
                prob = [l for l in msg if "found a problem" in l]
                killed = rc in (-9, -15, 137, 143) or (rc < 0 and not msg)
                fails.append(f"{p['package']}: leanchecker exit {rc}: " + (prob[0] if prob else (msg[-1][:300] if msg else "no output"))
                             + ("; the process was killed (out of memory?): lower MREG_REPLAY_BATCH (modules per process, now %d; 55 Mathlib modules at once and 16 at once were killed on a 24 GB machine, 4 passed)" % REPLAY_BATCH if killed else ""))
    return _step(4, "fail" if fails else "pass", t0, fails, "replay_failed" if fails else None, **det)


def lc_steps_wanted(a):
    if getattr(a, "fast", False):
        return list(FAST_STEPS)
    return [1, 2, 3, 4, 5, 6, 7]


def cmd_check_run(a):
    ctx = CheckCtx(a)
    if not (ctx.has_state or ctx.chunk_lock) and not os.path.exists(os.path.join(ctx.dir, "lakefile.toml")) and not os.path.exists(os.path.join(ctx.dir, "lakefile.lean")):
        raise NIError("error", f"{ctx.dir} is not a Lake project (no lakefile.toml or lakefile.lean)")
    want = lc_steps_wanted(a)
    runners = {1: step_integrity, 2: step_one_train, 3: step_own_modules, 4: step_replay, 5: step_axioms, 7: step_statements}
    steps = []
    for n in range(1, 8):
        if n not in want:
            steps.append({"step": n, "name": STEP_NAMES[n], "verdict": "not_run", "seconds": 0, "failures": [], "failure_kind": None,
                          "details": {"reason": "--fast runs steps 1, 2, 3 and 5 only"}})
            continue
        if n == 6:
            steps.append({"step": 6, "name": STEP_NAMES[6], "verdict": "not_run", "seconds": 0, "failures": [], "failure_kind": None,
                          "details": {"reason": "a second kernel (nanoda) is not part of phase A"}})
            continue
        ctx.log(f"step {n} ({STEP_NAMES[n]}) ...")
        try:
            st = runners[n](ctx)
        except SystemExit as e:
            if isinstance(e.code, str):
                err = _die_to_error(e)
                st = _step(n, "fail", time.time(), [err.message], err.kind)
            else:
                raise
        except NIError as e:
            st = _step(n, "fail", time.time(), [e.message], e.kind)
        steps.append(st)
        ctx.log(f"step {n} ({STEP_NAMES[n]}): {st['verdict'].upper()} in {st['seconds']} s" + "".join("\n    - " + _printable(f) for f in st["failures"][:30]))
    failed = [s for s in steps if s["verdict"] == "fail"]
    code = EXIT[failed[0]["failure_kind"] or "error"] if failed else 0
    tc = toolchain_state(ctx.dir, (next((s["details"].get("train_toolchain") for s in steps if s["step"] == 2), None)) or "")
    rep = next((s for s in steps if s["step"] == 4), {})
    doc = {"schema": LC_SCHEMAS["check"], "ok": not failed, "command": "check", "exit_code": code, "mreg_version": VERSION,
           "complete": False,
           "project": {"dir": ctx.dir, "own_modules": [m for m, _ in ctx.modules]},
           "train": {"name": ctx.train, "from": ctx.train_from}, "toolchain": tc,
           "lock_sha256": {"mreg.lock": sha256_file(os.path.join(ctx.dir, "mreg.lock")) if os.path.exists(os.path.join(ctx.dir, "mreg.lock")) else None,
                           CHUNK_LOCK: sha256_file(os.path.join(ctx.dir, CHUNK_LOCK)) if os.path.exists(os.path.join(ctx.dir, CHUNK_LOCK)) else None,
                           "lake-manifest.json": sha256_file(os.path.join(ctx.dir, "lake-manifest.json")) if os.path.exists(os.path.join(ctx.dir, "lake-manifest.json")) else None},
           "tools": lc_tool_versions(ctx) if any(s["verdict"] != "not_run" for s in steps if s["step"] in (3, 4, 5, 7)) else {},
           "mode": {"fast": bool(getattr(a, "fast", False)), "full_replay": bool(getattr(a, "full_replay", False)),
                    "replay": list(getattr(a, "replay", None) or []), "theorems": list(getattr(a, "theorem", None) or []),
                    "allow_axiom": list(getattr(a, "allow_axiom", None) or [])},
           "steps": steps, "sentences": {"public_olean": PUBLIC_OLEAN_SENTENCE, "statements": STATEMENT_SENTENCE},
           "seconds": round(time.time() - ctx.t0, 2)}
    used = {x for s in steps if s["step"] == 5 for t in s["details"].get("per_theorem", []) for x in t["axioms"]}
    allowed_names = sorted(({d["name"] for d in getattr(ctx, "allowed_decls", [])} | used) & set(getattr(a, "allow_axiom", None) or []))
    doc["allowed_axioms"] = allowed_names
    reasons = []
    if getattr(a, "fast", False):
        reasons.append("--fast: steps 4 and 7 were not run")
    if ctx.chunk_lock and not ctx.chunk_lock.get("receipt_sha256"):
        reasons.append("this project has declaration chunks: they are unverified experimental, and no registry gate, replay or axiom audit covers them")
    for s in steps:
        if s["step"] in (5, 7) and s["verdict"] == "pass" and not s["complete"]:
            reasons.append(f"step {s['step']} ({s['name']}): " + (s["details"].get("incomplete_reason") or "incomplete"))
    doc["incomplete_reasons"] = reasons
    doc["complete"] = not failed and not reasons and all(s["verdict"] == "pass" for s in steps if s["step"] != 6)
    lines = [f"mreg check {VERSION}: {ctx.dir}", f"train {ctx.train} ({ctx.train_from}); lean-toolchain {tc['project']}"]
    for s in steps:
        lines.append(f"  step {s['step']} {s['name']:<14} {s['verdict'].upper():<8} {s['seconds']} s"
                     + (f"  ({s['details'].get('reason')})" if s["verdict"] == "not_run" and s["details"].get("reason") else ""))
    for s in steps:
        if s["step"] == 4 and s["details"].get("not_replayed"):
            for n in s["details"]["not_replayed"]:
                lines.append(f"  not replayed: {n['package']} ({n['modules']} modules, {n['reason']}): {n['trust_basis']['text']}")
        if s["step"] == 7 and s["verdict"] == "pass":
            for t in s["details"].get("theorems", []):
                lines.append(f"  statement {t['name']} ({t['module']}): {t['statement']}")
                for u in t["uses"]:
                    lines.append(f"      uses {u['name']} [{u['kind']}] in {u['module']}" + (f" ({u['package_id'] or u['package']}" + (f", label {'/'.join(u['labels'])}" if u['labels'] else "") + ")" if u['package'] else ""))
    if allowed_names:
        lines.append("allowed by --allow-axiom: " + ", ".join(allowed_names))
    lines.append(PUBLIC_OLEAN_SENTENCE)
    lines.append(STATEMENT_SENTENCE)
    lines.append(("check FAILED (exit %d): " % code + "; ".join(f"step {s['step']} {s['name']}" for s in failed)) if failed else
                 ("check passed" + ((" but INCOMPLETE (complete=false): " + "; ".join(reasons)) if reasons else "; step 6 (second kernel) was not run")))
    if getattr(a, "json", False):
        print(json.dumps(doc, indent=1))
        for l in lines:
            print(_printable(l), file=sys.stderr)
    else:
        for l in lines:
            print(_printable(l))
    return code


def cmd_check(a):
    sys.exit(lc_guard("check", a, lambda: cmd_check_run(a)))


# ---------------------------------------------------------------- info, why, search (read commands)

DEFAULT_RECORD_MB = 32


def lc_reg_size(reg, path):
    """Size in bytes of a registry object without reading it (HEAD for https, stat for file://), or None when unknown."""
    try:
        if reg.kind == "file":
            return os.path.getsize(os.path.join(reg.root, *[x for x in path.split("/") if x]))
        if reg.kind == "http":
            req = urllib.request.Request(reg.base + path, method="HEAD", headers={"x-mreg-token": reg.tok, "User-Agent": "mreg/" + VERSION})
            with _safe_redirect_open(req, timeout=60) as r:
                n = r.headers.get("Content-Length")
                return int(n) if n and n.isdigit() else None
    except (OSError, ValueError, urllib.error.URLError):
        return None
    return None


def lc_train_doc(reg, train):
    td = reg.json(f"/v1/index/trains/{train}.json", missing_ok=True)
    if td is None:
        raise NIError("not_on_train", f"the registry has no train {train}")
    return td


def lc_build_on_train(reg, td, pid):
    """(package record of the train, package document, build entry, manifest dict, build base path) for pid on the train."""
    p = (td.get("packages") or {}).get(pid)
    if p is None:
        doc = reg.json(f"/v1/index/{pid}.json", missing_ok=True)
        on = sorted({t for v in ((doc or {}).get("versions") or {}).values() for b in v.get("builds", []) for t in b.get("trains", [])})
        raise NIError("not_on_train", f"{pid} is not on train {td['train']}" + (f"; the registry has it on: {', '.join(on)}" if on else
                      ("" if doc else "; the registry does not hold it")), package=pid, trains=on)
    doc = reg.json(f"/v1/index/{pid}.json", missing_ok=True)
    if doc is None:
        raise NIError("missing_object", f"{pid} is on the train but has no package document")
    builds = (doc["versions"].get(p["version"]) or {}).get("builds") or []
    b = next((x for x in builds if td["train"] in (x.get("trains") or [])), builds[0] if builds else None)
    if b is None:
        raise NIError("missing_object", f"{pid} {p['version']}: the registry has no build")
    base = f"/v1/blobs/{pid}/-/{p['version']}/{b['build_key']}/"
    raw = reg.get(base + "manifest.json")
    if sha256(raw) != b["manifest"]["sha256"]:
        raise NIError("hash_mismatch", f"{pid}: manifest SHA-256 differs from the package document's")
    return p, doc, b, json.loads(raw), base


def lc_report(reg, man, base, rel, cap_mb):
    """(bytes or None, status): a report file of a build, hash-checked against the manifest, cached in the store. status: ok, no_record, too_large."""
    want = (man.get("reports") or {}).get(rel)
    if not want:
        return None, "no_record"
    cache = os.path.join(Store().root, "reports", want)
    if os.path.exists(cache) and sha256_file(cache) == want:
        return read_file_retry(cache), "ok"
    size = lc_reg_size(reg, base + rel)
    if size is not None and size > cap_mb * 1e6:
        return None, f"too_large ({size / 1e6:.1f} MB > {cap_mb} MB; --max-record-mb)"
    raw = reg.get(base + rel, missing_ok=True)
    if raw is None:
        return None, "no_record"
    if sha256(raw) != want:
        raise NIError("hash_mismatch", f"{rel} does not match the manifest's SHA-256; refused")
    try:
        os.makedirs(os.path.dirname(cache), exist_ok=True)
        atomic_write(cache, raw)
    except OSError:
        pass
    return raw, "ok"


def lc_statement_row(raw, name):
    needles = {json.dumps(name)[1:-1], json.dumps(name, ensure_ascii=False)[1:-1]}
    for line in raw.decode("utf-8", "replace").splitlines():
        if any(n in line for n in needles):
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if isinstance(r, dict) and r.get("name") == name:
                return r
    return None


def lc_axioms_row(raw, name):
    try:
        j = json.loads(raw)
    except ValueError:
        return None
    for r in j.get("rows", []):
        if r and r[0] == name:
            return {"name": r[0], "module": r[1], "kind": r[2], "axioms": j["axiom_sets"][r[3]]}
    return None


def lc_index_open(train):
    """(Lookup, pointer, meta) of the train's declaration index, hash-matched; NIError not_on_train when the registry serves none."""
    f, store = Fetcher(), Store()
    ptr = read_pointer(f, train)
    idir, meta, _ = ensure_index(f, store, train, ptr["build"], ptr["index_sha256"])
    return Lookup(idir), ptr, meta


def lc_cone_of(lk, variant, hexchunk_index):
    cone = lk.cone([hexchunk_index])
    nb = ns = 0
    for i in cone:
        m = lk.manifest(variant, lk.chunk_hex(i))
        if m:
            nb += m["bytes_stored"]
    return {"chunks": len(cone), "bytes_stored": nb}


def lc_pkg_summary(doc, td, pid):
    out = {"id": doc.get("id") or pid, "lake_name": doc.get("lake_name"), "license": (doc.get("license") or {}).get("spdx"),
           "dist_tags": doc.get("dist_tags"), "versions": []}
    for v, e in (doc.get("versions") or {}).items():
        out["versions"].append({"version": v, "commit": e.get("commit"), "builds": [
            {"build_key": b.get("build_key"), "trains": b.get("trains"), "labels": b.get("labels") or [], "signed": bool(b.get("signed")),
             "gates": b.get("gates"), "modules": b.get("modules"), "bytes_compressed": b.get("bytes_compressed"), "kind": b.get("kind")}
            for b in e.get("builds", [])]})
    return out


def info_run(a):
    d = os.path.abspath(a.dir)
    train = a.train or lc_project_train(d)[0]
    target = a.target.strip()
    reg = Registry()
    td = lc_train_doc(reg, train)
    pd = parse_decl(target)
    notes = []
    cap = a.max_record_mb
    payload = {"schema": LC_SCHEMAS["info"], "ok": True, "command": "info", "train": train, "target": target}
    lines = []
    if pd is None and re.match(r"^[^/\s#]+/[^\s#]+$", target):         # a package
        pid = target
        p, doc, b, man, base = lc_build_on_train(reg, td, pid)
        s = lc_pkg_summary(doc, td, pid)
        payload.update({"kind": "package", "package": s, "on_train": {"version": p["version"], "commit": p.get("commit"), "modules": p.get("modules"),
                                                                      "module_roots": p.get("module_roots"), "build_key": b["build_key"],
                                                                      "labels": b.get("labels") or [], "gates": b.get("gates"), "signed": bool(b.get("signed")),
                                                                      "trains": b.get("trains")}})
        c_tc, d_tc = declared_toolchain(b, man)
        payload["on_train"]["compiled_toolchain"], payload["on_train"]["declared_toolchain"] = (c_tc, d_tc) if d_tc else (b.get("toolchain"), None)
        lock = next((e for e in lc_lock_packages_dir(d) if e["id"] == pid), None)
        payload["installed"] = None if lock is None else {"version": lock["version"], "build_key": lock["build_key"]}
        lines += [f"{pid} {p['version']}  train {train}  {p.get('modules')} modules  labels {','.join(b.get('labels') or []) or '-'}  "
                  + ("signed" if b.get("signed") else "unsigned") + f"  build {b['build_key']}",
                  "  gates: " + " ".join(f"{k}:{v}" for k, v in sorted((b.get("gates") or {}).items(), key=lambda kv: int(kv[0][1:])) if v != "not run"),
                  "  on trains: " + ", ".join(sorted({t for v in s['versions'] for bb in v['builds'] for t in (bb['trains'] or [])})),
                  "  installed here: " + ("no" if lock is None else f"{lock['version']} (build {lock['build_key']})")]
        if "imported" in (b.get("labels") or []):
            lines.append("  note: " + IMPORTED_MEANING)
        if d_tc:
            lines.append("  " + declared_line(c_tc, d_tc))
    elif pd is not None:                                                  # a declaration
        pid, name = pd
        p, doc, b, man, base = lc_build_on_train(reg, td, pid)
        rec = {"name": name, "package": pid, "version": p["version"], "build_key": b["build_key"], "labels": b.get("labels") or [],
               "gates": b.get("gates"), "signed": bool(b.get("signed")), "trains": b.get("trains")}
        kind = module = chunk = cone = None
        try:
            lk, ptr, meta = lc_index_open(train)
            try:
                tdd = {"packages": td.get("packages")}
                r = resolve_entry(lk, td, target)
                kind, module, chunk = r["kind"], r["module"], r["chunk"]
                rec["exact_name"], rec["in_toolchain"] = r["exact_name"], r["in_toolchain"]
                if not r["in_toolchain"]:
                    cone = lc_cone_of(lk, "checking", r["chunk_index"])
                rec["index_build"] = ptr["build"]
            finally:
                lk.close()
        except NIError as e:
            if e.kind in ("unknown_declaration", "ambiguous_name"):
                raise
            notes.append(f"declaration index: {e.kind}: {e.message}")
        rec["kind"], rec["module"], rec["chunk"], rec["cone"] = kind, module, chunk, cone
        c_tc, d_tc = declared_toolchain(b, man)
        rec["compiled_toolchain"], rec["declared_toolchain"] = (c_tc, d_tc) if d_tc else (b.get("toolchain"), None)
        stmt = ax = None
        raw, st_s = lc_report(reg, man, base, "reports/statements.jsonl", cap)
        rec["statement_status"] = st_s
        if raw is not None:
            row = lc_statement_row(raw, name)
            if row:
                stmt = row.get("statement")
                kind = kind or row.get("kind")
                module = module or row.get("module")
                rec["kind"], rec["module"] = kind, module
                rec["statement_sha256"] = row.get("sha256")
        raw, ax_s = lc_report(reg, man, base, "reports/axioms.json", cap)
        rec["axioms_status"] = ax_s
        if raw is not None:
            row = lc_axioms_row(raw, name)
            ax = None if row is None else row["axioms"]
            if row:
                rec["kind"] = rec["kind"] or row["kind"]
        rec["statement"], rec["axioms"] = stmt, ax
        if kind is None and stmt is None and ax is None and cone is None:
            raise NIError("unknown_declaration", f"{target}: no declaration {name!r} found for {pid} on train {train} (index and build records)")
        trains = sorted({t for v in (doc.get("versions") or {}).values() for bb in v.get("builds", []) for t in (bb.get("trains") or [])})
        rec["on_trains"] = trains
        payload.update({"kind": "declaration", "declaration": rec})
        lines += [f"{target}: {rec['kind'] or '?'} in {rec['module'] or '?'}  ({pid} {p['version']}, train {train})",
                  "  statement: " + (stmt if stmt is not None else f"not available ({st_s})"),
                  "  axioms: " + (", ".join(ax) if ax else ("none" if ax is not None else f"not available ({ax_s})")),
                  f"  labels: {','.join(rec['labels']) or '-'}  gates: " + " ".join(f"{k}:{v}" for k, v in sorted((b.get('gates') or {}).items(), key=lambda kv: int(kv[0][1:])) if v != 'not run'),
                  "  on trains: " + ", ".join(trains)] + (["  " + declared_line(c_tc, d_tc)] if d_tc else []) + [
                  "  cone: " + (f"{cone['chunks']} chunks, {human_bytes(cone['bytes_stored'])} stored" if cone else "not available")]
    else:                                                                 # a module
        root = target.split(".")[0]
        pid = (td.get("module_roots") or {}).get(root)
        if pid is None:
            raise NIError("unknown_declaration", f"{target}: no package on train {train} has the module root {root!r}")
        p, doc, b, man, base = lc_build_on_train(reg, td, pid)
        mods = lc_load_modules(reg, man, base)
        if target not in mods:
            raise NIError("unknown_declaration", f"{target}: not a module of {pid} {p['version']} on train {train}")
        closure_mods, pkgs = lc_module_closure(reg, td, target, pid, mods, notes)
        payload.update({"kind": "module", "module": {"name": target, "package": pid, "version": p["version"], "build_key": b["build_key"],
                                                     "labels": b.get("labels") or [], "gates": b.get("gates"), "imports": mods[target],
                                                     "closure_modules": len(closure_mods), "closure_packages": sorted(pkgs), "trains": b.get("trains")}})
        lines += [f"{target}: module of {pid} {p['version']} (train {train}), labels {','.join(b.get('labels') or []) or '-'}",
                  f"  imports {len(mods[target] or [])} modules directly; whole-file import closure: {len(closure_mods)} modules in {len(pkgs)} packages ({', '.join(sorted(pkgs))})"]
        c_tc, d_tc = declared_toolchain(b, man)
        payload["module"]["compiled_toolchain"], payload["module"]["declared_toolchain"] = (c_tc, d_tc) if d_tc else (b.get("toolchain"), None)
        if d_tc:
            lines.append("  " + declared_line(c_tc, d_tc))
    payload["notes"] = notes
    lines += [f"note: {n}" for n in notes]
    if a.json:
        print(json.dumps(payload, indent=1))
        for l in lines:
            print(_printable(l), file=sys.stderr)
    else:
        for l in lines:
            print(_printable(l))
    return 0


def lc_lock_packages_dir(d):
    lk = _read_json(os.path.join(d, "mreg.lock")) or {}
    return [e for e in (lk.get("packages") or []) if e.get("from") == "registry"]


def lc_load_modules(reg, man, base):
    """{module: imports list or None} from a build's shards/modules.jsonl[.zst], hash-checked against the manifest."""
    aux = man.get("aux_files") or {}
    rel = "shards/modules.jsonl"
    if rel + ".zst" in aux:
        raw = reg.get(base + rel + ".zst")
        if sha256(raw) != aux[rel + ".zst"]["sha256"]:
            raise NIError("hash_mismatch", f"{rel}.zst does not match the manifest")
        text = unzstd(raw).decode("utf-8")
    else:
        raw = reg.get(base + rel)
        if rel not in aux or sha256(raw) != aux[rel]["sha256"]:
            raise NIError("hash_mismatch", f"{rel} does not match the manifest")
        text = raw.decode("utf-8")
    out = {}
    for l in text.splitlines():
        if l.strip():
            e = json.loads(l)
            out[e["module"]] = e["imports"]
    return out


def lc_module_closure(reg, td, module, pid, mods, notes):
    """Whole-file import closure of a module over the train's packages: (set of modules, set of package ids). Toolchain modules are leaves."""
    cache = {pid: mods}
    owner_of_root = td.get("module_roots") or {}

    def graph(p):
        if p not in cache:
            _, _, _, man, base = lc_build_on_train(reg, td, p)
            cache[p] = lc_load_modules(reg, man, base)
        return cache[p]
    seen, todo, pkgs = set(), [module], set()
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        p = owner_of_root.get(m.split(".")[0])
        if p is None:
            continue
        pkgs.add(p)
        g = graph(p)
        if m not in g:
            notes.append(f"{m} is not in the manifest of {p}")
            continue
        todo += g[m] or []
    return {m for m in seen if owner_of_root.get(m.split(".")[0])}, pkgs


def cmd_info(a):
    sys.exit(lc_guard("info", a, lambda: info_run(a)))


# ---- why

def why_run(a):
    d = os.path.abspath(a.dir)
    train = a.train or lc_project_train(d)[0]
    target = a.target.strip()
    own = lc_own_modules(d)
    if not own:
        raise NIError("error", f"{d} has no Lean modules of its own libraries (lakefile.toml [[lean_lib]] roots)")
    notes, graph, pkg_of = [], {}, {}
    own_names = [m for m, _ in own]
    for m, p in own:
        graph[m] = parse_imports(p)
        pkg_of[m] = "(project)"
    lock = _read_json(os.path.join(d, "mreg.lock"))
    cl = _read_json(os.path.join(d, CHUNK_LOCK))
    if lock is None and cl is None:
        raise NIError("error", f"nothing installed: no mreg.lock and no {CHUNK_LOCK} in {d}")
    reg = Registry() if lock else None
    for e in lc_lock_packages_dir(d):
        raw = reg.get(f"/v1/blobs/{e['id']}/-/{e['version']}/{e['build_key']}/manifest.json")
        if sha256(raw) != e["manifest_sha256"]:
            raise NIError("hash_mismatch", f"{e['id']}: manifest SHA-256 differs from the lock's")
        man = json.loads(raw)
        mods = lc_load_modules(reg, man, f"/v1/blobs/{e['id']}/-/{e['version']}/{e['build_key']}/")
        for m, imps in mods.items():
            graph[m] = imps or []
            pkg_of[m] = e["id"]
    declared = None
    if cl:
        by_chunk = {x["chunk"]: x for x in cl.get("declarations", []) if x.get("chunk")}
        for x in cl.get("declarations", []):
            if x.get("chunk"):
                cm = chunk_module(x["chunk"])
                graph[cm] = []
                pkg_of[cm] = "(chunks)"
        entry = (load_cfg(d).get("chunks") or {}).get("entry") or "MregChunks.lean"
        notes.append("chunk-level declarations: the path goes from the generated entry file to the declaration's chunk; chunks inside a cone are not expanded")
    # the target: a module, else a declaration
    pd = parse_decl(target)
    target_mod, resolved = None, None
    if target in graph or any(target in v for v in graph.values()):
        target_mod = target
    else:
        name = pd[1] if pd else target
        try:
            lk, ptr, _ = lc_index_open(train)
            try:
                rows = lk.find(name)
            finally:
                lk.close()
        except NIError as e:
            raise NIError(e.kind, f"{target}: not a module of the project's closure and the declaration index cannot resolve it: {e.message}")
        rows = [r for r in rows if not r["in_toolchain"]] or rows
        if not rows:
            raise NIError("unknown_declaration", f"{target}: neither a module in the project's closure nor a declaration in train {train}'s index")
        if len({r["exact_name"] for r in rows}) > 1:
            raise NIError("ambiguous_name", f"{target}: several declarations have this name: " + "; ".join(f"{r['exact_name']} in {r['module']}" for r in rows))
        target_mod = rows[0]["module"]
        resolved = {"declaration": rows[0]["exact_name"], "module": target_mod}
        if cl:
            ch = next((x for x in cl.get("declarations", []) if x.get("name") == name or x.get("exact_name") == name), None)
            if ch and ch.get("chunk"):
                target_mod = chunk_module(ch["chunk"])
    # breadth-first search from every own module, all shortest paths
    from collections import deque
    dist, preds, q = {m: 0 for m in own_names}, {m: [] for m in own_names}, deque(own_names)
    if cl:
        for m in own_names:           # an own file that imports the generated entry's chunk modules reaches them directly
            pass
    while q:
        u = q.popleft()
        for v in graph.get(u, []) or []:
            if v not in dist:
                dist[v] = dist[u] + 1; preds[v] = [u]; q.append(v)
            elif dist[v] == dist[u] + 1:
                preds[v].append(u)
    if target_mod not in dist:
        raise NIError("not_in_project", f"{target} ({target_mod}) is not imported, directly or indirectly, by any of the project's {len(own_names)} own modules", own_modules=len(own_names))
    paths = []

    def walk(m, tail):
        if len(paths) >= a.max_paths:
            return
        if not preds[m]:
            paths.append([m] + tail)
            return
        for p in preds[m]:
            walk(p, [m] + tail)
    walk(target_mod, [])
    shown = [[{"module": m, "package": pkg_of.get(m) or "(toolchain)" if m.split(".")[0] in ("Init", "Std", "Lean", "Lake") and m not in pkg_of else pkg_of.get(m)} for m in p] for p in paths]
    payload = {"schema": LC_SCHEMAS["why"], "ok": True, "command": "why", "train": train, "target": target, "resolved": resolved,
               "target_module": target_mod, "found": True, "distance": dist[target_mod], "paths": shown,
               "own_modules": len(own_names), "graph_modules": len(graph), "notes": notes}
    lines = [f"{target} -> module {target_mod}; reached from {len(own_names)} own modules at distance {dist[target_mod]}"]
    for i, p in enumerate(shown, 1):
        lines.append(f"  path {i}: " + " -> ".join(f"{x['module']} [{x['package']}]" for x in p))
    lines += [f"note: {n}" for n in notes]
    if a.json:
        print(json.dumps(payload, indent=1))
        for l in lines:
            print(_printable(l), file=sys.stderr)
    else:
        for l in lines:
            print(_printable(l))
    return 0


def cmd_why(a):
    sys.exit(lc_guard("why", a, lambda: why_run(a)))


# ---- search

def search_run(a):
    d = os.path.abspath(a.dir)
    train = a.train or lc_project_train(d)[0]
    text = " ".join(a.text).strip()
    if not text:
        raise NIError("error", "search: give some text")
    toks = [t for t in re.split(r"\s+", text) if t]
    reg = Registry()
    td = lc_train_doc(reg, train)
    results, notes = [], []
    lim = a.limit
    cov = {"names": None, "statements": []}
    owner_of_root = td.get("module_roots") or {}
    # names, from the declaration index of the train
    try:
        lk, ptr, meta = lc_index_open(train)
        try:
            cond = " AND ".join("d.name LIKE ? ESCAPE '\\'" for _ in toks)
            args = ["%" + t.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_") + "%" for t in toks]
            q = ("SELECT d.name, m.name, k.name, d.tc FROM decl d JOIN modules m ON m.id=d.mod JOIN kinds k ON k.id=d.kind WHERE " + cond +
                 " ORDER BY length(d.name), d.name LIMIT ?")
            rows = lk.db.execute(q, args + [lim + 1]).fetchall()
            cov["names"] = {"index_build": ptr["build"], "declarations": meta.get("lookup", {}).get("declarations") if isinstance(meta, dict) else None}
            for n, mod, kind, tc in rows:
                results.append({"name": n, "kind": kind, "module": mod, "package": owner_of_root.get(mod.split(".")[0]) or ("toolchain" if tc else None),
                                "match": "name", "statement": None})
        finally:
            lk.close()
    except NIError as e:
        if e.kind in ("auth", "network"):
            raise
        notes.append(f"names: the declaration index is not available ({e.kind}: {e.message})")
    # statements, from the build records of the packages on the train that have one within the size limit
    if not a.names_only:
        want_pk = set(a.in_pkg or [])
        for pid in sorted((td.get("packages") or {})):
            if want_pk and pid not in want_pk:
                continue
            try:
                p, doc, b, man, base = lc_build_on_train(reg, td, pid)
                raw, st = lc_report(reg, man, base, "reports/statements.jsonl", a.max_record_mb if not want_pk else max(a.max_record_mb, 1000))
            except NIError as e:
                cov["statements"].append({"package": pid, "status": f"{e.kind}: {e.message}"})
                continue
            cov["statements"].append({"package": pid, "status": "scanned" if raw is not None else st})
            if raw is None:
                continue
            low = [t.lower() for t in toks]
            for line in raw.decode("utf-8", "replace").splitlines():
                ll = line.lower()
                if all(t in ll for t in low):
                    try:
                        r = json.loads(line)
                    except ValueError:
                        continue
                    stmt = r.get("statement") or ""
                    if all(t in stmt.lower() or t in (r.get("name") or "").lower() for t in low):
                        if not any(x["name"] == r.get("name") for x in results):
                            results.append({"name": r.get("name"), "kind": r.get("kind"), "module": r.get("module"), "package": pid,
                                            "match": "statement", "statement": stmt})
                        else:
                            for x in results:
                                if x["name"] == r.get("name") and x["statement"] is None:
                                    x["statement"] = stmt
                if len(results) > 4 * lim:
                    break
    truncated = len(results) > lim
    results = results[:lim]
    payload = {"schema": LC_SCHEMAS["search"], "ok": True, "command": "search", "train": train, "query": text, "results": results,
               "truncated": truncated, "coverage": cov, "notes": notes}
    lines = [f"search {text!r} on train {train}: {len(results)} result(s)" + (" (more exist; --limit)" if truncated else "")]
    for r in results:
        lines.append(f"  {r['name']} [{r['kind']}] {r['module']} ({r['package']}) matched by {r['match']}" + (f"\n      {r['statement']}" if r["statement"] else ""))
    sc = cov["statements"]
    if sc:
        lines.append("  statements scanned: " + ", ".join(f"{s['package']}: {s['status']}" for s in sc))
    lines += [f"note: {n}" for n in notes]
    if a.json:
        print(json.dumps(payload, indent=1))
        for l in lines:
            print(_printable(l), file=sys.stderr)
    else:
        for l in lines:
            print(_printable(l))
    return 0


def cmd_search(a):
    sys.exit(lc_guard("search", a, lambda: search_run(a)))


def _main(argv=None):
    ap = argparse.ArgumentParser(prog="mreg", description="client of the mathregistry.com registry (v%s)" % VERSION)
    ap.add_argument("-C", dest="dir", default=".", help="project directory (default: here)")
    sp = ap.add_subparsers(dest="cmd", required=True)
    p = sp.add_parser("install"); p.add_argument("modules", nargs="*", help="modules, or owner/pkg#Decl.name declarations"); p.add_argument("--all", action="store_true")
    ni_flags(p, install=True)
    p.add_argument("--dry-run", action="store_true"); p.add_argument("--check", action="store_true")
    p.add_argument("--rehash", action="store_true", help="(default now; kept for old scripts)")
    p.add_argument("--no-rehash", action="store_true", help="final check: plain `lake build --no-build`, which trusts trace files")
    p.add_argument("--train", help="train whose pins the project is measured against (default: newest with this toolchain)")
    p.add_argument("--allow-source", action="store_true",
                   help="leave a train-held dependency with no registry build to Lake instead of refusing")
    p.add_argument("--skip-root", action="store_true",
                   help="do not install the project's own package (builders: it is compiled here, so its registry build is not fetched)")
    p.add_argument("--any-platform", action="store_true")
    p.add_argument("--accept-new-key", action="store_true", help="trust a signing key not pinned for this registry yet")
    p.add_argument("--no-lake-check", action="store_true", help="skip the final `lake build --no-build` (tests without Lean)")
    p.add_argument("--require-views", action="store_true", help="also require the build's verified views check (contract 1.2.0) to have status pass")
    p = sp.add_parser("ci"); ni_flags(p, ci=True); p.add_argument("--rehash", action="store_true"); p.add_argument("--no-rehash", action="store_true")
    p.add_argument("--train", help="the train the project is on (default: the recorded one, else the baseline); builds of another train are refused")
    p.add_argument("--accept-new-key", action="store_true"); p.add_argument("--no-lake-check", action="store_true")
    p.add_argument("--require-views", action="store_true", help="also require the build's verified views check (contract 1.2.0) to have status pass")
    p = sp.add_parser("audit"); p.add_argument("target", nargs="?", help="<id>[@<version>]; default: the lock file's packages")
    p.add_argument("--strict", action="store_true", help="require every gate the promotion rules require (the default; see AUDIT_STRICT_DEFAULT)")
    p.add_argument("--lenient", action="store_true", help="the old behaviour: gates not run or flagged are not failures (prints a warning)")
    p.add_argument("--require", default="", help="comma-separated gates that must be pass, e.g. G6,G8")
    p.add_argument("--require-views", action="store_true", help="also require the build's verified views check (contract 1.2.0) to have status pass")
    p.add_argument("--json", action="store_true"); p.add_argument("--accept-new-key", action="store_true")
    p = sp.add_parser("verify"); p.add_argument("--json", action="store_true")
    p = sp.add_parser("resolve", help="declaration -> chunk and cone, no download"); p.add_argument("entries", nargs="+"); p.add_argument("--train")
    ni_flags(p)
    p = sp.add_parser("env", help="the LEAN_PATH setting for the installed chunks"); p.add_argument("--json", action="store_true")
    p = sp.add_parser("index", help="fetch the declaration index of a train's build, match its hashes to the pointer; print where it is")
    p.add_argument("--train"); p.add_argument("--build"); p.add_argument("--json", action="store_true")
    p.add_argument("--variant", choices=VARIANTS, help="variant whose packed tables are fetched too (default checking)")
    p.add_argument("--no-packed", action="store_true", help="do not fetch the packed tables")
    p = sp.add_parser("doctor", help="check this machine and the registry connection; prints no key")
    p.add_argument("--json", action="store_true"); p.add_argument("--train", default=DOCTOR_PROBE_TRAIN, help=argparse.SUPPRESS)
    p = sp.add_parser("view"); p.add_argument("id"); p.add_argument("--json", action="store_true", help="one JSON document on stdout (schema mreg-view/1)")
    p = sp.add_parser("train"); p.add_argument("train", nargs="?"); p.add_argument("--json", action="store_true", help="one JSON document on stdout (schema mreg-train/1)")
    p = sp.add_parser("init"); p.add_argument("dir"); p.add_argument("--train"); p.add_argument("--name"); p.add_argument("--json", action="store_true", help="one JSON document on stdout (schema mreg-init/1)")
    p = sp.add_parser("add"); p.add_argument("ids", nargs="+", help="<owner/pkg> or <owner/pkg>#<Decl.name>"); p.add_argument("--train"); ni_flags(p, install=True); p.add_argument("--dry-run", action="store_true", help="resolve and report only (declarations)")
    p.add_argument("--no-lake-update", action="store_true", help="edit the lakefile and mreg.json only (tests without Lean)")
    p = sp.add_parser("login", help="sign in in the browser and store a per-user API key")
    p.add_argument("--provider", type=str.lower, choices=sorted(PROVIDERS), help="skip the provider choice on the sign-in page")
    p.add_argument("--label", help="label of the key (1-64 characters; default: 'mreg on <this machine>')")
    p.add_argument("--no-browser", action="store_true", help="print the sign-in address instead of opening a browser")
    p.add_argument("--timeout", type=float, default=300.0, help="seconds to wait for the sign-in (default 300)")
    p.add_argument("--json", action="store_true", help="one JSON document on stdout (schema mreg-login/1); the text goes to stderr")
    p = sp.add_parser("logout", help="delete the stored key (--revoke also revokes it at the service)")
    p.add_argument("--revoke", action="store_true", help="sign in again and revoke the stored key at the key service")
    p.add_argument("--no-browser", action="store_true"); p.add_argument("--timeout", type=float, default=300.0)
    p.add_argument("--json", action="store_true", help="one JSON document on stdout (schema mreg-logout/1)")
    p = sp.add_parser("whoami", help="what kind of key is stored (decoded locally, nothing secret printed)")
    p.add_argument("--json", action="store_true", help="one JSON document on stdout (schema mreg-whoami/1)")
    # ---- phase A: the user's lifecycle
    p = sp.add_parser("check", help="is this project valid? integrity, one train, own modules, kernel replay, axioms, statements")
    p.add_argument("--fast", action="store_true", help="steps 1, 2, 3 and 5 only (no kernel replay, no statements)")
    p.add_argument("--full-replay", action="store_true", help="replay every installed module of every package (prints a time estimate first; whole Mathlib takes hours)")
    p.add_argument("--replay", action="append", metavar="PKG", help="also replay this dependency package's installed modules (id, Lake name, or `chunks`); repeatable")
    p.add_argument("--theorem", action="append", metavar="NAME", help="check the axioms of only this theorem of the own modules; repeatable")
    p.add_argument("--allow-axiom", action="append", metavar="NAME", help="an axiom (beyond propext, Classical.choice, Quot.sound) that is accepted; repeatable")
    p.add_argument("--train", help="the project's train (default: the recorded one, else the baseline)")
    p.add_argument("--accept-new-key", action="store_true"); p.add_argument("--json", action="store_true", help="one JSON document on stdout (schema mreg-check/1)")
    p = sp.add_parser("info", help="what the registry knows about a package, a declaration (owner/pkg#Decl) or a module")
    p.add_argument("target", help="owner/pkg, owner/pkg#Decl.name or Module.Name"); p.add_argument("--train", help="train to read (default: the project's, else the baseline)")
    p.add_argument("--max-record-mb", type=float, default=DEFAULT_RECORD_MB, help="largest build record (statements, axioms) to download (default %d MB)" % DEFAULT_RECORD_MB)
    p.add_argument("--json", action="store_true", help="one JSON document on stdout (schema mreg-info/1)")
    p = sp.add_parser("why", help="the import path from the project's own modules to a module or declaration")
    p.add_argument("target", help="Module.Name, a declaration name, or owner/pkg#Decl.name"); p.add_argument("--train")
    p.add_argument("--max-paths", type=int, default=3, help="shortest paths to print (default 3)")
    p.add_argument("--json", action="store_true", help="one JSON document on stdout (schema mreg-why/1)")
    p = sp.add_parser("search", help="declarations of the train by name and by statement text")
    p.add_argument("text", nargs="+"); p.add_argument("--train"); p.add_argument("--limit", type=int, default=20, help="results to show (default 20)")
    p.add_argument("--names-only", action="store_true", help="search declaration names only (the index); no statement records are read")
    p.add_argument("--in", dest="in_pkg", action="append", metavar="PKG", help="scan the statements of this package only (repeatable; lifts the size limit)")
    p.add_argument("--max-record-mb", type=float, default=DEFAULT_RECORD_MB, help="largest statement record to download (default %d MB)" % DEFAULT_RECORD_MB)
    p.add_argument("--json", action="store_true", help="one JSON document on stdout (schema mreg-search/1)")
    a = ap.parse_args(argv)
    table = {"install": cmd_install, "ci": cmd_ci, "verify": cmd_verify, "view": cmd_view, "train": cmd_train,
             "init": cmd_init, "add": cmd_add, "audit": cmd_audit, "login": cmd_login, "logout": cmd_logout,
             "whoami": cmd_whoami, "doctor": lambda a: sys.exit(cmd_doctor(a)), "resolve": cmd_resolve, "env": cmd_env, "index": cmd_index,
             "check": cmd_check, "info": cmd_info, "why": cmd_why, "search": cmd_search}
    if a.cmd in JSON_WRAPPED and getattr(a, "json", False):
        run_json_wrapped(a, a.cmd, lambda: table[a.cmd](a), extra=lambda: dict(_json_data.get(a.cmd) or {}))
    table[a.cmd](a)


def main(argv=None):
    """Entry point. Refuses a key on the command line, then runs with stdout and stderr (and the text of a SystemExit or an
    unexpected exception) passed through `scrub`."""
    refuse_credential_in_args(sys.argv[1:] if argv is None else list(argv))
    real_out, real_err = sys.stdout, sys.stderr
    sys.stdout, sys.stderr = _ScrubWriter(real_out), _ScrubWriter(real_err)
    try:
        _main(argv)
    except SystemExit as e:
        if isinstance(e.code, str):
            raise SystemExit(scrub(e.code)) from None
        raise
    except (KeyboardInterrupt, BrokenPipeError):
        raise
    except Exception as e:
        print(f"mreg: unexpected error: {type(e).__name__}: {e}", file=sys.stderr)
        if os.environ.get("MREG_DEBUG"):
            import traceback
            print(traceback.format_exc(), file=sys.stderr)
        raise SystemExit(1) from None
    finally:
        try:
            sys.stdout.flush()
            sys.stderr.flush()
        except Exception:
            pass
        sys.stdout, sys.stderr = real_out, real_err


if __name__ == "__main__":
    main()
