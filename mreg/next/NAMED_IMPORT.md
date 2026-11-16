# Named import: `mreg add owner/pkg#Decl.name`

The declaration-level import path of the `mreg` client (`mreg/next/mreg.py`, version 0.4.0). Plan section 2a. The unit a consumer
names is the declaration; the client fetches only the compiled chunks that declaration's check depends on. No Lean runs in the
client. Tests: `test_named_import.py` (stdlib, no network, no Lean). Status: built against the FINAL store layout (2026-11-10, build
numbers, three pinned index files, `in_toolchain` column) and tested against a local mirror in that layout and against the real
Lean 4.34.1 tables mapped to the final columns inside the test; **not run against a real registry** (build `b1` is not uploaded yet;
the end-to-end harness in `e2e/` is the test for that).

**What a chunk bundle is for (field `supports`, in every JSON document and as the last line of every human output):**
kernel checking and reference to declarations by name. The variant `full` adds compiled code, reducibility, structure and projection
info, docstrings. Neither carries instances, simp sets, notation, parsers, macros or tactics, so chunks alone are not a base for
writing new proofs. The text is one constant (`SUPPORTS` in the client); nothing in the client suggests otherwise.

## 1. Serving layout (the client's contract)

Final, agreed with the chunk-store team, 2026-11-10 (keys carry a build number and are never overwritten):

    <registry>/x/decl/<train>/current.json                                pointer, short cache
    <registry>/x/decl/<train>/<build>/checking/X<2 hex>/C<32 hex id>.olean.zst
    <registry>/x/decl/<train>/<build>/full/X<2 hex>/C<32 hex id>.olean.zst
    <registry>/x/decl/<train>/<build>/index/assignment.tsv.gz             name, exact_name, module, kind, in_toolchain, chunk
    <registry>/x/decl/<train>/<build>/index/chunk_edges.tsv.gz            chunk, imports_chunk
    <registry>/x/decl/<train>/<build>/index/manifest.tsv.gz               variant, key, id, sha256_raw, bytes_raw, sha256_stored, bytes_stored, n_decls

`current.json`: `{"schema":"mreg-decl-store/1","train":"lean-4.35.0","build":"b1","variants":["checking","full"],"manifest_sha256":"...",
"index_sha256":{"assignment.tsv.gz":"...","chunk_edges.tsv.gz":"...","manifest.tsv.gz":"..."},"published_at":"<UTC>"}`. All hashes are sha256 of
the files as stored. `manifest_sha256` stays for compatibility and must equal `index_sha256["manifest.tsv.gz"]` (else exit 19).
Everything under `<build>/` is immutable. Each object is one zstd frame of the raw `.olean`. Ids are name-based and valid only under
their train (the client never deduplicates across trains or builds by id). Registry token: `x-mreg-token`, same as the rest of the
registry (https needs one; `file://` mirrors do not).

Columns. The client reads these by NAME (extra columns are ignored, a missing one is exit 19). `chunk` and `imports_chunk` are 32 lower-case hex
digits; `id` in the manifest equals `chunk`; `key` is informative (the canonical layout above is the rule: the client builds paths itself).
Rows with `in_toolchain=1` (declarations of `Init`, `Std`, `Lean`, `Lake`) have an EMPTY `chunk` and never appear in the edge table; a chunk
imports those modules by their ordinary names and the installed toolchain provides them. A declaration that is a later copy of a name an
earlier module already defines points at the first owner's chunk. Any other value (`in_toolchain` not 0/1, `in_toolchain=1` with a chunk,
`in_toolchain=0` without one, a short row, an edge endpoint the assignment does not know) makes the whole index unusable: exit 19, nothing cached.

What the client does, in this order, before any chunk is requested:

1. Fetch the pointer (every command that resolves; one small request). Missing: exit 12 (the registry serves no declaration store
   for the train; `add`/`install` may then fall back to the module-level path). Present but unusable (not JSON, wrong schema, no sha256
   for each of the three index files, manifest hashes disagree): exit 19, no fallback.
2. Fetch the train document and compare its `toolchain` with the project's `lean-toolchain` (section 5, exit 20).
3. Fetch the three index files, check EACH against the pointer's hash as it arrives (exit 14 on a difference, 18 if a file is gone) and cache
   them only when all three match. The cache `index/<train>/<build>/` is keyed by (train, build), is re-checked against the hashes in
   hand each time it is used, and is never revalidated against the network (a build is immutable).
4. Resolve names, take the cone, count the chunk requests it needs, and apply the request budget (section 5, exit 21).
5. Fetch the missing chunks, verify, install, write the lock.

The lock records the build, the toolchain and the hashes of all three index files; `ci` restores from the LOCKED build, never from the
pointer (it does not even read it); if that build is gone, `ci` fails with exit 18. A project never holds chunks of two builds: `add` on a
locked project stays on the locked build (and says the pointer moved); if the pointer names the SAME build with different index hashes the
client refuses (exit 14: builds are immutable); `--build` naming another build is a forbidden mix (15); `mreg install --upgrade-build` is
the explicit move (clears the chunk directory, re-resolves every recorded declaration against the pointer's build, rewrites the lock).

## 2. Commands

All accept `--json` (section 4) and `-C DIR` (project directory, default `.`).

| command | does |
|---|---|
| `mreg resolve owner/pkg#Decl.name ... [--train T] [--variant V]` | resolve and print the cone (counts, bytes from the manifest, how many chunks the local store lacks, the budget, the toolchain match). Writes only the local index cache. Never refused for toolchain or budget: it reports them. |
| `mreg add owner/pkg#Decl.name ...` | resolve, fetch the missing chunks, install, write `mreg-chunks.lock.json`, `mreg.json` (`chunks.declarations`) and the entry file. Adds **no** `[[require]]` and touches no Lake file. `--dry-run` = `resolve` for these names. A refusal edits nothing. |
| `mreg install owner/pkg#Decl.name ...` | the same without recording in `mreg.json`. With no argument: the declarations recorded in `mreg.json`. `--upgrade-build` as above. `--dry-run` as for `add`. |
| `mreg ci [--chunks-only]` | restore exactly the chunks `mreg-chunks.lock.json` lists, from the locked build, verifying each; extra chunk files in the chunk directory are removed. Checks the locked toolchain and the request budget. If a module-level `mreg.lock` also exists, the module-level `ci` runs afterwards. |
| `mreg verify` | re-hash every installed chunk against the lock (exit 14 on a difference or a missing file). |
| `mreg env` | print the `LEAN_PATH` entry and the entry file. |
| `mreg index [--train T] [--build B]` | make sure the verified index of the train's current build is in the local cache and say where it is (`index_dir`): for tools that read the assignment table themselves (the harness). |

Flags of `resolve`, `add`, `install`: `--variant checking|full` (default `checking`; one per project), `--train T` (default: the project's
`mreg.json`/lock, else the registry's newest), `--build B`, `--chunk-dir DIR` (relative to the project; default
`.lake/mreg-chunks/<train>`), `--entry FILE` (default `MregChunks.lean`) / `--no-entry`, `--jobs N` (default 16), `--quiet`,
`--chunks` (require the declaration-level store), `--module-level` (the older module-level path), `--max-requests N` (default 2000) and
`--allow-over-budget` (also on `ci`).

`mreg add owner/pkg#Decl` uses the declaration-level store when the registry serves one for the train (the pointer exists); otherwise it
falls back to the module-level behaviour of 0.2.0 (graph in the build's `reports/`, module-level install). A project that
already has a chunk lock never falls back. The module-level answer for an unknown name also names the build whose graph it came from
(package version, build key, manifest sha256) and says that is all it says.

An entry is `owner/pkg#Decl.name` with no whitespace. `Decl.name` is the display name (`name` column) or the exact name (`exact_name`
column, `%XX` escapes, e.g. `Mathlib.weird.x%20y`). Resolution is by the train's tables: the package must be on the train and own the
declaration's module root (`module_roots` of the train document); a name that exists under another package is refused with the name to
use (`other/pkg#Decl`). Rows with the same exact name AND the same chunk (a later copy points at the first owner's chunk) are one declaration
(a note says so); a display name shared by declarations with different exact names or different chunks is ambiguous (11, with candidates).

A name defined only by the toolchain (`in_toolchain=1`, for example `Nat.add_comm`) is not a chunk: the result says
`provided by the toolchain; nothing to fetch`, `requested[].provided_by` is `"toolchain"`, `chunk` is null, the cone is empty, nothing is
requested, exit 0. The package in the entry must still be on the train, but the toolchain does not belong to it. If the same name is also a
declaration of the named package's own modules, that one wins.

## 3. What is stored where

- Local content-addressed store: `$MREG_STORE`, default `~/.mreg/store`. `objects/<aa>/<sha256 of the stored bytes>` (the verified `.zst`
  frames; reused across projects, trains and builds without ambiguity because the key is a content hash), `index/<train>/<build>/` (the
  three tables as fetched, `READY.json`, and the compact lookup: `decl.sqlite` names, `manifest.sqlite`, `ids.bin`, `off.bin`, `tgt.bin`
  as a CSR graph).
- Project chunk directory: `<chunk dir>/Mreg/X<2 hex>/C<id>.olean` (module `Mreg.X<2 hex>.C<id>`) and `<chunk dir>/.mreg-chunks.json`
  (`{"schema":"mreg-chunk-dir/1","train","build","variant"}`).
- Lock `mreg-chunks.lock.json`, schema `mreg-chunks-lock/1`, deterministic (no timestamps): `registry`, `train`, `build`, `variant`,
  `toolchain` (the train's; absent in locks of 0.2.0, which skip the check), `manifest_sha256`, `published_at`, `index` (sha256 of the three
  tables, all required for `ci`), `chunk_dir`, `covers_packages` (lake names of the train's packages: the mix check), `declarations`
  (`entry`, `package`, `name`, `exact_name`, `module`, `kind`, `chunk` (null for the toolchain)), `counts`, `bytes` (raw, stored), `chunks`
  (sorted by id: `id`, `sha256_raw`, `bytes_raw`, `sha256_stored`, `bytes_stored`).
- `mreg.json`: `chunks` = `{train, build, variant, dir, entry, declarations}`.

Verification. Each object: length and sha256 of the stored bytes against the manifest, then decompress, length and sha256 of the raw bytes
against the manifest; only then written (temporary file, then rename). A mismatch writes nothing of that object, stops the run (exit 14),
and nothing is installed or locked. Install re-verifies the raw hash from the store, so a damaged store object is caught too. Fetch is
resumable by construction: every verified object is in the store, a rerun requests only the rest.

Resolution without Lean. The assignment gives declaration -> chunk (`chunk` column, no guessing among column names). The cone is the
transitive closure in the edge table. The graph holds no toolchain chunks. The cone of a declaration whose check needs only the toolchain is empty.

## 4. JSON output (`--json`), schema `mreg-named-import/1`

One JSON document on stdout; progress and notes go to stderr. Always: `schema` (`"mreg-named-import/1"`), `ok` (bool), `command`, and `supports`
(the fixed text above, also in failures).

Failure (`ok: false`, process exit code = `error.exit_code`): `error` = `{kind, exit_code, message, ...}` where `kind` is a name from the
table in section 5 and extra fields may appear (`chunk`, `candidates`, `suggestions`, `packages`, `build`, `toolchain`, and for exit 21
`cone_chunks`, `bytes_stored`, `bytes_raw`, `requests_needed`, `max_requests`). **An `unknown_declaration` (and `ambiguous_name`) error carries
`error.answered_from` = `{train, build, manifest_sha256, index_sha256: {assignment.tsv.gz, chunk_edges.tsv.gz, manifest.tsv.gz}}` and its
message names the train, the build and the assignment hash, and says the name may exist in another build or train** (plan A.7). It is only ever
produced from an index that matched the pointer's (or the lock's) hashes. If the pointer, an index file or the hash check is unavailable the
answer is an error with another code (12, 14, 16, 18 or 19), never `unknown_declaration`.

Success of `resolve`, `add`, `install` (and `ci`, which has no `would_fetch` field):

| field | meaning |
|---|---|
| `registry`, `train`, `build`, `variant` | what was used |
| `manifest_sha256`, `index_sha256` | the verified manifest hash of the build, and the sha256 of all three index files the answer was computed from |
| `supports` | the one fixed statement of what a bundle supports (see the top of this file) |
| `requested` | list; each: `entry`, `package`, `name`, `exact_name`, `module`, `kind`, `chunk` (32 hex or null), `in_toolchain`, `provided_by` (`"chunk"` or `"toolchain"`) |
| `cone` | `chunks` (to install), `bytes_raw`, `bytes_stored` (sums over the cone) |
| `toolchain` | `{project, train, match}`: the project's `lean-toolchain`, the train's, whether they are the same (`null` for `ci` on a 0.2.0 lock) |
| `budget` | `{max_requests, requests_needed, over_budget, allowed}`: `requests_needed` is the PLANNED request count: one per chunk the local store lacks, or, when the packed archives serve the fetch (section 8), one per planned range plus one per chunk that must come as its own file |
| `packed` | (client 0.4.0) `{available, used, error, reason, chunks_missing, ranges_planned, ranges, bytes_fetched, bytes_used, overfetch_ratio, fallback_chunks, fallback_ranges, fallback_reasons, non_206, non_206_kinds, fallbacks[]}`; `seconds_fetch` (top level) is the time of the fetch phase alone |
| `dry_run` | true for `resolve` and `--dry-run`; `would_fetch` then says how many chunks the store lacks |
| `notes` | list of strings (for example that the pointer moved to a newer build, or that the name appears in several modules) |
| `fetched` | chunks requested from the registry now |
| `reused` | chunks already in the local store (zero requests) |
| `installed` / `already_installed` | chunk files written / already identical in the chunk directory |
| `removed_extra` | (`ci`) chunk files removed that the lock does not list |
| `bytes_fetched` | bytes received for objects |
| `requests` | all requests this command made; `requests_index` = for the index (3 on a cold build, else 0); `requests_objects` = chunk requests. The pointer, the train document and, when no train is known, `trains.json` count in `requests` only |
| `seconds` | wall time |
| `lock` | path of the lock written (null when dry) |
| `chunk_dir`, `entry_file`, `lean_path` | where the chunks are, the generated import file (or null), the directory to put on `LEAN_PATH` |

`verify`: `train`, `build`, `variant`, `checked`, `mismatched` (ids), `missing` (ids), `extra` (ids), `chunk_dir`; `ok` false with exit 14.
`env`: `chunk_dir`, `lean_path`, `path_separator`, `entry_file`.
`index`: `registry`, `train`, `build`, `variants`, `published_at`, `manifest_sha256`, `index_sha256`, `index_dir` (the directory holding the
three verified tables), `fetched` (false when cached), `lookup` (counts), `requests`, `seconds`.

## 5. Exit codes

| code | kind | when |
|---|---|---|
| 0 | `ok` | done (including "provided by the toolchain; nothing to fetch") |
| 1 | `error` | anything else: bad arguments in an entry, malformed lock, a train document without a toolchain, a store the client does not support |
| 2 | (usage) | command line not understood (argparse) |
| 10 | `unknown_declaration` | no such declaration in this build's index, or it belongs to another package (the message names it); `error.answered_from` says which index; nothing is changed |
| 11 | `ambiguous_name` | several declarations share the display name; `error.candidates` lists exact names and chunks |
| 12 | `not_on_train` | package not on the train, no train document, no pointer (the registry serves no declaration store for the train), variant or `--build` not served |
| 13 | `auth` | no token, or the registry answered 403. If the response carries the optional header `x-mreg-denial` with `bad_signature`, `revoked` or `owner_blocked`, the message says which and the error carries `denial` and `http_status` (section 11); nothing is retried |
| 14 | `hash_mismatch` | an index file differs from the pointer's (or the lock's) hash; stored or decompressed bytes differ from the manifest; a damaged store or installed chunk; the pointer rewrote the index hashes of a locked build |
| 15 | `forbidden_mix` | original module files of a covered package and chunks; `checking` and `full`; two trains; two builds |
| 16 | `network` | the registry could not be reached or answered 5xx, or 429, after retries (`MREG_RETRIES`, default 3). A `Retry-After` on 429 or 503 sets the wait, at most 30 s (section 11) |
| 17 | `missing_object` | the manifest lists a chunk the registry does not serve (404) or a chunk of the cone is not in the manifest; also HTTP 451 (taken down): no retry, `error.http_status` is 451 (section 11) |
| 18 | `build_removed` | the build's objects or an index file are gone from the registry (also: an index file of the current build is absent) |
| 19 | `index_unavailable` | the pointer exists but is unusable (not JSON, wrong schema, no `index_sha256` for each of the three files, inconsistent), or an index file does not have the final columns or has a malformed row. No answer is computed; this is never "not found" |
| 4 | `unverified_refused` | admission (0.5.0): install or ci found a build that does not pass the registry's strict audit (unsigned, label, gates), or a declaration-chunk install/ci, which is experimental and unverified; nothing was installed. `--allow-unverified` installs it anyway with a banner and records it in the lock. (The existing `REFUSED_EXIT`; also the code of `install`'s train-pin refusal.) |
| 20 | `toolchain_mismatch` | the project's `lean-toolchain` is not the train's toolchain (or there is none); nothing was fetched or installed. `lean-toolchain` is compared after adding the default `leanprover/lean4:` prefix to a bare version. `resolve` and `--dry-run` report it instead (`toolchain.match`) |
| 21 | `over_budget` | the cone needs more chunk requests than `--max-requests` (default 2000) and `--allow-over-budget` was not given; nothing was fetched; the error carries `cone_chunks`, `bytes_stored`, `bytes_raw`, `requests_needed`, `max_requests` |
| 22 | `own_code` | `mreg check` step 3: a `sorry` warning, `admit`, `native_decide`, `decide +native`, `bv_decide`, `axiom` or `debug.skipKernelTC` in the project's own modules, a failed `lake build` of them, or Lake began compiling a dependency (Phase A, not a named-import code) |
| 23 | `replay_failed` | `mreg check` step 4: Lean's replay checker rejected a module (the report names it) |
| 24 | `axiom_not_allowed` | `mreg check` step 5: a theorem of the own modules depends on an axiom beyond `propext`, `Classical.choice`, `Quot.sound` (and `--allow-axiom`), or the axiom list stored in the compiled files differs from what its proofs use |
| 25 | `tool_missing` | `lean`, `lake` or `leanchecker` of the project's toolchain was not found (`mreg check`) |
| 26 | `not_in_project` | `mreg why`: the target is not imported, directly or indirectly, by any of the project's own modules |
| 130 | | interrupted; verified objects stay in the store, rerun to resume |

Environment: `MREG_REGISTRY` (https, http on localhost, or `file:///dir`), `MREG_TOKEN`, `MREG_STORE`, `MREG_RETRIES`, `MREG_BACKOFF`
(seconds, times attempt number), `MREG_TIMEOUT`.

Request budget. The cone size is known from the index before any chunk is requested. `requests_needed` is the planned request count: the number of cone chunks the
local store does not hold (one request each), or, with the packed archives (section 8), the planned ranges (at most 100 by default, so the default 2000 no longer refuses large imports). If it exceeds `--max-requests` the client stops with 21 and the figures above, so an agent can
decide; `--allow-over-budget` proceeds. The default 2000 is above the median cone of the old 4.34.1 measurements (about 370); 23.5 percent of random theorems have a larger
cone (section 7); the CDN allowance is 10 million requests a month for everybody. The index files and the pointer are not counted
against it (they are made first, and are 5 requests on a cold build).

## 6. How a Lean file uses it (from FOR_THE_REGISTRY.md and REPORT.md; nothing invented)

- The chunk that holds the named declaration imports its whole cone, so `import Mreg.X<2 hex>.C<id>` is the bundle, no generated bundle
  module is needed for one name. For several names the project needs a file that imports each top chunk. `mreg add` generates it
  (`MregChunks.lean`, one `import Mreg.X..C..` line per distinct declaration chunk, a comment for toolchain declarations, and the `supports`
  line) and never edits any other file.
- The chunk directory must be on Lean's search path: the measurements in REPORT.md and store/STORE.md ran plain `lean FILE` with
  `LEAN_PATH` set to the directory that holds `Mreg/`. `mreg env` prints that line. Chunks import `Init` and the unchanged toolchain
  modules (`Std`, `Lean`, `Lake`), so the project's Lean must be the train's (the client now refuses otherwise).
- One chunk directory per train, one variant per project. Chunk bundles and the original module files of the same packages never load in one
  process (FOR_THE_REGISTRY.md section 10): the client refuses both (exit 15) in the project.

Open questions (not decided here, nothing was assumed in code beyond what is marked):

1. **Lake.** Not tested anywhere: Lake building a downstream project whose imports resolve in a chunk directory, and whether Lake keeps an
   initial `LEAN_PATH` when it runs `lean`. The client only prints the path. `e2e/lake_probe/` holds the probe that answers it; to be run
   in WSL with the train's Lean once a chunk directory exists.
2. **Manifest `key` column.** The client ignores it; the canonical layout is the rule.
3. **`full` variant.** Instance, simp and notation entries are not in any chunk (FOR_THE_REGISTRY.md section 4): what must be installed beside
   `full` chunks to write proofs, and is it served? Today: nothing, and the client says so in `supports`.
4. **Request budget.** A cold import costs 1 request per chunk plus about 5. If the CDN allowance is the scarce quantity, a per-declaration cone
   bundle (one object per popular top chunk, or a range-readable pack) is the lever; the client's store and lock would not change.
5. **Names with whitespace** cannot be written as an entry (use the `%XX` exact name); acceptable?
6. Ids are 128-bit name hashes: the client cannot detect two different chunks with one id inside a build; only the manifest hashes.
7. **A.7 beyond the index.** "Unknown" is relative to one build's table. A `current.json` that moves to a new build changes answers; the
   answer names the build so a caller can tell. A name in no build of the train but defined in a package the train does not hold cannot be
   told apart from a typo (a statements-by-meaning search is plan A.2).
8. **Pointer freshness.** The pointer is short-cached (60 s); a client may see build `b1` for up to a minute after `b2` is published.
   Harmless (builds are immutable) and reported in `notes` once a lock exists.

## 8. Ranged archives ("packed"), client 0.4.0

Optional layer; absent it, everything above is unchanged. Built by `decl-chunks/archives/build_archives.py`, served under
`x/decl/<train>/<build>/packed/<variant>/`: `A0000.bin` ... (concatenated stored chunk frames, about 256 MiB each, layout `dfs.deepfirst/v1`),
`layout.tsv.gz` (`chunk, archive, offset, length, sha256_stored`), `archives.tsv` (`name, bytes, sha256`), `packed.json` (`mreg-decl-packed/1`:
train, build, variant, layout, algorithm_version, archive_count, chunk_count, manifest_sha256, layout_sha256, archives_sha256, policy
`{gap_floor: 16384, max_requests: 100}`). The pointer names it: `"packed": {"checking": {"path": "b1/packed/checking/", "packed_sha256": "<sha256 of packed.json>"}}`.

Client behaviour. `packed.json` is checked against the pointer's hash, the two tables against `packed.json`, `manifest_sha256` against the build's.
Then the missing chunks are sorted by (archive, offset); runs of adjacent chunks and gaps up to `gap_floor` are merged into one range, then the
smallest remaining gaps until at most `min(policy max_requests, --range-requests, --max-requests)` ranges (a range never crosses an archive).
Ranges go out as single `Range: bytes=a-b` requests (never reversed, empty, beyond the archive or suffix form) on 8 keep-alive connections.
A reply counts only as 206 with `Content-Range` equal to `bytes a-b/<archive size>`; a 200 is never read (it would be the whole archive). Each chunk is cut
out by its offset and checked against the MANIFEST (stored size and sha256, decompressed sha256) exactly like a per-chunk download; gap bytes are discarded
unverified. A 200, a Content-Range mismatch, a missing archive (404), a body that stays short after the retries, a 429/5xx that persists, or a chunk that fails
its hash sends that range's (or that chunk's) chunks to their own per-chunk files; each is counted in `packed.fallbacks`. A chunk whose layout row disagrees
with the manifest or lies outside its archive is fetched as a per-chunk file (`layout_mismatch`, `outside_archive`). If `packed` is absent, `--no-packed`
is given, or the tables fail verification (reported in `packed.error` and a note), the per-chunk path runs. With fewer than `--packed-min` (default 200) missing
chunks the 30-odd MB layout table is not downloaded unless cached (`mreg index` caches it). `ci` uses the `packed` entry recorded in the lock.


## 9. Which file wins: `mreg.lock`, `mreg-chunks.lock.json`, `lake-manifest.json`

Pinned by `test_baseline.py` (class `Precedence`). As the code applies them:

1. `lake-manifest.json` is the reference. A module-level `mreg.lock` is valid only for the manifest it was made for: `mreg ci` compares
   `sha256(lake-manifest.json)` with the lock's `lake_manifest_sha256` first and stops with "lake-manifest.json is not the one this lock
   was made for". Only after that match does it compare `lean-toolchain` with the lock's, then each package's checkout commit with the
   locked commit. The lock never overrides the manifest.
2. The two locks are independent files for two kinds of content: `mreg.lock` for module-level packages, `mreg-chunks.lock.json` for
   declaration chunks. `mreg ci` restores the chunk lock first. If that fails it exits with its code (13 to 21) and the module lock is
   not read. If it succeeds and `mreg.lock` exists, the module-level `ci` runs next; `--chunks-only` skips it. With no `mreg.lock`
   the chunk lock alone decides the exit code.
3. One package is never present twice. Original module files and chunks of the same package are refused with exit 15 (`forbidden_mix`),
   in both directions (module install over a chunk lock: `reverse_mix`; chunk install over module files: `check_mix`). The sources that count
   as "module files are here" are read in this order and the first one that names the package is the reason in the message:
   `lake-manifest.json`, `lakefile.toml` `[[require]]`, `.lake/mreg-state.json`, `mreg.lock`.

## 10. Concurrent use (client 0.4.0, T-C3)

Several mreg processes may use one store (`MREG_STORE`) at the same time. Pinned by `test_store_concurrency.py` (50 processes, at most 12
at once, one synthetic `file://` registry).

- Every file another process may read is written to a unique temporary name in the same directory (`<name>.part-<pid>-<thread>-<random>`),
  flushed, and renamed over the target with `os.replace` (atomic on POSIX and Windows; on Windows a refused rename is retried for up to about
  2 s). Covered: store objects, the shard cache, `mreg.lock`, `.lake/mreg-state.json`, `mreg-chunks.lock.json`, the entry file, `mreg.json`,
  the lakefile edit, `~/.mreg/keys.json` (pins, also under a lock because it is read-modify-write) and the token file.
- Installed chunk files inside one project directory are still written in place (a project is used by one mreg at a time; the
  measured cost of rename on Windows is in the docstring of `write_in_place`). Every reader re-checks size and hash, so a partial file
  is rewritten and never accepted.
- An index (`index/<train>/<build>/`) and a packed table directory are built by one process at a time: a lock file
  `<dir>.lock` created with `O_CREAT|O_EXCL` holding pid, host and time. The others wait (at most `MREG_LOCK_WAIT` seconds, default 120,
  then exit 1 with the lock path in the message), then find `READY.json` and use the finished directory.
- A lock whose process is dead (same host) or which is older than 900 s is taken over; a lock file nobody could finish writing is taken
  over after 5 s. `*.part-<pid>-*` files and directories of a dead process (older than 5 s), or older than an hour, are removed when an
  index is built; a leftover temporary object file is never read by anything.
- Not covered: two mreg processes installing into the SAME project directory at once.

## 11. Statuses (client 0.4.0, T-C4)

| response | what the client does |
|---|---|
| 451 | a takedown: no retry; exit 17 (`missing_object`, the existing code closest to "the registry no longer serves it"); `error.http_status` is 451; the message says it was taken down. It is never treated as "not found": no fallback to module level, no "build removed" rewrite |
| 403 (or 401, 405) with `x-mreg-denial: bad_signature`, `revoked` or `owner_blocked` | no retry; exit 13 (`auth`); the message names the reason; `error.denial` and `error.http_status` are set |
| 405 with `x-mreg-denial: method_not_allowed` | no retry; exit 1 (`error`); same extra fields |
| 403 without the header, or with a value not in the list | exactly as before the header existed (exit 13, "the token is missing, wrong or revoked", no extra fields) |
| 429 or 503 with `Retry-After` (seconds, or an HTTP date) | the wait before the next try is that value, at most **30 s** (`RETRY_AFTER_CAP`), instead of the backoff; the number of tries is unchanged (`MREG_RETRIES`); after the last, exit 16 |
| 429 or 503 without `Retry-After`, other 5xx | the backoff as before |

The header name is the constant `DENIAL_HEADER` (`x-mreg-denial`); it is not final and the edge does not send it yet. The legacy commands
(`view`, `train`, `install` by module) use the same rules and stop with exit 1 and the same message, because they have only that one exit code.
The extra fields `http_status` and `denial` are inside the `error` object of the `--json` document; section 4 already says extra fields may appear
there, and the test validator ignores unknown fields.
