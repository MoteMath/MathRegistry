# mreg 0.5.2, private beta: one page

You have a personal key for the private registry. `mreg.py` is one Python file with no packages to install. Check it first: its SHA-256 must equal the line for `mreg.py` in `SHA256SUMS.txt` that you were given with it (`sha256sum -c SHA256SUMS.txt`, or `certutil -hashfile mreg.py SHA256` on Windows).

## What you need

- Python 3.10 or newer, and `git`.
- zstd support: Python 3.14 (`compression.zstd`), or the `zstandard` module, or the `zstd` program on PATH.
- Lake and Lean 4.35.0 (through `elan`) to use what you install. `mreg view`, `train`, `audit`, `doctor` and `resolve` need neither.
- Windows: the client itself runs on native Windows Python, but the registry lists its builds as usable on `x86_64-unknown-linux-gnu` only, so on native Windows `mreg install` is refused ("a build exists but the registry does not list it as usable on x86_64-w64-windows-gnu") unless you pass `--any-platform`. That flag installs the listed build anyway; the compiled files are Linux files, so Lean and Lake themselves need Linux or WSL to use them.
- Network: `mreg add` makes Lake clone the dependency repositories from GitHub, so it needs access to GitHub as well as to the registry.
- Disk: installs go to `~/.mreg/store`. Large cones are big (below).

## Your key

A key looks like `mreg_...`. Put it in the environment variable `MREG_TOKEN`, or in the file `~/.mreg/token` (one line; `mreg login` signs you in in the browser and writes it for you, for invited accounts only). **Never put a key on a command line, in a flag, or in the registry address**: the client refuses any argument that begins with `mreg_`, and any address that contains a key, without printing it. The client never prints your key.

## First commands

    python mreg.py doctor      # your tools, zstd, key (judged by shape only), local store, for an https registry one request to it (an s3 registry is reported as not checked); prints no key
    python mreg.py train       # the packages of the newest train (Lean version and Mathlib commit)
    python mreg.py view leanprover-community/batteries
    python mreg.py whoami      # what kind of key is stored (decoded locally; prints nothing secret)

For a first walk through sign-in, key creation, audit, rotation and revocation, follow `FIRST_USER_STEPS.md` (same folder). `python mreg.py logout --revoke` signs you in again, revokes the stored key at the service and deletes the key file.

## Installing

By module (compiled files for the modules your project imports, and what they need):

    python mreg.py init myproj          # a Lake project pinned to the train's Lean version
    cd myproj
    python mreg.py add leanprover-community/mathlib4
    python mreg.py install Mathlib.Data.Nat.Basic

By named declaration (only the chunks that declaration needs):

    python mreg.py add leanprover-community/mathlib4#Nat.add_comm
    python mreg.py resolve leanprover-community/mathlib4#Nat.add_comm     # what it would fetch; nothing downloaded
    python mreg.py env                                                      # the LEAN_PATH setting for the installed chunks

`--dry-run` reports before it fetches. The client says the size first and stops above 2,000 requests unless you pass `--allow-over-budget`. `mreg ci` installs exactly what the lock file says and fails on any mismatch.

## What `mreg audit` tells you, and what it does not

Mathlib and its seven dependency packages are served as the registry's own gated, signed builds (label `clean`), promoted on 12 November 2026. The three AxiomMath packages are served unsigned and not gated. A strict audit says which is which on the day you run it; today the eight clean packages pass and the three AxiomMath packages fail as unsigned.

`mreg audit <package>` (or with no name, the packages in your `mreg.lock`) is **strict by default** (the registry's rule since 2026-11-12: it fails on an unsigned build or a gate that did not run). For each build it prints one line and, if the build fails, one `- ` line per reason (an unsigned build also prints `UNSIGNED: manifest.json.sig is missing`). Exit code 0 only if every build passes; 1 otherwise.

What each report means:

- `unsigned: no registry gate record`. The build has no registry signature and no promotion record: it has no registry gate record. An unsigned build may still show statuses for G3 and G5 (for example `[G3:pass G5:pass]` in `mreg view`); the earlier loader wrote those into the package document. They are not backed by a signed gate record, and strict `audit` reports the build as unsigned. The client still compared the files you downloaded with the SHA-256 the registry recorded for them, but those recorded hashes are unsigned. Exit 1. Today you should expect this on the three AxiomMath packages (ClusterAlgebras, RiemannJensen, Stacks); the eight others audit OK: `mreg view` shows `labels=-` and `unsigned: no registry gate record`, and a strict `mreg audit` prints `FAIL`, `UNSIGNED: manifest.json.sig is missing` and a `strict: unsigned: no registry gate record` line, then exits 1. That is the strict audit working, not a fault of your install.
- `labels=clean`. The build is signed, in the promotion log, and the gates G1 to G10 passed (the policy allows G9 not to run; the live eight all show it as pass) (the registry compiled it and checked it with Lean's replay and a second kernel). Exit 0.
- `labels=imported`. Files compiled elsewhere, gated here (G2 to G10), and a sample of modules recompiled here and found identical. The registry did not compile all of them. It is not `clean`. Exit 0 if the signature, log and gates are consistent.
- `partial`, `flagged` or no label, a gate `not run`, `flag`, `fail` or missing where the label needs `pass`, or a signature or log that does not agree with the build: reported as `strict:` lines, exit 1.

What a passing audit checks: that the registry's signature, its reports and its log agree with each other and with the build's manifest. It is not a check of any proof. Importing a compiled file does not re-check its proofs. A passing label does not show that a theorem states what its name suggests. The authoritative text is the registry's page "What is and is not guaranteed" (`guarantees`): a hash match shows that bytes equal what the registry recorded; a build that is unsigned has no registry gate record, whatever statuses its package document prints.

`mreg audit --lenient` restores the old behaviour (gates that are `not run` or `flag` are not failures) and prints a warning. `mreg view` shows each build's labels and whether it is signed.

## Known limits

- Large cones: many declarations need thousands of chunks (some tens of thousands). Lean maps every file: it needs 8 to 9 GiB of address space for large cones. Never cap address space (`ulimit -v`); cap resident memory instead.
- Chunks give kernel checking and reference by name only. They carry no instances, simp sets, notation, parsers, macros or tactics: they are not a base for writing new proofs.
- Lake does not see chunks. Only plain `lean` or `lake env lean` with `LEAN_PATH` set from `mreg env` does; `lake build` does not.
- Chunks are tied to one Lean version, are not signed, and are trusted by hash against a list held in the same place.
- Wait times: the client retries on busy or slow answers (`Retry-After` is honoured, at most 30 seconds).

## Where errors go

Errors and warnings go to stderr, results to stdout; each failure is one plain line and exits non-zero (1 for most; 2 for a command-line usage error; named codes for declaration import: 10 unknown declaration, 11 ambiguous name, 12 not on the train, 13 key refused or missing, 14 hash mismatch, 15 forbidden mix of files, 16 registry unreachable, 17 object missing or taken down, 18 build removed, 19 index unusable, 20 wrong Lean toolchain, 21 over the request budget, 130 interrupted). When the registry says why it refused a key (bad signature, revoked, blocked), the client prints that reason. `MREG_DEBUG=1` adds a traceback with keys removed. Send what the command printed, plus `python mreg.py doctor`, to the person who gave you the key. Do not paste your key.
