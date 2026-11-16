# Changes in mreg 0.5.2 (over 0.5.1)

`mreg 0.5.2` keeps all four repository client copies (`mreg/mreg.py`, `mreg/next/mreg.py`, `mreg/dist-beta/mreg.py`, and `builder/compose/mreg_beta.py`) byte-identical and adds signed redacted transparency-log verification plus automatic `LICENSE`, `NOTICE`, and `THIRD_PARTY_LICENSES.txt` handling.

## Redacted transparency-log tombstones
- `mreg audit` and log-chain verification (`log_entry_raw`, `_verify_redacted_chain_sha`, `chain_problems`) accept signed redacted log tombstones (`schema: "mreg-log/1"`, `type: "redacted"`) stored under `v1/log/<n>.json` or `v1/log/redacted/<n>.json` when the original entry returns 404 or 451.
- Each redacted tombstone is checked for canonical JSON formatting, ECDSA P-256 signature under the registry's `keys.json`, and signed `entry_sha256` + `prev` hash-chain continuity across the surrounding log entries.
- `mreg audit` clearly reports `log entry N has been redacted (<reason>)` when auditing a redacted entry instead of treating it as corrupt chain data.

## Licence & notice preservation
- Module-level installs download and SHA-256-verify both `LICENSE` and `NOTICE` files (when recorded in `license_sha256` / `notice_sha256` on the manifest) alongside the unpacked package files.
- Declaration-chunk installs (`_ensure_chunk_licenses`) write `THIRD_PARTY_LICENSES.txt` into the chunk directory, fetching `/x/decl/<train>/THIRD_PARTY_LICENSES.txt` (cached locally per train under the store) or writing the bundled Apache-2.0 / attribution fallback notice.

## Unified distribution artifact
- `VERSION = "0.5.2"`
- All four repository client copies (`mreg/mreg.py`, `mreg/next/mreg.py`, `mreg/dist-beta/mreg.py`, and `builder/compose/mreg_beta.py`) are byte-identical (`SHA-256: 1f5d0010c042180308852d6aabfd46f833faf7594737c29f8ab827aae9f079e6`).
