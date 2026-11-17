# First steps with mreg 0.6.6

Updated 2026-11-17 for mreg 0.6.6. Commands are the client's own (`mreg --help` and `<command> --help`).
What you should see below is what the registry's records say it should be; wording the client prints that we did not check is
marked "(wording not checked)". Never paste a key into a chat, a ticket, a file or a command line. If a step differs, see the
last section.

Mreg 0.6.6 preserves user-edited Lean files and reuses the generated entry and chunk directory recorded in the lock. Signed declaration installs use the registry receipt. Use --preserve-behavior to install the original modules. Building on 0.5.0's strict
admission (`install` and `ci` refuse exit 4 without `--allow-unverified`) and `mreg check` (which runs your project's own code and is
not a sandbox) and 0.5.1's `--require-views` / `MREG_REQUIRE_VIEWS=1` (contract 1.2.0), Tarjan SCC cycle fix in `mreg check`,
`/.well-known/mreg-auth.json` endpoint discovery, and loopback callback port fallback (`8976`, `8977`, `8978`), 0.5.2 adds signed
redacted transparency-log tombstone verification and automatic `LICENSE`/`NOTICE`/`THIRD_PARTY_LICENSES.txt` preservation. Earlier changes:
0.4.2 made `install --check` and `ci` re-hash every installed file; 0.4.1 fixed a second sign-in on Linux.

## 0. Install the client

Run `python -m pip install "git+https://github.com/MoteMath/MathRegistry.git"`, then `mreg --help`.
Python 3.10 or newer and Git are required. Lean and Lake are required to use compiled packages.

## 1. Sign in at the account page

Open `https://mathregistry.com/account`. You see "Account" and two buttons, "Sign in with GitHub" and "Sign in with Google".
Use the account whose verified email address was invited; only invited addresses can sign in. After the provider's page you
return to `/account` and see "Signed in as <your address> via GitHub." (or "via Google."), a "Label (optional)" box, a
"Create API key" button and a table that says "No keys yet." for a new user.

## 2. Create a key

Type a label if you like, then click "Create API key". The page shows "Copy this key now. It is shown only once and cannot be
shown again." and the key, which starts `mreg_`. It gives read access only. Keep the page open until step 3 has worked.

## 3. Give the key to the client

The client reads the key from the environment variable `MREG_TOKEN`, or from the file `.mreg/token` in your home folder (one
line). Either put the key there yourself, or let the client do steps 1 to 3 for you:

    mreg login

It opens the sign-in page, creates a key and stores it in your `.mreg` folder (options: `--provider github|google`, `--label`,
`--no-browser`). Its printed wording was not checked. `mreg whoami` then tells you what kind of key is stored, and
prints nothing secret.

## 4. `mreg doctor`

    mreg doctor

It prints your Python version, tools found on the PATH, whether zstd is usable, the credential (kind and where it came from,
never the key), your local store, and one request to the registry. The last line is "result: ok" when nothing is wrong, or
"N problem(s)" with a "problem:" line for each. A "warning:" line about Lake or Lean not being on the PATH does not matter for
the next steps.

## 5. Strict audit of Mathlib

    mreg audit leanprover-community/mathlib4

Audit is strict by default. The first time the client sees the registry's signing key it pins it and prints a line starting
"note: pinned signing key", with the key id. That id must be

    f4ac93fa070519ea

(we also ask you to confirm it with us in a channel other than this site before you rely on it). Then you should see one row

    leanprover-community/mathlib4 4.35.0 adc2e7427d6cb981  [G1:pass ... G10:pass]  labels=clean  OK

with every gate G1 to G10 showing pass, and the exit code 0 (`echo $LASTEXITCODE` in PowerShell, `echo $?` in a Linux shell).
What that means and does not mean is in the page "What is and is not guaranteed": the signature, the log and the gate records
agree with the build's manifest; it is not a check of any proof, and 1,148 constants marked `unsafe` or `partial` plus 656
macro-scoped names are not checked by the second kernel.

## 6. Audit an imported build

    mreg audit AxiomMath/ClusterAlgebras

The output names the exact version, build key, and gate results. A passing imported build has a registry signature and verification evidence for the compiled files. Use the exit status to check the result for the version currently served.

## 6c. `mreg check`: is your project valid?

In a project where you installed something (for example after `mreg init` and `mreg add leanprover-community/mathlib4`
and `mreg install Mathlib.Data.Nat.Prime.Basic`, plus a module of your own), run

    mreg check

It re-hashes the installed files against the registry and audits their builds (step 1), checks that everything is on one train
(step 2), builds your own modules with Lake and fails on any `sorry`, `admit`, `native_decide`, `bv_decide` or `axiom` in them, with
file and line (step 3), replays your modules with Lean's checker (step 4), lists the axioms each of your theorems uses and fails on
any beyond propext, Classical.choice and Quot.sound unless you name it with `--allow-axiom` (step 5), and prints your theorems'
statements (step 7). Exit 0 means every step passed; a line "check passed but INCOMPLETE" names what was not covered. Read
CHANGES-0.5.0.md for what it does not prove (no kernel checks that a theorem says what you meant; dependencies' public .olean files
are pinned by hash, not re-checked). **`check` runs your project's code (`lake build`, Lean on your modules): run it only on code you
would build anyway.** `--fast` skips the replay; `--json` prints one document.

## 7. Rotate the key

On the account page, click "Rotate" in the key's row and confirm. The old key stops working and a new one is shown once: copy it,
replace the key in `MREG_TOKEN` or `.mreg/token`, and run `mreg whoami` and `mreg doctor` again.

## 8. Revoke the key

Click "Revoke" in the key's row and confirm (it cannot be undone), or run `mreg logout --revoke` (it signs you in again
and revokes the stored key at the service, then deletes the stored key file). A revoked key was refused at the edge within about 30
seconds in the three measurements we made (23, 29 and 29 seconds); the account page says about a minute, so allow a minute.

What you will see. After `logout --revoke` the key file is gone, so `mreg doctor` reports that there is no credential; that is
not a rejected key. To see that the revoked key no longer works, look at the key list on the account page (the key's row is struck
through and its state reads "revoked"), or, if you kept a copy of the old key, put it in `MREG_TOKEN` and run any read such as
`mreg train`: it must fail with an error saying the key is not accepted (wording not checked). Then create a new key (step 2)
if you want to continue.

## If any step differs

Write to the contact address in section 11 of the terms of use, served behind your key at `/x/docs/pages/terms.md`. Send the step
number, the exact command, and the output, with any key removed first. Never send a key. If you think a key has leaked, revoke it
on the account page first.
