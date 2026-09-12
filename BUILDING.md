# Building and verifying Noether

## Reproduce the locked library

Use elan and the repository's `lean-toolchain` (Lean 4.31.0). Keep the committed
`lake-manifest.json`, which fixes Mathlib and its transitive dependencies.

```sh
lake exe cache get
lake build MathematicalCommons
```

`lake exe cache get` retrieves dependency objects; it does not establish that
this repository's proofs are correct. `lake build` builds the requested root
and its imports, using normal incremental caching. Neither command is a
source-to-paper audit. The cleanup fixes the historical Mathlib `configFile` entry from `lakefile.toml`
to the existing `lakefile.lean`; all nine dependency revisions stay unchanged.
Do not run `lake update` unless intentionally changing
and separately reviewing the dependency lock.

## Current inventory and checker tests

Python 3.11 or later is sufficient; no third-party Python packages are required.

```sh
python3 -m unittest discover -s tests -v
python3 scripts/noether_check.py
```

The inventory reads the local source tree and both TSV ledgers. It validates
unique row identifiers, claim-to-work references, locked dependency revisions,
local import closure and acyclicity, and reports actual module and ledger-state
counts. It records the SHA-256 of each Lean source and its explicit
`#print axioms` targets. It masks comments and strings before the limited source
scan. This is not a full Lean parser; unsupported import/report syntax is rejected
rather than silently certified. The scan and checker tests do not run Lean.

Output goes to `.noether-check/inventory.json`, outside the historical receipts.
The report distinguishes metadata classifications from fresh proof evidence and
does not estimate the percentage of Noether's complete mathematics formalized.

## Fresh serial source and axiom checks

After retrieving the locked dependencies:

```sh
python3 scripts/noether_check.py --resolved
python3 scripts/noether_check.py --build \
  --strict-file MathematicalCommons/Noether/EliminationIdealTheorySurvey1924.lean
```

The checker verifies the resolved commit and tracked-source cleanliness of every
locked dependency. It then compiles **every local module in topological order**,
including the two umbrellas, with `lean --trust=0`. Newly generated local objects
are placed first in Lean's import path. It never reuses an earlier local-object
run or replaces the package's normal Lake build directory. The compilation is
serial and uses `LEAN_NUM_THREADS=1`; this is not a measured RAM ceiling or a
replacement for the historical Windows process-tree memory controls.

`--strict-file` additionally promotes warnings to errors for a named file. Other
warnings are retained in the report, not suppressed or presented as a warning-free
build. A build timeout, missing module, missing/mismatched/duplicate axiom report,
nonzero compiler exit, or unapproved reported axiom causes failure.

The accepted axiom set is `propext`, `Classical.choice`, and `Quot.sound`.
The checked targets are **all explicit source `#print axioms` commands**, not every
local definition, generated declaration, or historical claim. Both the target
list and the actual qualified names are retained. A clean selected dependency
report does not establish that a definition expresses the intended mathematics,
nor does it independently recheck the complete Mathlib cache or provide an
adversarial proof-security certification.

For a second run, select a fresh output directory; existing local objects are
rejected rather than reused:

```sh
python3 scripts/noether_check.py --build --output .noether-check/recheck
```

The outputs are `verification.json`, per-module logs, source and log hashes,
warning records, and local `.olean` files. The GitHub workflow also archives the
exact checked source and commit. Read the workflow conclusion and the report's
`build_success` together; an artifact from a failed run is retained for diagnosis,
not proof of success.

## Historical verification remains separate

The PowerShell tools in `scripts/` and the existing `artifacts/build/` receipts
remain untouched. They document earlier bounded, sometimes incremental builds
and release verification. Their hashes refer to those historical source bytes.
A refactored file needs a new current-source result; an old receipt is not silently
rewritten to match it. For the old procedure and its memory caveats, see
[the preserved checkpoint narrative](README.checkpoint-20260829.md).
