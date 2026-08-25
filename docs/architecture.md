# Architecture and release policy

The library is organized by author and work, while theorem names remain close
to Mathlib style so genuinely reusable declarations can later move upstream.

Every promoted theorem must record:

- a stable bibliographic work identifier and source location;
- the exact controlled transcription snapshot used;
- its Mathlib coverage class;
- a no-`sorry` build result and `#print axioms` output;
- whether the formal proof supports, contradicts, or is neutral toward the
  transcription at that location.

Accepted build evidence uses schema-1.2 receipts. A receipt binds the exact
source, runner, Lean executable, normalized and raw toolchains, repository and
dependency manifests, parsed Mathlib revision, logs, platform, memory sample,
and pre/post hashes. Volatile checks remain under `artifacts/build/`; accepted
clusters are copied with their complete receipt/log triples and a checksum
manifest under `artifacts/release/`.

The checker never calls Lake or Git. It invokes the pinned Lean executable
directly, holds an exclusive workspace build lock, sets `LEAN_NUM_THREADS=1`,
and samples the captured process tree against an 8 GiB limit. On abnormal
termination it kills only that captured tree. The watcher is best-effort
sampled enforcement on Windows, not a Job Object hard ceiling, and receipts
state that limitation explicitly.

A direct Lean source check does not produce the `.olean` files required for
imports between local modules. The separate
`scripts/build-local-olean-bounded.ps1` therefore accepts an explicit ordered
file list, compiles each module serially into a run-specific cache, and emits a
`module-build-receipt/1.0` for every output. It shares the same exclusive lock,
one-thread setting, pinned dependency cache, and sampled memory ceiling. These
volatile integration receipts supplement but do not replace schema-1.2 theorem
receipts in a release cluster. Keeping this builder separate also leaves the
checker file hash embedded in existing release evidence unchanged.

Coverage classes are:

- `MATHLIB_EXACT`: an existing declaration already states the result;
- `MATHLIB_MODERN_FORM`: Mathlib has a stronger or structurally different form;
- `NEW_PACKAGING`: the ingredients exist, but the source-shaped declaration does not;
- `GAP_CANDIDATE`: no declaration was found, but proof work has not established novelty;
- `FORMALIZED_GAP`: searched, implemented without `sorry`, and built;
- `BLOCKED_SOURCE`: the mathematical statement is not stable enough to formalize;
- `DEFERRED_INFRASTRUCTURE`: genuine-looking gap requiring substantial foundations.

GitHub and Zenodo are checkpoint outputs. A release is warranted when a coherent
work or theorem cluster is green, its provenance ledger is complete, and its
claims have been reviewed. Tiny edits do not create deposits.
