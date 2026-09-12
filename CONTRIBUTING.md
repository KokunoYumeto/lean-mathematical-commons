# Contributing source-linked mathematics

Keep one mathematical target or one maintenance change reviewable at a time.
A clean build is necessary, but it does not establish that a theorem matches
its historical source or that every claim in a paper has been formalized.

## Before changing a proof

Read the relevant source locator and claim-ledger row. Write the exact intended
statement and hypotheses; distinguish Mathlib coverage, new packaging, a completed
formalization and support for a still-open target. Retain joint-author and external
Lean attribution. A source discrepancy belongs in the critical apparatus, not in
a silent rewrite of the controlled witness.

Keep the public namespace and theorem statement stable during proof cleanup.
Changes to assumptions, exported names, dependency versions or mathematical scope
need an explicit explanation. Do not add an axiom, `sorry`, native proof escape or
stronger assumption to obtain a green check.

## Validate the current source

Run the inventory and checker regression tests described in [BUILDING.md](BUILDING.md).
Run a fresh serial build and inspect the explicit transitive axiom reports. Use
`--strict-file` for a changed proof file, preserve any remaining warnings in the
report, and retain the exact commit and source hashes. Extending the set of public
theorems should include explicit `#print axioms` commands for the new targets.

A module must belong to the actual root import graph; a file left outside the
umbrella is not silently counted as an integrated result. An intentional research
scratchpad belongs outside the compiling `MathematicalCommons/` tree.

## Preserve provenance

Do not rewrite old build receipts, claim snapshots, source hashes, release metadata
or controlled-source decisions to make a new edit look previously verified.
Attach new evidence to new source bytes. Update current claim classifications only
when the mathematical obligation they describe is genuinely discharged; a helper
or a wrapper alone is not closure of the encompassing historical theorem.

Review the diff for generated caches, credentials, unlicensed source copies and
unrelated changes. Do not commit `.noether-check/`, `.lake/`, or Python bytecode.
The CI artifact carries the checked source and logs; compiled objects remain
disposable build outputs, not committed source. Current verification and the historical release checks have distinct
scopes; neither should impersonate the other.
