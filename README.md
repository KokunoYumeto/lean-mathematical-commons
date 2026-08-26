# Lean of the Mathematical Commons

Public living repository:
[KokunoYumeto/lean-mathematical-commons](https://github.com/KokunoYumeto/lean-mathematical-commons).

A living Lean 4 library for source-linked formalization of classical mathematics.
The pilot author is **Emmy Noether**. The work runs on two coordinated tracks:

1. transcription QA against a controlled German witness; and
2. Lean formalization, prioritizing results not already present in Mathlib.

Formalization is evidence about mathematical statements, not a certificate of
page completeness, typography, translation, or diplomatic transcription.
Suspected German-source defects are routed to the separate canon owner and are
never silently repaired here.

## Current checkpoint

- Reproduces the downloaded Zenodo sidecars from
  [record 21129946](https://zenodo.org/records/21129946) under
  `archive/zenodo/21129946/`, with verified MD5 and SHA-256.
- Pins Lean/Mathlib `v4.31.0`, matching that deposit.
- Indexes all 43 numbered Noether work packets, including joint authorship,
  editorial roles, posthumous-source caveats, and open canon QA.
- Records declaration-level Mathlib coverage for nineteen Noether works: the 1916
  finite-group invariant paper, 1918 variational paper, 1919 integral-invariant
  paper, 1920 series-expansion paper, joint 1920 Noether–Schmeidler
  noncommutative-module paper, Noether's 1921 report on Hentzelt's elimination
  theory, 1921 *Idealtheorie*, the 1922 formal-variational encyclopedia entry
  and absolute-irreducibility criterion, the attribution-sensitive 1923
  Hentzelt--Noether polynomial-ideals/resultants paper, both 1923
  invariant/elimination surveys, the 1924 elimination/ideal-theory survey, the
  1924 abstract ideal-theory and 1925
  Hilbert-number/group-character communications, the 1926 modular-invariant
  paper, 1927 abstract Dedekind ideal theory, and the 1927 discriminant paper.
- Adds source-shaped, axiom-audited 1921 declarations for finite irreducible
  decomposition, both primary-ideal formulations, Satz V's unique prime,
  greatest-ideal and least-exponent clauses, Satz VI, and part of Satz VIII.
- Exposes the 1916 orbit-resolvent facts already in Mathlib without claiming
  that this proves Noether's still-open full invariant-system theorem.
- Adds a characteristic-free fixed-ring finite-generation theorem for finite
  actions on finite-type commutative algebras over Noetherian bases. The
  Mathlib ingredients existed, but the integrality-to-Artin–Tate combination
  did not; the ledger marks this precisely as `FORMALIZED_GAP`.
- Promotes bounded, axiom-audited support lemmas for the 1918 test-function
  step and the finite-bad-primes component of the 1922 argument without
  claiming either headline theorem.
- Maps every numbered theorem in the joint 1920 noncommutative-module paper,
  records its source dictionary and QA conflicts, and promotes the bounded,
  axiom-audited noncommutative quotient-product core of Satz I.
- Maps the 1919 integral-invariant paper through its determinant, multisymmetric,
  Plücker-ideal, straightening, and arithmetic finite-generation layers, and
  promotes only the elementary four-index Plücker support identity with bounded
  build and axiom evidence.
- Maps the 1920 series-expansion paper, its three authorial corrections to
  earlier papers, and the missing Fischer/Plücker/operator layers; promotes the
  exact substitution-kernel congruence without claiming a normal form.
- Maps Noether's five 1927 Dedekind axioms, unique prime-power factorization,
  converse development, fractional ideals, finite length, and Jordan–Hölder;
  the exact Artinian-nonzero-quotient/dimension-one bridge is promoted with
  bounded build and axiom evidence.
- Maps the five labelled results of the 1927 discriminant paper, records the
  pinned `proof_wanted` dependency in reverse étale descent, and promotes the
  independent local finite-free quotient-discriminant reduction.
- Maps the 1922 formal-variational entry and the algebraic/differential halves
  of the 1923 invariant survey, preserving historical attribution and keeping
  Noether I/II, curvature jets, Reynolds operators, and jet reduction as
  explicit infrastructure gaps.
- Maps all 31 claims in the 1924 elimination/ideal-theory report. Root fields,
  prime quotients, finite ideal bases, and splitting fields are separated from
  the missing primary-decomposition and successive-norm layers.
- Promotes P23 Satz 5 with the source's uniform quantifier order—one positive
  radical exponent works for every vanishing ideal—and promotes P25's generic
  zero in the fraction field of a prime quotient, where evaluation vanishes
  exactly on the prime ideal. Both are axiom-audited Lean 4.31 builds.
- Maps P22's staged ground modules, Smith forms, resultants, determinantal
  elimination, compatible zeros, and multiplicities without conflating its
  factors with `Polynomial.resultant`. Promotes the conditional Satz VIII
  radical/zero-set bridge, proves unrestricted relative Dedekind--Mertens, and
  uses bounded Kronecker substitution to prove Hentzelt's literal integer-linear
  multivariate equation (17). It now also formalizes the full lower-
  unitriangular equation (12) over its natural algebraically-independent
  lower-pair parameters, the literal late-variable stage submonoids, common
  parameter-denominator presentations, coefficient reconstruction, and the
  final two-sided transformed-ground-ideal equality of Satz VI. Satz XI's
  exact residue rank and displayed basis are also promoted. Satz XII now has
  the finite-coordinate root-box theorem and its explicit zero-locus embedding,
  as well as the following Nullstellensatz corollary; the later staged
  resultants and compatible-zero construction remain open. Equation (21)'s
  regular-division step is also promoted: for a supplied degree-`k` polynomial
  regular in `x₁`, every polynomial has an exact representative modulo it whose
  `x₁`-degree is strictly less than `k`. Equations (22)--(23) are now promoted
  too: the remainder has an explicit `Fin k` coefficient vector, and every
  polynomial ideal containing the regular divisor is the internal sum of its
  bounded-degree part and the disjoint principal tail generated by that
  divisor. The characteristic-zero finite-avoidance step used after Satz VII
  is formalized for any supplied finite family of regularity coefficients. The
  full independent lower-unitriangular transform from equation (12) is now
  proved to preserve the exact total degree of every nonzero input. A
  dehomogenization and algebraic-independence argument proves its first-variable
  leading coefficient nonzero for every nonzero polynomial, and the generic
  transform of every nonzero ideal therefore contains a regular member. Finite
  parameter descent, the later stage modules, staged resultants, and the
  compatible-zero system remain open.
- Extends P25's generic-zero construction: evaluation has kernel exactly the
  prime ideal, and the generic coordinate tuple generates the fraction field
  of the prime quotient over the coefficient field. It now also proves the
  range-cardinality bound, the finite-coordinate theorem `trdeg ≤ n`, and the
  strict theorem `trdeg < n` when the prime ideal is nonzero. The unqualified
  printed strict bound remains critical apparatus, not silently repaired.
- Promotes the P23 Satz 3 coefficient-replacement core under an explicit
  additive invariant retraction; construction of Hilbert/Fischer's
  Ω/Reynolds operator remains an explicit representation-theory gap.
- Promotes Noether's 1924 Dedekind characterization as an exact equivalence
  between `IsDedekindDomain` and integral closure plus Artinian nonzero
  quotients, under explicit Noetherian-domain assumptions.
- Promotes the binary localization-contraction core of the 1923 ground-ideal
  intersection lemma, without claiming the missing elimination norm or primary
  decomposition.
- Enforces serial, memory-watched Lean runs; the working ceiling is 5 GiB.

## Author index

The full cross-author landing page is [docs/index.md](docs/index.md), backed by
the machine-readable [metadata/authors.tsv](metadata/authors.tsv).

| Author | Local corpus | Lean status | Existing public record |
|---|---|---|---|
| Emmy Noether | present | active pilot | [Noether corpus DOI](https://doi.org/10.5281/zenodo.20412587) |
| Ernst Steinitz | present | one deposited Mathlib anchor | [Steinitz corpus DOI](https://doi.org/10.5281/zenodo.20616988) |
| J. J. Sylvester | present | inventory queued | [Sylvester corpus DOI](https://doi.org/10.5281/zenodo.20520692) |
| Hellmuth Kneser | present | inventory queued | [Kneser corpus DOI](https://doi.org/10.5281/zenodo.20836971) |
| Paul Gordan | present | invariant-theory scaffold queued | [Gordan corpus DOI](https://doi.org/10.5281/zenodo.20616260) |

The historical corpus remains centrally indexed in
[modern-latex-manuscripts](https://github.com/KokunoYumeto/modern-latex-manuscripts).
This repository is the formalization-focused companion, not a duplicate archive.

## Build without exceeding RAM

The normal local check is serial and watched:

```powershell
./scripts/run-lean-bounded.ps1 `
  -File ./MathematicalCommons/Noether/Idealtheorie1921.lean `
  -DependencyProject C:/path/to/a/prebuilt/mathlib-project `
  -MaxMemoryGiB 5
```

The checker invokes the pinned Lean executable directly and builds `LEAN_PATH`
from the named project's existing package cache. It does not invoke Lake or Git,
perform a repository-wide scan, or update dependencies. Each schema-1.2 receipt
binds the source, runner, Lean executable, toolchains, manifests, Mathlib commit,
logs, platform, process-tree peak, and limit. The Windows watcher samples the
captured Lean process tree every 200 ms and kills only that tree over the limit;
it is explicitly recorded as sampled enforcement, not a Job Object hard ceiling.

Direct source checks do not create local `.olean` files. To verify the complete
local import graph, `scripts/build-local-olean-bounded.ps1` compiles an explicit
ordered file list into a run-specific cache under `artifacts/build/local-olean/`.
It uses the same one-thread, exclusive-lock, sampled process-tree policy and
writes a receipt for every module. It never invokes Lake or Git and does not
modify the release-verifier-bound source checker. For a narrowly missing
dependency object, its opt-in `-MirrorPackageOutputs` mode hash-checks and
mirrors only explicitly compiled sidecars into the disposable dependency
project; it refuses a conflicting target rather than rebuilding a package.

The current 32-target graph check (30 promoted theorem/support modules and both
umbrellas) is checkpoint
[`20260826T0458000385704-942a1542`](artifacts/build/module-graph-checkpoint-20260826T0458000385704-942a1542.json).
It reuses 29 unchanged theorem modules, completes P22's existing generic-
regularity module, and rebuilds both umbrellas; every current target exited
zero with empty stderr and unchanged source/environment. The
maximum observed process-tree working set across the checkpoint chain was
1,919,344,640 bytes under the strict 3 GiB worker envelope; every new build
used a 2.5 GiB process-tree cap.

Meaningful theorem clusters—not individual edits—are the intended GitHub/Zenodo
release unit. The existing sidecar concept DOI is
[10.5281/zenodo.21129945](https://doi.org/10.5281/zenodo.21129945).

## Project map

- `MathematicalCommons/`: compiling Lean source.
- `docs/noether/mathlib-coverage.md`: verified coverage and gaps.
- `docs/index.md`: central cross-author “Lean of the Mathematical Commons”
  landing page.
- `docs/noether/paper-inventory.md`: all 43 numbered work packets and QA flags.
- `docs/noether/integral-invariants-1919.md`: binary integral invariants,
  multisymmetry, Plücker relations, straightening, and open source QA.
- `docs/noether/series-expansion-1920.md`: Fischer normal forms, relation
  ideals, authorial corrections, and the promoted substitution congruence.
- `docs/noether/communications-1924-1925.md`: abstract ideal theory, Hilbert
  numbers, semisimple group algebras, and source-scope boundaries.
- `docs/noether/elimination-ideal-theory-1923.md`: successive elimination
  forms, primary decomposition, dimension, and arithmetic specialization gaps.
- `docs/noether/hentzelt-elimination-report-1921.md`: attribution-sensitive
  resultant claims and the boundary between exact zero-locus semantics and
  source-blocked elimination structure.
- `docs/noether/hentzelt-polynomial-ideals-resultants-1923.md`: the full
  staged Hentzelt--Noether construction, pinned Smith/norm coverage,
  promoted source-exact multivariate Dedekind--Mertens equation (17), its
  source-faithful coordinate/localization/ground-ideal equality, Satz XI rank
  and basis, Satz XII's finite-coordinate zero-locus substrate and
  Nullstellensatz corollary, the finite regularity-specialization theorem,
  equation-(21) bounded regular-division representatives, equations-(22)--(23)
  finite coefficients and internal ideal decomposition, and promoted Satz VIII
  support.
- `docs/noether/formal-variational-calculus-1922.md`: formal variations,
  covariant differentiation, curvature, and the source-level Noether I/II gap.
- `docs/noether/algebraic-differential-invariants-1923.md`: Hilbert-basis and
  invariant-theory claims, uniform radical powers, and differential reduction.
- `docs/noether/elimination-ideal-theory-survey-1924.md`: all 31 compressed
  univariate/multivariate claims, generic-zero theorems, and the safe
  transcendence-degree bound.
- `docs/noether/dedekind-theory-1927.md`: source and Mathlib map for Noether's
  five Dedekind axioms, factorization, finite length, and Jordan–Hölder.
- `docs/noether/discriminant-theorem-1927.md`: discriminants of finite algebras
  and orders, scalar extension, localization, ramification, and open source QA.
- `metadata/noether-works.tsv`: machine-readable paper inventory.
- `metadata/noether-theorems.tsv`: source-to-declaration ledger.
- `metadata/noether-canon-qa.tsv`: machine-readable open discrepancies already
  routed to the German canon owner.
- `sources/noether/CANON_REFERENCE.json`: immutable reference to the external
  German authority snapshot used by this checkpoint.
- `sources/noether/CANON_DECISION_ED0020_20260825.json`: verified append-only
  canon decisions and inactive-successor custody; it does not rebase existing
  ED0014 theorem provenance or activate ED0020.
- `archive/zenodo/21129946/`: original deposited ZIP and lossless extraction.
- `scripts/run-lean-bounded.ps1`: RAM-bounded serial checker.
- `scripts/run-lake-bounded.ps1`: RAM-bounded dependency-cache command runner;
  it is not a dependency updater.
- `scripts/build-local-olean-bounded.ps1`: RAM-bounded serial local-module and
  umbrella builder using a disposable import cache.
- `scripts/verify-release.ps1`: independent checksum, receipt, source, axiom,
  toolchain, Mathlib-pin, and memory-evidence verifier.
