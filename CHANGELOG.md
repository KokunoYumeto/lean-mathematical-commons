# Changelog

## Unreleased

- Created the public living repository
  [`KokunoYumeto/lean-mathematical-commons`](https://github.com/KokunoYumeto/lean-mathematical-commons)
  and published the 29-target green Noether checkpoint at commit
  `159b957c9d95375151d51d5dc957ebf879852659`. All 258 selected source,
  documentation, ledger, script, pointer, and build-evidence blobs matched the
  local Git blob hashes; anonymous archive and raw-checkpoint downloads both
  returned HTTP 200. Caches, staging, logs, credentials, and large corpora were
  excluded.
- Published the coherent 32-target P22 scaffold checkpoint at GitHub commit
  `035cc26424023f2414cae2daf5fb0d0c213e371b`; 338 selected blobs were checked,
  and anonymous archive, raw-file, and repository requests returned HTTP 200.
- Expanded P22's equation-(12) module from ten to 35 declarations. The new
  dehomogenization/algebraic-independence proof makes the generic leading
  coefficient nonzero for every nonzero polynomial, proves exact total-degree
  preservation and first-variable regularity, and gives a regular member in
  the transform of every nonzero ideal. P22 now has 256 canonical declarations
  across the base and fifteen support modules, with 29 claim/definition records.
- Expanded the maintained graph to 32 targets (30 theorem/support modules and
  both umbrellas). The completed module and umbrellas all exited zero with
  empty stderr under 2.5 GiB caps; the checkpoint-chain peak remains
  1,919,344,640 bytes under the strict 3 GiB worker envelope.
- Added opt-in, hash-checked dependency sidecar mirroring to the bounded local
  builder for narrowly missing prebuilt objects; conflicting targets are
  refused and no package-wide rebuild is performed.

- Continue the theorem-level audit of Noether's 1921 *Idealtheorie*.
- Formalize the still-open multivariate invariant-system and degree-bound
  arguments from the 1916 finite-group paper.
- Added source inventories and dependency maps for the 1918 variational and
  1922 absolute-irreducibility papers, with green bounded support lemmas that
  are explicitly not advertised as the headline theorems.
- Added the 1919 integral-invariant audit covering all four Sätze, the integral
  Plücker relation ideal and straightening argument, and the final finite-group
  applications. Three formula conflicts were routed to the canon owner; the
  elementary Plücker identity is promoted with a clean bounded build and axiom
  output, without claiming the full relation ideal or Satz I.
- Added the 1920 series-expansion audit, recorded its authorial corrections to
  the 1918/1919-era invariant work and Hilbert-irreducibility hypothesis, and
  promoted the exact substitution-relation congruence. Fischer normal forms,
  polar/Omega expansions, and Plücker kernels remain explicit gaps.
- Added the 1926 modular-invariant audit and a green characteristic-free
  fixed-ring finite-generation theorem, classified as `FORMALIZED_GAP` because
  Mathlib supplied the ingredients but not their Artin–Tate combination.
- Added the 1927 abstract Dedekind-theory audit: five axioms, integrality,
  primary and prime-power factorization, the converse, fractional ideals,
  finite length, and Jordan–Hölder. The source-shaped equivalence between
  Artinian nonzero quotients and dimension at most one is now promoted with a
  clean bounded build and axiom output.
- Added the 1927 discriminant-paper audit: all five labelled results, exact
  field-level trace/norm/discriminant anchors, arbitrary-order gaps, source QA,
  and the warning that reverse étale descent depends on `proof_wanted` at the
  pinned Mathlib revision.
- Promoted the local finite-free quotient-discriminant reduction at source line
  16041 with a clean bounded Lean 4.31 receipt, independently of the unfinished
  reverse étale-descent route.
- Expanded the paper inventory to nineteen partial declaration audits and added a
  central cross-author index without duplicating the large source corpora.
- Added claim-level maps for the 1922 formal-variational encyclopedia entry and
  the 1923 algebraic/differential-invariant survey. The maps preserve reported
  historical attribution, distinguish finite-dimensional Lie groups from
  finite groups, and keep jets, curvature reconstruction, Reynolds operators,
  and Noether I/II as explicit gaps rather than inferred formalizations.
- Added all 31 claims and definitions from the 1924 elimination/ideal-theory
  report. Exact root-field, zero-locus, quotient-domain, splitting-field, and
  finite-basis coverage is separated from the primary-decomposition gap and
  the source-blocked successive elementary-divisor norm.
- Promoted the exact uniform-quantifier core of P23 Satz 5 in abstract radical
  language and algebraically closed zero-locus form. Promoted P25's generic-zero
  construction and relation-ideal equality in the fraction field of a prime
  quotient. Both canonical modules build with empty stderr and only `propext`,
  `Classical.choice`, and `Quot.sound` in their axiom reports.
- Routed the P21 `f'`/undefined-`D` formula questions and the P25 strict
  transcendence-degree/Galois-terminology scope questions to the German canon
  owner without changing the controlled witness.
- Recorded the canon owner's primary-witness resolutions without editing Lean
  or German: P21's primes are transcription errors corrected only in inactive
  ED0020; capital `D`, P25's strict bound and Galois wording, P16's continuation,
  P24/P27/P28 conventions, and P18's grammar are print-faithful; P18's page is
  101 and P22 confirms staged resultants; P31's three reported issues are
  resolved. Existing declarations remain bound to ED0014 provenance.
- Added complete claim maps for Noether's three 1924–25 one-page
  communications on abstract ideal theory, Hilbert numbers, and group
  characters; routed the colon-ideal notation and irreducible-character scope
  questions to the German canon owner.
- Promoted the precise 1924 Dedekind characterization using the local
  Artinian-quotient/dimension-one bridge, with a green bounded module build and
  clean axiom output.
- Promoted the general localization-contraction definition of ground ideals and
  its binary-intersection theorem, the honest lattice core of P24 Hilfssatz VI.
- Mapped all definitions, eight Hilfssätze, and seventeen Sätze in the 1923
  elimination/general-ideal-theory paper, isolating the successive
  Smith/elimination norm as missing infrastructure and routing two index
  readings to canon review.
- Added an attribution-sensitive map of Noether's 1921 conference report on
  Hentzelt: nine Hentzelt claims are separated from Noether's reporting/editorial
  role, and the grammar/resultant-layout questions are with the canon owner.
- Added the exact-range P22 audit, now 26 machine-readable records after
  separating the parameter-denominator proof layer, while preserving
  Hentzelt's authorship and Noether's free editorial recasting. Promoted the
  conditional Satz VIII principal-radical and zero-set bridge, and recorded
  Dedekind--Mertens as a genuine TODO in pinned Mathlib rather than treating
  the missing staged resultant as ordinary `Polynomial.resultant`.
- Proved unrestricted Dedekind--Mertens for coefficient submodules over an
  arbitrary commutative base algebra. A bounded injective Kronecker encoding
  preserves coefficient finsets and yields Hentzelt's literal multivariate
  equation (17), including its `ℤ`-linear semantics. The coefficient-to-ideal
  inference used in equations (19)--(20) is also formalized.
- Added 81 further P22 declarations: the full lower-unitriangular equation
  (12) with recursive inverse and ideal transport; nested-variable and
  rational-parameter denominator clearing; the localization witness model of
  stage ground ideals; and the exact parameter-coefficient (19)→(20) theorem.
- Added 56 more P22 declarations, bringing that paper's canonical library to
  188. Natural algebraically-independent lower-pair parameters, literal
  successive-stage submonoids, finite-parameter coefficient reconstruction,
  and common denominator presentations now prove both inclusions of Satz VI's
  transformed-ground-ideal equality. The same increment promotes Satz XI's
  exact residue rank and displayed basis and Satz XII's finite-coordinate
  root-box substrate plus its Nullstellensatz corollary. Regularity
  determinants, staged resultants, and compatible partial zeros remain open.
- Added eight P22 regularity-specialization declarations, bringing the paper's
  canonical library to 196 and its claim ledger to 27 records. They define the
  printed pure-power regularity
  condition and prove simultaneous preservation of any supplied finite family
  of regular leading coefficients over a characteristic-zero field. The
  finite avoidance theorem is separate from the still-open construction of
  Hentzelt's determinants and rational-function denominator data.
- Added twelve P22 equation-(21) regular-division declarations, bringing the
  paper's canonical library to 208 while its claim ledger remains at 27
  records. They normalize a supplied degree-`k` regular divisor to monic form,
  define quotient and remainder, reconstruct every polynomial modulo the
  original divisor, and produce a multivariate representative with strict
  `x₁`-degree `< k`. Construction of the source determinants `C^(i)`, the
  multistage finite-module assembly, Smith data, and auxiliary-choice
  independence remain open.
- Added thirteen P22 declarations for equations (22)--(23), bringing the
  paper's canonical library to 221 and refining its ledger to 28 records. They
  extract the exact finite coefficient vector of a regular remainder, decompose
  every containing polynomial ideal into its bounded part and principal tail,
  identify the original and monic tails, and prove the two summands disjoint.
  The historical quotient isomorphism and inductive finite-stage/Smith
  construction remain open.
- Proved P25's field-generation clause `R = P(α₁, ..., αₙ)`: the intermediate
  field generated by the generic coordinate classes is the whole fraction
  field of the prime quotient. The theorem is separate from the printed
  strict transcendence-degree bound and does not resolve that canon apparatus.
- Derived P25's valid transcendence-degree content from that field-generation
  theorem: for arbitrary coordinates, `trdeg` is bounded by the cardinality of
  their range, and for `Fin n` it is at most `n`. Equality remains allowed for
  the zero prime, so the primary-print-confirmed strict `k<n` is still kept as
  apparatus rather than silently repaired.
- Proved the complementary P25 strict theorem under the explicit alternative
  repair `I ≠ ⊥`: a nonzero relation in the prime ideal rules out the full
  generic tuple being a transcendence basis, hence `trdeg < n`. The diplomatic
  German remains unchanged because the source itself states no such hypothesis.
- Expanded the maintained import graph from 20 to 27 targets after the second
  P22 promotion: reused eighteen theorem modules, added seven theorem modules,
  rebuilt both umbrellas under a 2.5 GiB per-tree cap, and recorded nine green,
  empty-stderr receipts in checkpoint `20260825T1731028838723-d142a692`.
- Expanded the maintained import graph to 28 targets with the P22 regularity
  module and rebuilt both umbrellas under the same 2.5 GiB cap. Checkpoint
  `20260825T2238382165549-6e0a4f8b` records three green, empty-stderr receipts.
- Expanded the maintained import graph to 29 targets (27 theorem modules and
  both umbrellas) with P22's regular-division module. It reused 26 theorem
  modules and rebuilt the new module and both umbrellas under the 2.5 GiB cap.
  Checkpoint `20260826T0014097083391-9fccc982` records three green,
  empty-stderr receipts.
- Expanded the maintained import graph to 31 targets (29 theorem modules and
  both umbrellas) with the two equations-(22)--(23) modules. It reused 27
  theorem modules and records four green, empty-stderr receipts in checkpoint
  `20260826T0128334961800-2e82e4f7` under the 2.5 GiB per-tree cap.
- Promoted the abstract P23 Satz 3 coefficient-retraction core: finite
  coefficient identities can be replaced by invariant coefficients once an
  additive projection with the required fixed-point, range, and
  invariant-factor laws is supplied. The Ω/Reynolds construction remains open.
- Added the joint Noether–Schmeidler 1920 theorem inventory, Mathlib map,
  machine-readable source QA, and a promoted Satz-I quotient-product core with
  a clean bounded Lean 4.31 receipt and axiom output.
- Added a serial bounded local-module builder and verified all fifteen promoted
  theorem modules plus both umbrellas in one import cache. Batch
  `20260825T0355153955281-3669b4fc` produced seventeen green receipts with
  empty stderr; its observed peak was 1,827,332,096 bytes under the 4.5 GiB
  watcher.
- Restored the exact pinned source packages and only the targeted prebuilt
  cache closure without `lake update` or Git. New work uses a 5 GiB ceiling;
  observed proof checks remained below 1.4 GB.
- Continue auditing the remaining Noether works paper by paper before
  promoting the next coherent release cluster.

## 0.1.0-dev — 2026-08-24

- Preserved and independently hash-verified Zenodo record 21129946.
- Added a 43-work Noether paper inventory with attribution and canon-QA flags.
- Added a source-linked 1916 orbit-polynomial module, explicitly classified as
  packaging of existing Mathlib declarations rather than the full theorem.
- Expanded the 1921 module to eleven green declarations covering finite
  irreducible decomposition, primary-ideal formulations, the three clauses of
  Satz V, Satz VI, a prime-irreducibility corollary, primary decomposition, and
  the first direction of Satz VIII.
- Added schema-1.2 serial build receipts with an exclusive workspace build
  lock, an 8 GiB process-tree watcher, exact toolchain/manifest/Mathlib pins,
  and source/log/environment hashes.
- Added Apache-2.0 licensing and citation metadata. The related concept DOI is
  recorded without falsely claiming that this unreleased checkpoint already
  has its own DOI.
