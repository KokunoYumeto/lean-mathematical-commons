# Changelog

## Unreleased

## 0.2.5 — 2026-08-28

- Added the 16-declaration P22 `FirstSmithAnnihilatorBounds` module for the
  finite localized algebra at the opening of Satz VIII, source lines
  13340--13342. Ten generic declarations are `NEW_PACKAGING`; six declarations
  instantiate the actual cutoff-one equation-(24) Smith quotient as
  `FORMALIZED_GAP`. For `A = Ann(G₁*/M₁*) = ⋂ᵢ(eᵢ)` and
  `D = ∏ᵢeᵢ`, the module proves `(D) ≤ A`, `A^ρ ≤ (D)`, the two principal-
  generator divisibilities, and radical equality without assuming that
  Mathlib's selected coefficients are divisibility ordered. It does not
  identify `D` with primitive `R^(i)` or the annihilator generator with
  normalized `E^(i)`. The 14,013-byte source has SHA-256
  `417314B11EE176E90D365FA706EE01B0F48A6BB0A05293A88339CCF693880292`;
  its clean 7,303-byte
  [receipt](artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstSmithAnnihilatorBounds-20260828T2245349715763-862933b6.module.receipt.json)
  has SHA-256
  `40BE879598DEAFCEDA0C9BBC8B8FD8437E46062F0D0C164E7B01F0002C52CC37`
  and records a 1,402,142,720-byte peak.
- Sealed the finite Smith-annihilator cluster with the 6,826-byte
  [claim receipt](artifacts/build/claim-P22-first-smith-annihilator-bounds-20260828T2248235911582-32a08ca0.json),
  SHA-256
  `E39F795AE5CD93B03FA7F29182AB70C347B77E3E59DE424E1B9B6C94E2682421`,
  and the 3,405-byte
  [46-target graph checkpoint](artifacts/build/module-graph-checkpoint-20260828T2248235911582-32a08ca0.json),
  SHA-256
  `23A27DD8B7B1328F6BDADC008F5E898B12D61872258F65B690F6F40A6AAE8FDE`.
  P22 now totals 511 declarations across its base and 29 support modules, with
  47 machine-readable ledger records and 526 declaration references.
- Added the eight-declaration P22 `FirstSmithGroundReciprocity` module for
  Satz II and equation (5), source lines 12815--12844. Six generic declarations
  are `NEW_PACKAGING`: they distinguish the module-valued quotient `M / J` from
  the ideal-valued scalar colon, reduce a principal quotient to a scalar
  preimage, and prove finite diagonal reciprocity. Two declarations are
  `FORMALIZED_GAP` instances for the actual localized cutoff-one pair. Under
  the explicit hypothesis that every selected Smith coefficient divides
  `eᵢ`, they prove both `M₁*/G₁* = (eᵢ)` and
  `G₁* = M₁*/(eᵢ)`. No canonical ordering or normalization is inferred.
  The 9,122-byte source has SHA-256
  `B34074BD5D298D53470B576CD322A3E1C44D7FC265B10480D35E95F213A52A07`;
  its clean 7,301-byte
  [receipt](artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstSmithGroundReciprocity-20260828T2217329496419-78b62eaf.module.receipt.json)
  has SHA-256
  `D1D61114AC63068550FB3B51EF4DE1C44BC3B02F0967F50D147BFCF96D4B16C9`
  and records a 1,380,622,336-byte peak.
- Sealed the reciprocal-ground-module cluster with the 6,776-byte
  [claim receipt](artifacts/build/claim-P22-first-smith-ground-reciprocity-20260828T2221155880785-bb27cb08.json),
  SHA-256
  `C7648327017131D30B5801A09F4E08F0F3E5A07C3FD7F6B4E70399607781A6A0`,
  and the 3,334-byte
  [45-target graph checkpoint](artifacts/build/module-graph-checkpoint-20260828T2221155880785-bb27cb08.json),
  SHA-256
  `24BA677DFBB473A7A09505A47DF00347DB1B0F2C9EA076180412D5C5BE5BF509`.
  At that checkpoint P22 totaled 495 declarations across its base and 28
  support modules, with 45 machine-readable ledger records and 505 declaration
  references.

## 0.2.4 — 2026-08-28

- Added the 35-declaration P22 `FirstSmithScalarQuotients` module for the
  displayed scalar module quotients following equation (24), source lines
  13164--13179. Fifteen generic finite-filtration and product-tail declarations
  are `NEW_PACKAGING`; the 20 declarations for the actual localized cutoff-one
  Smith pair and its arbitrary/countable common tail are `FORMALIZED_GAP`. The
  historical slash is interpreted as the scalar colon ideal
  `A.colon (B : Set E)`: adjoining one `ηᵢ` yields `(eᵢ)` unconditionally,
  whereas quotienting by the whole ground module yields the infimum of the
  remaining principal coefficient ideals. Its reduction to one `(eᵢ)` requires
  the explicit hypothesis that all remaining coefficients divide `eᵢ`. No
  canonical divisibility ordering, norm/resultant identification, or
  historical-tail identification is asserted. The 34,313-byte source has
  SHA-256
  `D65B09A006E97F4B6F32FA50BC064BF401811069382CB2BA08DD5CB424BA7703`;
  the green 7,285-byte
  [receipt](artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstSmithScalarQuotients-20260828T2052403988381-386b0cec.module.receipt.json)
  has SHA-256
  `75EA954635F63B2A23AEC4CF866701006CEFA3A14F4FED37816A724EFB4D4593`
  and records a 1,462,034,432-byte peak. P22 now totals 487 declarations across
  its base and 27 support modules, with 43 machine-readable ledger records.
- Sealed the scalar-quotient cluster with the 7,537-byte
  [claim receipt](artifacts/build/claim-P22-first-smith-scalar-quotients-20260828T2055573367899-6e27c54b.json),
  SHA-256
  `681152AA43FCB326269455A7C38398DC34EF2B5F01A03967C4C8F14B2440A022`,
  and the 3,433-byte
  [44-target graph checkpoint](artifacts/build/module-graph-checkpoint-20260828T2055573367899-6e27c54b.json),
  SHA-256
  `40889076C3B15D3F580D1FC5AA617A2D71890EE477C4C366E41D95A1BC6B98D3`.
- Added the 37-declaration P22 `FirstSmithCommonTail` module for source lines
  13155--13173. Four generic product-head quotient helpers are `NEW_PACKAGING`;
  the 33 source-instantiated declarations are `FORMALIZED_GAP`. The module
  freely adjoins an arbitrary Finsupp tail to the actual localized cutoff-one
  pair, specializes it to the printed countable `ζ` sequence, extends both
  selected bases, proves coefficient `1` on every tail coordinate, cancels the
  common tail, and recovers the finite cyclic quotient. It does not identify
  this model with a separately constructed/localized historical unbounded
  `ζ`-module, assert divisibility ordering, or form an infinite determinant.
  The 25,766-byte source has SHA-256
  `6A2AC9FC7F0550676DA302581E54FBC244DEC400D802E2415D190231A300245A`;
  the green 7,240-byte
  [receipt](artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstSmithCommonTail-20260828T2012238968138-efd307ef.module.receipt.json)
  has SHA-256
  `9812CF23D7DFACC4E4D58AB573549C60255D0F2A2F85B021953E5067A211A6F9`
  and records a 1,421,987,840-byte peak. P22 now totals 452 declarations across
  its base and 26 support modules, with 41 machine-readable ledger records.
- Sealed the common-tail cluster with
  [claim receipt](artifacts/build/claim-P22-first-smith-common-tail-20260828T2016152269335-1092d717.json)
  SHA-256
  `D2610B6B73598E372BCEE8FE6C8AC58E14763ABB9E43989928B0431C3860FAEF`
  and a [43-target graph checkpoint](artifacts/build/module-graph-checkpoint-20260828T2016152269335-1092d717.json)
  SHA-256
  `6DE844FF9A0189582515F29B4A405799694783CAD4DE50E3F121D70C62E9EBDD`.
- Prepared the coherent public `noether-pilot-0.2.4` checkpoint under the
  living concept DOI `10.5281/zenodo.21129945`; its immutable release DOI is
  `10.5281/zenodo.22149791`. GitHub and Zenodo carry the same three release
  assets and are anonymously rehashed after publication.

## 0.2.3 — 2026-08-28

- Added the sixteen-declaration P22 `FirstGroundModule` module. It formalizes
  Definition I's nonzero-scalar saturation as the least ground module, proves
  exact cutoff-one multiplier transport through `finSuccEquiv`, and closes line
  13162 with `G₁* = saturation(M₁*)` plus the source-facing membership and
  cancellation forms. This is `FORMALIZED_GAP`.
- Added the ten-declaration P22 `FirstGroundModuleTorsion` module. It
  characterizes saturation by torsion of the relative quotient, derives equal
  cardinal rank and `finrank`, records Satz I's same-rank theorem, proves bounded
  finite generation, and supplies the unlocalized full-rank premise for the
  stage-one pair consumed by the new source-faithful localization.
- Added the 25-declaration P22 `FirstGroundModuleLocalization` module. It uses
  exactly `B = P[x₃,…]`, `A = B[x₂]`, `K = Frac(B)`, and `R = K[x₂]`, so
  only the late-variable coefficients are inverted and `x₂` remains the
  polynomial variable. It transports the cutoff-one saturation identity and
  equal `finrank` to `R`. The green
  [receipt](artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstGroundModuleLocalization-20260828T1711488036548-b4e9f21a.module.receipt.json)
  records a 1,408,970,752-byte peak, and the promoted claim is pinned
  [here](artifacts/build/claim-P22-first-ground-module-localization-20260828T1741336133599-43d2ef8c.json).
- Added the 13-declaration P22 `FirstSmithPairedQuotient` module: the actual
  finite cutoff-one equation-(24) instance over `R`. It provides selected Smith
  bases and coefficients, the diagonal relation, denominator membership, the
  cyclic-quotient decomposition, and the selected-basis determinant product.
  The green
  [receipt](artifacts/build/MathematicalCommons-Noether-PolynomialIdealsAndResultants1923-FirstSmithPairedQuotient-20260828T1726213885481-badb6014.module.receipt.json)
  records a 1,391,661,056-byte peak, and the promoted claim is pinned
  [here](artifacts/build/claim-P22-first-smith-paired-quotient-20260828T1741336133599-43d2ef8c.json).
  Divisibility ordering, the infinite `ζ` tail and unit factors, determinant
  norm/resultant identification, primitive normalization and choice
  independence, and later stages remain explicit gaps. P22 now totals 415
  declarations across the base and 25 support modules, with 39 ledger records.
- Expanded the maintained graph to 42 targets (40 theorem/support modules and
  both umbrellas). The new modules exited zero with empty stderr, zero warnings,
  zero `sorry`, and no new axioms beyond Lean's standard axioms; both umbrellas
  also exited zero with empty stderr under 2.5 GiB caps. Checkpoint
  [`20260828T1741336133599-43d2ef8c`](artifacts/build/module-graph-checkpoint-20260828T1741336133599-43d2ef8c.json)
  is 3,670 bytes with SHA-256
  `BD1C021476EEFDC21CE77CC74144492BE73AD471A8913961E0A9CDDB7DBDF5F6`;
  its incremental peak was 1,917,771,776 bytes and the checkpoint-chain peak
  remains 1,922,387,968 bytes under the 3 GiB worker envelope.

## 0.2.2 — 2026-08-28

- Added the six-declaration P22 `RegularPairedQuotient` module. For a supplied
  regular polynomial in a denominator ideal `M ≤ G`, it specializes equations
  (22)--(23) to identify `G/M` with the quotient of the bounded coefficient
  modules, proves the paired quotient finite, and supplies a bounded numerator
  representative for every class. This is `NEW_PACKAGING` of existing Mathlib
  and local infrastructure, not new mathematics; line 13162's ground-module
  characterization and later stages remain open.
- Added the eleven-declaration P22 `FirstGroundPairedQuotient` module. It fixes
  the source indexing `g₀ = cutoff 0`, `g₁ = cutoff 1`, recovers the unit-ideal
  base case, and instantiates the finite bounded quotient for the transported
  cutoff-one ground ideal. This is an ideal-level `NEW_PACKAGING` counterpart.
- Added the twenty-declaration P22 `FirstLinearFormModules` module. It models the
  first finite `ξ` coordinates and common `ζ` tail, realizes the ground/original
  pair as the actual cutoff-one ideals under a supplied regular member, cancels
  the common tail, and connects the coordinate, ideal, and bounded quotients.
  This is `FORMALIZED_GAP`; line 13162's ground-module characterization remains
  open.
- Added the nine-declaration P22 `SmithPairedQuotient` module. It packages
  Mathlib's finite-free PID Smith bases, diagonal coefficients, cyclic quotient
  decomposition, common-tail composition, and selected-basis determinant
  product. It is generic `NEW_PACKAGING`, not the historical localized
  `G₁*/M₁*` instantiation and not a canonical divisibility-ordered
  elementary-divisor theorem.
- Expanded the maintained graph to 38 targets (36 theorem/support modules and
  both umbrellas). Both added modules and both umbrellas exited zero with empty
  stderr under 2.5 GiB caps; the checkpoint-chain peak is 1,922,387,968 bytes
  under the strict 3 GiB worker envelope.

## 0.2.1 — 2026-08-27

- Added the six-declaration P22 `CommonTailQuotient` module. It gives a
  source-facing modern form of the representative-system isomorphism after
  equation (23): if `M ≤ G` and a common tail `T` is disjoint from `G`, then
  `(G ⊔ T)/(M ⊔ T) ≃ G/M`, and every enlarged class has a representative from
  `G`. This is classified as `NEW_PACKAGING` of Mathlib's existing second
  isomorphism theorem, not new mathematics.
- Expanded the maintained graph to 34 targets (32 theorem/support modules and
  both umbrellas). The new module and both umbrellas exited zero with empty
  stderr under 2.5 GiB caps; the checkpoint-chain peak remains 1,919,508,480
  bytes under the strict 3 GiB worker envelope.

## 0.2.0 — 2026-08-27

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
- Added 27 equation-(12) finite-descent declarations, bringing that module to
  62 declarations and P22 to 283 canonical declarations. The generic transform
  is recovered from a polynomial-parameter transform; one characteristic-zero
  parameter assignment preserves a finite family of regularity witnesses; and
  every specialization is identified with an actual lower-unitriangular
  algebra equivalence. Thus every nonzero ideal has a finite specialized
  coordinate transform containing a first-variable regular member.
- Added the 16-declaration `RegularQuotient` module for P22's equation-(21)
  representative system and the reduction following equation (23). It proves
  that the quotient by a supplied regular polynomial's principal tail is free
  finite on the `k` bounded coefficient classes, and that every containing
  ideal maps exactly to its bounded coefficient module. P22 now has 299
  canonical declarations across the base and sixteen support modules, with 30
  claim/definition records.
- Published Zenodo release DOI `10.5281/zenodo.22132542` under the existing
  concept DOI `10.5281/zenodo.21129945`; its coherent source archive is mirrored
  as an identical public GitHub release asset and Zenodo deposit.
- Expanded the maintained graph to 32 targets (30 theorem/support modules and
  both umbrellas). The completed module and umbrellas all exited zero with
  empty stderr under 2.5 GiB caps; the checkpoint-chain peak remains
  1,919,344,640 bytes under the strict 3 GiB worker envelope.
- Expanded the maintained graph to 33 targets (31 theorem/support modules and
  both umbrellas). The new module and both umbrellas exited zero with empty
  stderr under 2.5 GiB caps; the checkpoint-chain peak is 1,919,508,480 bytes
  under the strict 3 GiB worker envelope.
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
