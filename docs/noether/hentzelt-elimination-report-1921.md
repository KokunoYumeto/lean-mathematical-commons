# Noether's 1921 report on Hentzelt's elimination theory

## Provenance and attribution

- Work packet: P18, controlled lines 11218–11242.
- Verified publication page: J. Ber. d. DMV 30 (1921), p. 101. The inherited
  bibliography's p. 48 identifies a different short notice and is corrected
  only in the inactive ED0020 successor.
- Witness: `NOETH-DE-AUTH-v052-20260815` / `ED0014_R785`, SHA-256
  `EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`.
- Baseline: Lean 4.31.0; Mathlib `v4.31.0`, commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

The heading at line 11225 and Noether's first-person editorial notice at line
11228 make this a conference report on Kurt Hentzelt's dissertation. The main
construction and results are therefore recorded as **Hentzelt claims reported
by Noether**, not as sole-Noether theorems. The final abstract-ideal
interpretation is voiced in Noether's report, but this extract cannot determine
whether that interpretation originated with Hentzelt or with Noether's planned
free edition.

## Claim map

| Source claim | Pinned coverage | State and limitation |
|---|---|---|
| common zeros of every polynomial in an ideal, line 11230 | `MvPolynomial.zeroLocus`, `mem_zeroLocus_iff`, antitonicity | `MATHLIB_EXACT` semantics |
| generic linear coordinate change, line 11230 | `MvPolynomial.bind₁`, `eval₂Hom`, `renameEquiv`, matrices | `BLOCKED_SOURCE`: coefficient extension, determinant localization, and transformed-ideal convention are omitted |
| unique resultant form and triangular product, lines 11232–11236 | ideal membership models the displayed congruence | staged/triangular reading is canon-confirmed; exact definitions must be imported from P22 before this becomes a `GAP_CANDIDATE` |
| resultant form vanishes exactly on the common zero set, line 11238 | zero-locus and Nullstellensatz APIs are modern substrate | canon confirms stagewise resultants/zeros, not one arbitrary hypersurface equation; source-shaped P22 bridge remains open |
| divisor ideal plus equal resultant implies equal ideal, line 11238 | ideal order exists | `BLOCKED_SOURCE`: historical divisibility orientation and normalized equality are unspecified |
| characteristic multiplicity, line 11240 | multiplicity APIs do not define this invariant | `BLOCKED_SOURCE` |
| ideal as a module of linear forms in earlier monomials, line 11240 | `MvPolynomial.basisMonomials` is substrate | `BLOCKED_SOURCE`: base ring, bounded monomials, presentation, and identification are omitted |
| successive factors are norms of ground modules, line 11240 | `Algebra.norm`, determinant norms, and Smith norms are analogies only | `BLOCKED_SOURCE`, later `GAP_CANDIDATE`; this is not automatically `Algebra.norm` |
| primary ideal corresponds to a primary factor of a successive norm, line 11240 | `Ideal.IsPrimary`, radicals, and associated primes supply vocabulary | `BLOCKED_SOURCE`, later `GAP_CANDIDATE`; decomposition, complement, bracket, and norm semantics are absent |

The first row is exact modern semantics, not a formalization of Hentzelt's
resultant construction. Primary-witness review and the later Hentzelt–Noether
paper now fix the high-level meaning as a staged triangular construction. The
next step is therefore to audit P22's definitions rather than guess them from
the compressed report.

## Canon resolution

- The official p. 101 visibly prints singular `adjungiert ist`. It is retained
  as an original grammatical anomaly; P22's plural `sind` is corroboration,
  not evidence of a P18 transcription error.
- The product/ellipsis layout at lines 11232–11238 is print-faithful. P22
  confirms staged resultants and stagewise zeros, so the display must not be
  flattened into a claim that one ordinary hypersurface equals every ideal
  variety.
- Attribution is fixed: P18 is Noether reporting Hentzelt's mathematics; P22
  names Hentzelt as author and Noether as editor/adaptor.

The append-only decision packet is referenced by
`sources/noether/CANON_DECISION_ED0020_20260825.json`. Historical terms such as
`Teiler`, `[Q,L]`, `Komplement`, and `Norm … nach …` remain explicit
source-semantics questions, not presumed transcription defects.
