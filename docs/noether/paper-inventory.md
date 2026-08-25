# Emmy Noether paper inventory

This document indexes the 43 numbered Emmy Noether work packets in the
controlled cumulative German source. It is the paper-level entry point for the
Noether formalization pilot; theorem-level coverage remains in
[mathlib-coverage.md](mathlib-coverage.md) and
[noether-theorems.tsv](../../metadata/noether-theorems.tsv).

The machine-readable inventory is
[noether-works.tsv](../../metadata/noether-works.tsv).
Open discrepancies reported to the canon owner are also recorded in
[noether-canon-qa.tsv](../../metadata/noether-canon-qa.tsv).

## Scope and source

- Source ID: **ED0014_R785**
- Controlled file:
  C:\Users\Floris\Documents\interlanguage\03_projects\noether\07_german_canon_control\candidates\ED0014\noether.tex
- File declaration: cumulative working revision R785, dated 2026-07-04 at
  source line 1.
- Numbered-work bibliography: source lines 23993–24078.
- Inventory method: top-level work headings, immediately associated
  publication metadata, work-packet boundaries, and the cumulative
  bibliography only.

All line numbers in the TSV are one-based and inclusive. The source spans are
paper-packet locators, not assertions that every line is mathematical prose.
The controlled corpus was not edited. This inventory does not certify the
transcription, typography, translation, completeness, or mathematical
correctness of any source.

## Summary

- **43 numbered works**, with stable IDs P01 through P43 and no numerical gap
  in the cumulative bibliography.
- **24 works are not yet paper-level Mathlib audits.** Nineteen works have partial
  declaration-level audits backed by theorem records: P07 (1916 finite-group
  invariants), P13 (1918 variational problems), P15 (1919 integral invariants
  of binary forms), P16 (1920 series expansion), P17 (1920 noncommutative
  modules, jointly with Werner Schmeidler), P18 (1921 Noether report on
  Hentzelt's elimination theory), P19 (1921 ideal theory), P20 (1922 absolute
  irreducibility), P21 (1922 formal variational calculus), P22 (1923
  Hentzelt--Noether polynomial ideals and resultants), P23 (1923 algebraic and
  differential invariants), P24 (1923 elimination and general ideal theory),
  P25 (1924 elimination and ideal theory), P26 (1924 abstract ideal theory),
  P27 (1925 Hilbert numbers), P28 (1925 group
  characters and ideal theory), P29 (1926 modular invariants), P30 (1927
  abstract Dedekind ideal theory), and P31 (1927 discriminant theorem).
  Each still has explicit open results; `PARTIAL_AUDIT` is not paper
  completion.
- **Four displayed body headings omit the collection number:** P04, P17, P18,
  and P19. Their IDs are grounded in sequence, source comments where present,
  and the cumulative bibliography.
- **Three explicit joint works:** P17 with Werner Schmeidler, P32 with Richard
  Brauer, and P38 with Richard Brauer and H. Hasse.
- **Three attribution-sensitive works:** P18 reports K. Hentzelt’s work; P22
  is Hentzelt’s work edited and freely reworked by Noether; P34 credits B. L.
  van der Waerden’s free elaboration and joint preparation for print.
- **One posthumous source caveat:** P43 was supplied by H. Grell, and its
  source note says that the manuscript after §6.3 apparently still required
  revision.

The TSV separates **coverage_state** from **initial_lean_lane**. A topic lane
is only a routing hint. It must not be read as a claim that Mathlib lacks the
result. Promotion to MATHLIB_EXACT, MATHLIB_MODERN_FORM, NEW_PACKAGING,
GAP_CANDIDATE, FORMALIZED_GAP, BLOCKED_SOURCE, or DEFERRED_INFRASTRUCTURE
requires a declaration-level audit.

## Open canon QA

No reading below has been silently normalized. The following twelve conflicts
across seven works are recorded as **OPEN_CANON_QA** and should be reconciled by
the German canon owner.

| Work | Controlled reading | Comparison or candidate | Source locations |
|---|---|---|---|
| P02 | “u. zwei Tabellen” | “u. eine Tabelle” | 478; 23996 |
| P15 | row-4/row-3 specialization displays only `ξ₁₄ = ξ₁₃` | likely also requires `ξ₂₄ = ξ₂₃`; scan verification required | 9653; compare 9799 |
| P15 | identical monomial displayed for two complementary normalized cases | second display likely lost the complementary case; exact repair needs the scan | 9699 and 9703 |
| P15 | `wᵢ = ωᵢ/h`, later reversed to `ωᵢ = wᵢ/h` | latter should be consistent with `ωᵢ = h wᵢ`; scan verification required | 9882 and 9886 |
| P17 | `ξ-(y/x)η=ξ-a` | likely `ξ-y/x=ξ-a`; because `a=y/x` and the later module is `ξ-y/x` | 11139; compare 11162–11184, 11190, 11205 |
| P17 | quotient contains powers of `y` | likely powers of `η`, which establish infinite `P`-linear dimension | 11141; compare 11205 |
| P17 | cross-reference §12.2 | likely §12.3; scan verification required | 10586; target begins 11137 |
| P17 | bare expression `y log x − ∫φ(y)dy + c` called a common solution | likely an exponential of that expression; scan verification required | 11190–11194 |
| P21 | “Encyklopädie d. math. Wiss. II, 3” | “Encyklopädie d. math. Wiss. III, 3” | 12612; 24034 |
| P23 | “Algebraische und Differentialinvarianten” | “Algebraische und Differentialvarianten” | 13534 and 13540; 24037 |
| P39 | “… zur kommutativen Algebra und Zahlentheorie” | “… zur kommutativen Algebra und zur Zahlentheorie” | 19052; 24069 |
| P40 | displayed title “Nichtkommutative Algebra” | section and bibliography “Nichtkommutative Algebren” | 19149; 19142 and 24071 |

Three P17 items are recorded as source-scope or mathematical-proof review,
not as asserted transcription conflicts:

| Work | Review state | Evidence |
|---|---|---|
| P17 | **REVIEW_STATEMENT_SCOPE** | Satz VIII at 10690 omits the `α ≥ 2` lower bound used at 10696. |
| P17 | **REVIEW_SOURCE_ARGUMENT** | The arbitrary-field setup at 10214 is followed by division by `k−1` at 10437–10440; an idempotent proof may avoid the characteristic issue. |
| P17 | **REVIEW_STATEMENT_SCOPE** | Satz XI is at 10918, while its analytic and regular-locus qualifications follow at 10920–10921. |

Four lower-confidence review cases remain separate from OPEN_CANON_QA:

| Work | Review state | Evidence |
|---|---|---|
| P15 | **REVIEW_BIBLIOGRAPHY** | Line 9841 cites P07 as 1915, while its heading and cumulative bibliography give 1916; this may reflect a non-publication date convention. |
| P15 | **REVIEW_SYMBOL_ORIENTATION** | Line 9821 has `(n,n−1)`, while surrounding variables use `ξ_{n−1,n}`; the sign changes but the stated nonvanishing does not. |
| P33 | **REVIEW_ORTHOGRAPHY** | Body line 16261 has “Grössen”; bibliography line 24057 has “Größen”. This may be an orthographic normalization rather than a defect. |
| P42 | **REVIEW_PAGINATION** | Body line 19947 gives “S. 5–15”; bibliography line 24076 gives “(15 S.)”. Publication pagination must be checked before asserting an error. |

## Primary-witness resolutions received 2026-08-25

The canon owner supplied an append-only, primary-witness-verified decision
packet. ED0015 remains the reported active/public authority; ED0020 is an
inactive successor candidate and is not used to rewrite existing ED0014-bound
theorem provenance.

| Work | Resolution | Formalization effect |
|---|---|---|
| P16 | Formula [9]'s bare equality is print-faithful continuation from `Fᵢ`. | No source block remains; preserve continuation layout in quotations. |
| P18 | `adjungiert ist` is a printed grammatical anomaly; the resultant display is print-faithful staged semantics confirmed by P22; bibliography p. 48 is corrected to p. 101 in ED0020. | P22's exact-range audit now fixes the triangular definitions; preserve Hentzelt/Noether attribution. |
| P21 | Print has `f(dx)` and `δf`, not primed `f`; capital `D` is genuinely printed as an implicit third formal differential. | ED0020 corrects the primes; model `d`, `δ`, and `D` separately. |
| P24 | Reused `c_i/g_i` and the unit-ideal/dimension `−1` convention are printed; `r_a` was corrected to `r_α` in ED0019. | Avoid dummy-name dependence; use the corrected component index after rebase. |
| P25 | Strict `0≤k<n` and historical `Galoisscher Körper` are printed. | Use `k≤n` or `p≠0`; distinguish splitting fields from modern Galois extensions. |
| P27 | Slash notation is the printed historical ideal quotient. | Formalize colon ideals explicitly. |
| P28 | Bare `Charaktere` is printed. | State irreducible-character, splitting, and semisimplicity hypotheses in Lean. |
| P31 | `u` is already introduced; ED0019 corrects seven `R_{\bar a}` glyphs and “nach 1.” to “nach 2.” | These three issues no longer block the arbitrary-order theorem. |

Local custody metadata and verified hashes are in
[`CANON_DECISION_ED0020_20260825.json`](../../sources/noether/CANON_DECISION_ED0020_20260825.json).

## Numbering and attribution notes

- P04 has no displayed “4”; its place is fixed by P03/P05 and bibliography
  item 4.
- P17 has no displayed “17”, but source line 10071 explicitly labels the
  packet Paper 17.
- P18 is marked as Paper 18 at source line 11218. The displayed “1.” at line
  11225 is a conference-session contribution number. Primary publication
  identity fixes its page as 101, not the inherited bibliography's page 48.
- P19 has no displayed “19”; its place is fixed by P18/P20 and bibliography
  item 19.
- P22’s heading names Kurt Hentzelt as author and Emmy Noether as Bearbeiterin.
  It must not be flattened into an uncomplicated sole-authorship record.
- P34’s bibliography lists Noether, while the heading footnote at line 16339
  credits van der Waerden’s free elaboration and their joint preparation for
  print.
- P43 is a posthumous manuscript and duplicates the title of the short 1930
  communication P36; the two records are intentionally distinct.

## Excluded unnumbered material

The cumulative file continues beyond P43, but the following blocks are not
part of the numbered P01–P43 bibliography and therefore are not represented as
numbered rows:

- *Algebra der hyperkomplexen Größen*, a 1929/30 Noether lecture worked out by
  M. Deuring, source lines 21003–23740.
- H. Kapferer, *Notwendige und hinreichende Multiplizitätsbedingungen zum
  Noetherschen Fundamentalsatz der algebraischen Funktionen*, with a joint
  Noether addendum, source lines 23742–23982.

They should receive separate stable IDs only after their bibliographic and
authorship roles are modeled explicitly. The later short-communication,
review, and editorial lists are reference apparatus, not additional numbered
paper packets.
