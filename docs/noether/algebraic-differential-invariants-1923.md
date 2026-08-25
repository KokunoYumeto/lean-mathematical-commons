# Noether 1923: algebraic and differential invariants

## Provenance and formalization scope

- Work: P23, *Algebraische und Differentialinvarianten*.
- Publication: *Jahresbericht der Deutschen Mathematiker-Vereinigung* 32
  (1923), pp. 177–184; report of Emmy Noether's Leipzig lecture of
  18 September 1922.
- Controlled source: lines 13534–13654 of witness
  `NOETH-DE-AUTH-v052-20260815` / `ED0014_R785`.
- Witness SHA-256:
  `EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`.
- Baseline: Lean 4.31.0; Mathlib `v4.31.0`, commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

The paper is a survey organized around Hilbert's arithmetic method. Its five
numbered algebraic statements are reported ingredients of that method, not
five uniformly new Noether theorems. The last section sketches Noether's
reduction of differential invariants to algebraic invariant theory. The
formalization ledger must therefore distinguish exact commutative-algebra
substrate from invariant-theory gaps, later-false general expectations, and a
differential reduction theorem whose hypotheses are compressed.

## Status vocabulary

- `MATHLIB_EXACT`: the modern theorem or direct constituent is already in
  pinned Mathlib.
- `MATHLIB_MODERN_FORM`: Mathlib has the modern concept or a more standard
  formulation, not the source's complete claim.
- `NEW_PACKAGING`: existing results should yield the source-shaped theorem
  after a bounded wrapper proof.
- `GAP_CANDIDATE`: a missing but well-motivated theorem or construction.
- `DEFERRED_INFRASTRUCTURE`: substantial representation, jet, differential,
  or effective-algebra infrastructure must come first.
- `BLOCKED_SOURCE`: the historical statement lacks enough hypotheses for a
  unique safe Lean declaration, or is explicitly posed as open.

## Algebraic invariant-theory inventory

| Source | Mathematical content | Coverage | Exact boundary |
|---|---|---|---|
| 13554–13572, (1)–(3) | General-linear change of variables, induced coefficient action, and determinant-weight relative invariants | `GAP_CANDIDATE` | `GL`, linear representations, polynomial evaluation, determinants, and invariant elements exist. A reusable action on coefficient tensors and the semi-invariant equation of weight `rho` still need packaging. `det != 0` must be represented by membership in `GL` or localization, not a bare proposition over an arbitrary ring. |
| 13573 | Reduction to rational/integer coefficients and to components homogeneous in every coefficient row | `MATHLIB_MODERN_FORM` / `NEW_PACKAGING` | Graded and multigraded polynomial decompositions exist in modern form. Descent from an arbitrary number field to rational or integral coefficient invariants needs the precise scalar-extension statement. |
| 13577 | Equal weights are closed under addition; restricting to determinant one combines weight spaces into a homogeneous invariant domain | `NEW_PACKAGING` | Weight-space multiplication and the restriction from `GL` semi-invariants to `SL` invariants are representation-theoretic wrappers. The claim that these exhaust all restricted invariants needs the intended grading and base-field hypotheses. |
| 13581–13587 | Ideals in rings of integers and finite ideal bases; extension of the ideal definition to arbitrary domains | `MATHLIB_EXACT` in modern form | `Ideal` and finite generation under Noetherian hypotheses cover the content. For number rings, the Dedekind/Noetherian infrastructure supplies finite generation. The source's three clauses omit the explicit zero/nonempty clause required by a modern definition. |
| 13589–13600, theorem 1 | Every ideal in a polynomial ring over a “Rationalitätsbereich” has a finite basis; hence every system generates a finitely generated ideal | `MATHLIB_EXACT` | `Polynomial.isNoetherianRing`, `MvPolynomial.isNoetherianRing`, and `Ideal.fg_of_isNoetherianRing` give the modern Hilbert-basis theorem. Passing from an arbitrary set to its generated ideal is definitional packaging. |
| 13591, theorem 2 | A homogeneous polynomial subdomain is finitely generated as an algebra iff it satisfies the finite ideal-basis property | `GAP_CANDIDATE` | The two implications require a source-specific homogeneous-subalgebra theorem. General Noetherian and finite-type results do not automatically identify the exact grading and coefficient hypotheses compressed here. |
| 13592–13600, theorem 3 | An ambient-polynomial ideal basis of an invariant ideal can be replaced by invariant coefficients | `GAP_CANDIDATE` with promoted support | The abstract coefficient-replacement step is now proved for an additive retraction that fixes invariant elements, lands in invariants, and commutes with right multiplication by invariant generators. Construction of Hilbert/Fischer's `Omega`/Reynolds operator for the general-linear action still needs reductivity and characteristic hypotheses. |
| 13603, theorem 4 | A polynomial subdomain is finitely generated iff it contains a finitely generated subdomain over which it is integral; generators are completed by a fundamental system of integral elements | `BLOCKED_SOURCE` / `GAP_CANDIDATE` | The converse is not a bare theorem about arbitrary integral extensions: an integral algebra can fail to be module-finite without finite-type hypotheses. The source invokes a rational-basis result and its polynomial-subring setting. Those suppressed hypotheses must be reconstructed before formalization. |
| 13604–13606, theorem 5 | For every polynomial ideal `a`, one exponent `r` works for every ideal `b` vanishing on all zeros of `a`, so that `b^r` is divisible by `a` | `NEW_PACKAGING` | In modern terms, `b <= radical a` implies `b^r <= a` for one `r` depending only on `a`. Nullstellensatz/radical semantics plus finite generation of `radical a` provide the ingredients; a uniform ideal-power wrapper is the best immediate theorem target. |
| 13607 | A finite set defining the invariant nullcone gives an integral finite subalgebra; degree and cardinality bounds depend only on the degrees of the ground forms | `GAP_CANDIDATE` | The nullcone criterion needs geometric invariant theory, and the asserted effective degree bound needs substantially more than Hilbert-basis existence. |
| 13609 | Hentzelt's computable coefficient-independent bound for the exponent in theorem 5, hence a bound for degrees in an invariant basis | `DEFERRED_INFRASTRUCTURE` | This is effective commutative algebra. The report gives no formula in this passage; it depends on Hentzelt's separate manuscript and should not be reconstructed from the survey alone. |
| 13611 | Finite-generation results for invariants of subgroups, including orthogonal, affine, motion, semi-invariant, and translation cases | `GAP_CANDIDATE` | These are attributed survey results with representation- and characteristic-specific hypotheses. The paragraph explicitly says the general reach of the reduction method was unresolved and that the strengthened ideal-basis property can fail for subgroups. |
| 13613 | For a finite group, coefficients of the Galois resolvent give a distinguished integral basis of invariants | `MATHLIB_MODERN_FORM` / `GAP_CANDIDATE` | Finite-group orbit products and integrality of invariant extensions have modern substrate. The explicit resolvent-coefficient generating set and its relation to the local fixed-ring finite-type theorem need a source-shaped construction. |
| 13615 | Hilbert basis over the integers; persistence of theorem 2; integral finite generation for binary invariants and finite-group invariants | mixed | The integer polynomial-ring Hilbert basis theorem is `MATHLIB_EXACT`; the binary-form result and its bracket/linear-factor argument remain a `GAP_CANDIDATE`; finite-group integral invariants have modern integrality and finite-type ingredients but need the integral specialization. |

## Differential-invariant inventory

| Source | Mathematical content | Coverage | Exact boundary |
|---|---|---|---|
| 13617–13636, (4)–(5) | Coordinate changes act triangularly on higher differentials and coefficient jets; all symbols are first treated as independent indeterminates | `DEFERRED_INFRASTRUCTURE` | A faithful implementation needs finite-order jet coordinates, the chain rule/Faà di Bruno action, invertibility of the first derivative, and a distinction between formal variables and later evaluation on smooth functions. |
| 13638–13644 | Replace higher differentials by polarized Euler–Lagrange expressions and coefficients of normal forms of higher variations; the resulting objects transform under ordinary induced linear actions | `GAP_CANDIDATE` / `DEFERRED_INFRASTRUCTURE` | This is Noether's reduction theorem. Its algebraic target is clear, but the source does not provide a typed finite-order statement, the required regularity/nondegeneracy hypotheses, or an induction controlling all higher variations. |
| 13642–13646 | The forms `[Omega_i]` and their covariant derivatives furnish algebraic coefficient tensors; the series stops at `Omega_alpha` for degree `alpha`, and `Omega_2` is the Riemann curvature form | `GAP_CANDIDATE` | The finite truncation may become a graded-degree lemma after the variation algebra is defined. Identifying `Omega_2` with Mathlib's curvature needs the coordinate/abstract connection bridge. |
| 13646 | Normal coordinates reduce arbitrary coordinate transformations to general-linear transformations at a point | `MATHLIB_MODERN_FORM` / `DEFERRED_INFRASTRUCTURE` | Manifold and connection APIs provide modern vocabulary, but the source-level reduction needs a normal-coordinate existence theorem and a jet naturality statement tailored to the invariant construction. |
| 13648 | Ask whether the reduction theorem persists when a connection/transport law, rather than a variational problem, defines the group | `BLOCKED_SOURCE` | This is explicitly a historical open question. The text reports only lowest-order calculations by Weitzenböck and says that a general approach was missing; it must not enter the theorem ledger as an asserted result. |

## Exact pinned Mathlib anchors

The strongest exact coverage in this paper is commutative algebra, not the
invariant or differential reduction machinery:

- `Polynomial.isNoetherianRing` and `MvPolynomial.isNoetherianRing` provide
  the Noetherian polynomial-ring instances used by theorem 1.
- `Ideal.fg_of_isNoetherianRing` turns those instances into finite ideal
  bases.
- `Ideal.radical`, ideal powers, zero-locus/vanishing-ideal APIs, and
  Nullstellensatz results provide the constituents for the uniform-exponent
  wrapper in theorem 5.
- Group representations, invariant submodules, `GroupAlgebra.average`, and
  representation averaging provide the finite-group version of the
  coefficient-projection idea behind theorem 3. They do not cover Hilbert's
  general-linear `Omega` process without added hypotheses.
- `AddMonoidHom.map_sum` supplies the finite-sum substrate for the promoted
  theorem-3 support. The local declaration assumes, rather than postulates,
  the projection's fixed-point, range, and invariant-factor laws.
- Polynomial grading, `GL`, `SL`, determinants, and scalar-extension APIs are
  substrate for (1)–(3), but no existing declaration should be cited as the
  complete determinant-weight relative-invariant theory described here.

The highest-confidence addition, theorem 5, is now promoted in modern ideal
language:

```text
for a finitely generated ideal b,
  b <= radical a  ->  exists r, b ^ r <= a.
```

In a Noetherian polynomial ring, finite generation can then make the exponent
uniform over the generators of `b`. To match the literal source's stronger
wording—one `r` for every such ideal `b`—the proof should instead choose a
power of the finitely generated ideal `radical a` contained in `a`; monotonicity
then handles every `b <= radical a`. This is a wrapper theorem, not a new
Nullstellensatz. The canonical module also contains three theorem-3 support
declarations: passage of an additive map through a finite coefficient sum,
replacement of coefficients by a retraction, and existence of invariant
coefficients when the retraction lands in invariants. These do not construct
the retraction.

The canonical module
`MathematicalCommons/Noether/AlgebraicDifferentialInvariants1923.lean`
contains both the abstract uniform radical-power theorem and the source-shaped
zero-locus specialization. Its Lean 4.31 graph check exited zero with empty
stderr, unchanged source, and a 1,405,575,168-byte observed peak under the
4.5 GiB watcher. The two radical/zero-locus declarations report `propext`,
`Classical.choice`, and `Quot.sound`; the three retraction declarations report
only `propext` and `Quot.sound`. Receipt
`artifacts/build/MathematicalCommons-Noether-AlgebraicDifferentialInvariants1923-20260825T0400290494887-4afb1564.module.receipt.json`.

## Canon QA and historical semantics

No controlled German was changed during this audit. The following constraints
must be attached to any formal statements:

- The ideal definition at lines 13581–13585 gives closure under subtraction
  and scalar multiplication but does not explicitly require `0` or
  nonemptiness. This is authorial shorthand; use Mathlib's `Ideal`, not a
  literal possibly-empty predicate.
- `Rationalitätsbereich` at line 13590 is historical coefficient-field
  language and does not necessarily mean the field `Q`. The formal theorem
  should quantify over the appropriate field or Noetherian coefficient ring.
- `endlicher Integritätsbereich` at lines 13579, 13600, and 13603 means a
  finitely generated algebra/domain. It does **not** mean a ring with finitely
  many elements.
- Historical ideal divisibility runs opposite to inclusion. In theorem 5,
  “`b^r` is divisible by `a`” is to be normalized as `b^r <= a`; this direction
  should be stated explicitly rather than inferred from modern prose.
- `D != 0` at lines 13557 and 13636 expresses invertibility of a change of
  variables after passing to a field or localization. Over a general base
  ring, nonzero determinant alone does not produce an element of `GL`.
- The “relatively integral functions” question at line 13613 is the historical
  Hilbert-fourteenth-problem setting. It was open in 1923 and is false in full
  generality; the paragraph reports partial finite-group evidence, not a
  theorem for arbitrary subgroups.
- Line 13648 is grammatically and mathematically a question. Its
  Weitzenböck sentence reports only low-order confirmation, followed by the
  explicit statement that no general approach was known.

These are interpretation and theorem-scope findings, not proposed silent
repairs to the controlled witness.

## Attribution boundaries

- The paper is Noether's authored lecture report, but the three statements at
  lines 13589–13598 are presented as the components of Hilbert's finiteness
  proof.
- The strengthened invariant-ideal step is attributed to Hilbert's
  `Omega`-process and to a newer argument of E. Fischer.
- The effective exponent and invariant-degree bound at line 13609 are
  attributed to Kurt Hentzelt; Noether says she intends to publish his
  posthumous work.
- The finite-group invariant construction at line 13613 and the integral
  binary/finite-group results at line 13615 point to Noether's earlier papers.
- The differential reduction theorem at lines 13638–13646 cites Noether's
  1918 *Invarianten beliebiger Differentialausdrücke*; the normal-coordinate
  quadratic antecedents are credited to Riemann, Lipschitz, Christoffel, and
  Ricci.

## Formalization route

1. Extend the promoted theorem-5 wrapper with useful ideal-family and
   vanishing-ideal corollaries, while keeping Hentzelt's separate effective
   exponent bound out of scope.
2. Add a determinant-weight semi-invariant definition and prove the basic
   weight-space addition, multiplication, and restriction-to-`SL` lemmas.
3. Instantiate the promoted abstract retraction lemma first for finite groups
   in invertible characteristic, then develop the separate reductive/GL
   operator construction without claiming it from the abstract scaffold.
4. Reconstruct the exact hypotheses of theorem 4 before creating any Lean
   declaration; the compressed historical wording is unsafe as a general
   integral-extension theorem.
5. Build finite jet-coordinate actions and the formal variation algebra
   separately. Only then formulate the differential reduction theorem and the
   `Omega_2`/curvature comparison.
