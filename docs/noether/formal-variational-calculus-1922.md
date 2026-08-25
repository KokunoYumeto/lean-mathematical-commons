# Noether 1922: formal variational calculus and differential invariants

## Provenance and formalization scope

- Work: P21, *Formale Variationsrechnung und Differentialinvarianten*.
- Publication: entry 28 in R. Weitzenböck's encyclopedia article,
  *Encyklopädie der mathematischen Wissenschaften* II, 3 (1922),
  pp. 68–71; the source explicitly says that this entry is by Emmy Noether.
- Controlled source: lines 12610–12699 of witness
  `NOETH-DE-AUTH-v052-20260815` / `ED0014_R785`.
- Witness SHA-256:
  `EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`.
- Baseline: Lean 4.31.0; Mathlib `v4.31.0`, commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

This is an expository encyclopedia contribution, not a paper with a sequence
of newly proved numbered theorems. It explains how formal variational
calculus produces differential invariants, specializes the construction to a
quadratic differential form, and ends by summarizing Noether's two 1918
theorems. A source-faithful formalization therefore needs to separate the
displayed algebraic identities from analytic variational claims and from
historical reports of results due to Riemann, Lipschitz, Christoffel, Ricci,
Levi-Civita, Weyl, and Noether herself.

## Status vocabulary

- `MATHLIB_EXACT`: the modern statement or a direct constituent is already
  present in pinned Mathlib.
- `MATHLIB_MODERN_FORM`: Mathlib has the abstract modern object, but not the
  source's coordinate formula or historical convention.
- `NEW_PACKAGING`: the mathematics is available, but a source-shaped wrapper
  or finite-index calculation is still needed.
- `GAP_CANDIDATE`: a meaningful missing theorem or construction can be stated
  after fixing the source model.
- `DEFERRED_INFRASTRUCTURE`: formal jets, higher variations, local analysis,
  or another substantial prerequisite is missing.
- `BLOCKED_SOURCE`: the passage does not determine a unique formal statement,
  or reports a result whose hypotheses are too compressed to encode safely.

These labels describe the boundary of a source-linked formalization. They do
not claim that Mathlib lacks every theorem adjacent to the subject.

## Result inventory

| Source | Mathematical content | Coverage | Formalization boundary |
|---|---|---|---|
| 12622–12633, (140) | A regular homogeneous Lagrangian gives Euler–Lagrange expressions `2 psi_i = d/dt (partial f / partial x'_i) - partial f / partial x_i`, transforming contragrediently | `DEFERRED_INFRASTRUCTURE` | A rigorous theorem needs a typed Lagrangian, differentiability and endpoint hypotheses, first variation, integration by parts, and a representation-level transformation law. The source instead treats all differentials formally. |
| 12633–12639 | Lagrange's “central equation,” an integration-by-parts identity defining the `psi_i` without an integral | `GAP_CANDIDATE` | Primary print resolves the spurious primes to `f(dx)` and `delta f`; a polynomial-jet identity still needs typed `d`, `delta`, and `psi_i(d,d)`. |
| 12639–12643 | Quadratic specialization for `sum g_ik dx_i dx_k` | `NEW_PACKAGING` | Once finite indices, symmetry of `g`, and formal derivations are defined, this should be a finite-sum product-rule calculation. It is not yet the curvature theorem. |
| 12644–12656, (141) | Polarize by replacing `d` with `d + lambda delta`; the three coefficients show that `psi_mu(d,delta)` and its diagonal cases are contragredient vectors | `NEW_PACKAGING` / `GAP_CANDIDATE` | Primary print confirms capital `D` as an implicit independent outer formal differential. Polynomial coefficient comparison is routine after `d`, `delta`, and `D` are typed separately. |
| 12656–12665, (142) | Compute the polarized Euler expression, raise its index with `g^(sigma mu)`, obtain Christoffel symbols, and recover the geodesic equation `p^nu(d,d)=0` | `GAP_CANDIDATE` | Matrix inversion, finite sums, and polarization are available ingredients. The coordinate Christoffel calculation and its equivalence with an abstract geodesic equation need a metric, nondegeneracy, and a connection bridge. |
| 12667–12671, (143) | Eliminate second differentials to define the covariant derivative of a form in one or more differential rows | `MATHLIB_MODERN_FORM` | Pinned Mathlib has abstract covariant-derivative interfaces such as `IsCovariantDerivativeOn` and `CovariantDerivative`; it does not identify Noether's coordinate elimination formula with those objects. That identification is a `GAP_CANDIDATE`. |
| 12673–12687, (144)–(146) | Form the normal form of the second variation, subtract connection terms, and obtain the Riemann–Lipschitz curvature form | `DEFERRED_INFRASTRUCTURE` | A faithful proof needs second and third formal variations, an elimination/substitution calculus that respects order of differentiation, and a coordinate-to-tensor curvature theorem. |
| 12689 | Successive covariant derivatives of the curvature form, together with `f`, generate all differential invariants of a quadratic form; equivalence of the resulting data decides local equivalence | `BLOCKED_SOURCE` / `DEFERRED_INFRASTRUCTURE` | The passage compresses regularity, locality, normal-coordinate, convergence or finite-jet, and group-action hypotheses. Modern curvature-jet reconstruction can guide a later statement, but no theorem should be inferred verbatim from this paragraph. |
| 12691 | Levi-Civita parallel displacement, Weyl's axiomatic connection, and a conformal extension using an additional one-form | `MATHLIB_MODERN_FORM` / `GAP_CANDIDATE` | Abstract connections and covariant derivatives are modern infrastructure. Uniqueness of the source's `p(d,delta)` and the claimed invariant constructions require a separately stated conformal/one-form package. The paragraph itself says the general reduction and equivalence questions were open. |
| 12693 | Noether theorem I: invariance under a group with `rho` essential parameters corresponds to `rho` independent divergences, with converse | `GAP_CANDIDATE` / `DEFERRED_INFRASTRUCTURE` | Pinned Mathlib has no source-level Noether theorem connecting Lie-group variational symmetry, Euler–Lagrange expressions, and conservation laws. This needs manifolds or jets, infinitesimal actions, variational bicomplex data, and boundary-divergence semantics. |
| 12693 | Noether theorem II: invariance under a group depending on `rho` arbitrary functions through order `sigma` corresponds to `rho` differential identities among Euler expressions through order `sigma`, with converse | `DEFERRED_INFRASTRUCTURE` | This is the higher-order gauge-symmetry theorem and needs a formal differential-operator or jet-bundle framework before a source-shaped statement is meaningful. |
| 12693 | Euler–Lagrange expressions become relative invariants, yielding an invariant-generating process | `GAP_CANDIDATE` | This should follow from a precise naturality theorem for the Euler operator; the representation weight and transformation convention are not specified in the excerpt. |

## Exact and modern Mathlib boundary

Pinned Mathlib already supports finite sums, multilinear algebra, bilinear
forms, smooth manifolds, vector bundles, connections, and abstract covariant
derivatives. In particular, its `IsCovariantDerivativeOn` and
`CovariantDerivative` APIs provide a modern home for the operation discussed
at lines 12667–12671. Those APIs do **not** by themselves prove:

- the formal central identity (12635–12638);
- the polarized coordinate formulas (141) and (142);
- equivalence of Noether's elimination operation with a covariant derivative;
- the second-variation construction of curvature in (144)–(146);
- generation or completeness of differential invariants; or
- either direction of Noether's first or second theorem.

The lowest-cost formal result is the finite-index polarization calculation in
the quadratic case. The highest-value result is a naturality theorem for an
Euler operator, because it is the bridge both to the contragredient
transformation law at line 12633 and to the relative-invariant claim at line
12693. Neither should be labeled as coverage of Noether's theorems until the
variational symmetry and divergence semantics are present.

## Canon QA and interpretation constraints

No controlled German was changed in this repository. Primary-witness review
has resolved the two formula questions:

- Official print p. 68 has `f(dx)` at line 12622 and `delta f` at line 12635;
  the primes in ED0014 are transcription errors. Inactive successor ED0020
  corrects them, restoring `f(dx)`, the Hessian of `f`, `f(x')`, and
  `delta f` as one coherent chain.
- Capital `D` throughout (141) is genuinely printed. It is an implicit
  independent outer formal differential/variation, distinct from both `d`
  and `delta`; a faithful formalization must type all three.
- The raised-index notation `p^sigma` at lines 12662–12665 is historical
  coordinate notation. It should not be modeled as an exponent.
- Most importantly, `endliche Gruppe mit rho wesentlichen Parametern` at line
  12693 means a finite-dimensional continuous/Lie group with finitely many
  essential parameters. It does **not** mean a finite-cardinality group. The
  following `unendliche Gruppe` is the historical contrast with a
  function-parameter group.

The remaining points are source-scope and semantic cautions. Existing theorem
records remain bound to ED0014; ED0020 is not treated as active canon here.

## Attribution boundaries

- The entry is explicitly attributed to Emmy Noether at line 12618.
- The variational method and quadratic constructions are reported as work of
  Riemann and Lipschitz, with coordinate and equivalence developments by
  Christoffel, Ricci, Vermeil, and others.
- The geometric interpretation of `p(d,delta)=0` is attributed to
  Levi-Civita; the axiomatic connection discussion is attributed to Weyl and
  related work by Hessenberg and Weitzenböck.
- Only the two general invariant-variational correspondences summarized at
  line 12693 are explicitly tied to Noether's 1918 paper. A formal library
  should preserve those credits rather than presenting every displayed
  coordinate identity as a new Noether theorem.

## Formalization route

1. Define a small algebraic jet language with three typed formal directions
   `d`, `delta`, and `D` and finite coordinate indices, using the resolved
   print readings `f(dx)` and `delta f`.
2. Prove the quadratic central identity and its polarization coefficient by
   coefficient, then derive the Christoffel-coordinate expression (142).
3. Relate the elimination formula (143) to Mathlib's abstract covariant
   derivative and prove a source-shaped naturality statement.
4. Add second variations and prove the curvature formula only after the
   differentiation-before-substitution rule is represented explicitly.
5. Treat the curvature-jet generation claim and the two Noether theorems as
   separate projects. The latter require genuine variational and Lie/gauge
   infrastructure, not just finite-sum algebra.
