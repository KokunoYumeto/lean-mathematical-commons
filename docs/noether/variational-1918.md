# Noether 1918 variational-theorem formalization map

Work: Emmy Noether, *Invariante Variationsprobleme* (1918), controlled witness
`NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
packet lines 8489–9099.

This is a formalization dependency map, not a translation or critical edition.
It separates Noether's mathematical statements from later physics language and
does not silently repair the German source.

## Explicit results

The packet contains exactly two author-labelled Sätze and no author-labelled
Hilfssatz.

- **Satz I, line 8604.** Invariance under a finite continuous group with
  `ρ` essential parameters gives `ρ` linearly independent combinations of the
  Euler–Lagrange expressions that are divergences. Formula (13), line 8673,
  gives the currents. The source also gives a converse.
- **Satz II, line 8606.** Invariance under a group depending essentially on
  `ρ` arbitrary functions and derivatives through order `σ` gives `ρ`
  differential identities among the Euler–Lagrange expressions through order
  `σ`. Formula (16) is at line 8715. The source also gives a converse.
- **Hilbertsche Behauptung, lines 9027–9029.** After defining improper
  divergence relations, Noether states that currents of a finite group are
  improper exactly when the finite group is contained in an infinite
  invariance group. The translation/energy specialization is at line 9049.

First integrals, general-relativity applications, field equations,
conservation-law terminology, and energy-component language elsewhere in the
packet are consequences, examples, or interpretations—not additional labelled
theorems.

## Source qualifications that must become assumptions

- Functions are analytic, or continuous and differentiable as often as needed
  (line 8511).
- Transformations are invertible, preserve the numbers of independent and
  dependent variables, and may depend on derivatives (line 8515).
- Action invariance is equality over every real domain and its transformed
  domain (line 8521).
- Variations and the required boundary derivatives vanish, while remaining
  arbitrary in the interior (lines 8533 and 8714).
- Parameters and arbitrary functions are essential (line 8513); trivial
  infinitesimal transformations are removed (line 8665).
- The Satz I converse divides by the density and leaves closure for
  derivative-dependent transformations open (lines 8732–8744).
- The Satz II converse invokes Lie integration and retains corresponding
  derivative-dependent qualifications (lines 8829–8843).

The last two points are why the ledger marks the unqualified converse clauses
`BLOCKED_SOURCE`, rather than encoding a stronger iff than the paper supports.

## Pinned Mathlib anchors

- `ae_eq_zero_of_integral_contDiff_smul_eq_zero`
- `Measure.eq_of_ae_eq`
- `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable`
- `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`
- `hasFDerivAt_integral_of_dominated_of_fderiv_le`
- `is_const_of_deriv_eq_zero`
- `LieGroup`, `ContMDiffSMul`, and
  `exists_isMIntegralCurveAt_of_contMDiffAt`

The promoted Lean lemma composes the first two anchors to turn test-function
orthogonality into pointwise zero for a continuous coefficient. It is a
supporting `NEW_PACKAGING` result, not Satz II.

## Smallest honest dependency graph

```text
Mathlib differentiation + integration + test functions
        |
        +-- finite jets, total derivatives, prolongation          [missing]
        +-- action/Lagrangian + Euler operator + boundary current [missing]
        +-- finite/gauge infinitesimal symmetry structures        [missing]
                         |
               first variational identity
                         |
          +--------------+------------------+
          |                                 |
   Satz I forward                  formal-adjoint IBP
          |                                 |
   on-shell conservation             fundamental lemma
                                            |
                                    Satz II forward

Converses additionally need generator integration, group closure,
derivative-dependent transformations, and quotients by trivial symmetries.
The Hilbert claim additionally needs conservation laws modulo trivial currents
and Euler–Lagrange terms.
```

The first realistic theorem milestone is the forward, fixed-domain,
first-order, vertical finite-symmetry case. Coordinate-changing,
derivative-dependent, arbitrary-function, and converse coverage should be
added only after their infrastructure and source assumptions are explicit.
