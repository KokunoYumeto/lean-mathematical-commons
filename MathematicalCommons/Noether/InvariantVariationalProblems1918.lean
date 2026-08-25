/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Emmy Noether, *Invariante Variationsprobleme* (1918)

Controlled source: `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
lines 8489–9099.

This module formalizes one analytic support step used in the proof of Satz II,
not either of Noether's two main theorems. At lines 8714–8720, arbitrary test
functions (with sufficiently many boundary derivatives zero) separate the
coefficient of each arbitrary function. Mathlib already proves the
almost-everywhere test-function separation theorem; continuity and positivity
on open sets upgrade it to pointwise equality here.

The full theorems remain outside this module. They require finite jets and
prolongations, total derivatives, a Lagrangian Euler operator, boundary-current
identities, formal differential-operator adjoints, generalized/gauge symmetry
structures, and quotients by trivial symmetries and currents. In particular,
the converse clauses at source lines 8732–8744 and 8829–8843 carry division,
integration, and group-closure qualifications and must not be advertised as
unconditional modern equivalences.
-/

open MeasureTheory
open scoped ContDiff

namespace MathematicalCommons.Noether.InvariantVariationalProblems1918

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace E] [BorelSpace E]
  {f : E → F} {μ : Measure E} [Measure.IsOpenPosMeasure μ]

/-- A continuous, locally integrable coefficient that pairs to zero with every
compactly supported smooth scalar test function vanishes pointwise.

This is a source-linked combination of Mathlib's
`ae_eq_zero_of_integral_contDiff_smul_eq_zero` and `Measure.eq_of_ae_eq`. It is
`NEW_PACKAGING`, not a formalization of Noether's Satz II. -/
theorem continuous_eq_zero_of_integral_contDiff_smul_eq_zero
    (hf : LocallyIntegrable f μ) (hfc : Continuous f)
    (h : ∀ g : E → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • f x ∂μ = 0) :
    f = 0 := by
  exact Measure.eq_of_ae_eq (μ := μ)
    (ae_eq_zero_of_integral_contDiff_smul_eq_zero hf h) hfc continuous_const

#print axioms continuous_eq_zero_of_integral_contDiff_smul_eq_zero

end MathematicalCommons.Noether.InvariantVariationalProblems1918

