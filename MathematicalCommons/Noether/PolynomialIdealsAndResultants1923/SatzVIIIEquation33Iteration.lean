/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.SatzVIIIOneStageDescent

/-!
# Hentzelt--Noether Satz VIII: finite iteration of equation (33)

Module for P22, controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
lines 13344--13380, especially equations (33)--(34).

`SatzVIIIOneStageDescent` formalizes one supplied equation-(33) witness.  This
file proves the finite iteration used in the printed argument.  A consecutive
family of witnesses sends a product of the corresponding integral forms and
an element of the starting ground ideal into the later ground ideal.  At the
terminal cutoff, all allowed multipliers are nonzero constants over the source
field, hence units; consequently the terminal ground ideal is the original
ideal.  The full product therefore belongs to the original ideal when the
whole witness family is supplied.

The file does not construct that witness family, identify the forms with
primitive or canonical historical `E^(i)`, prove the parallel `R^(i)` result,
or establish determinant-norm/resultant identities.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open scoped BigOperators

namespace SatzVIIIOneStageDescent

noncomputable section

variable {P : Type*} [Field P]
variable {n : ℕ}

/-- The elementwise equation-(33) witness is equivalent to the ideal
inclusion naturally produced by annihilator and determinant calculations. -/
theorem hasEquation33Witness_iff_span_mul_le_succStageGroundIdeal
    (I : Ideal (MvPolynomial (Fin n) P)) (cutoff : ℕ)
    (e : MvPolynomial (Fin n) P) :
    HasEquation33Witness I cutoff e ↔
      Ideal.span ({e} : Set (MvPolynomial (Fin n) P)) *
          stageGroundIdeal (S := P) cutoff I ≤
        stageGroundIdeal (S := P) (cutoff + 1) I := by
  rw [Ideal.span_singleton_mul_le_iff]
  constructor
  · intro h g hg
    exact equation33_mem_succStageGroundIdeal I cutoff e h hg
  · intro h g hg
    have heg := h g hg
    rw [mem_stageGroundIdeal_iff] at heg
    obtain ⟨b, hb0, hbfree, hbI⟩ := heg
    exact ⟨b, ⟨hb0, hbfree⟩, hbI⟩

/-- Over the source field, the terminal ground ideal is the original ideal:
at cutoff `n`, an allowed multiplier has no variables and is therefore a
nonzero constant, hence a unit. -/
theorem stageGroundIdeal_card_eq
    (I : Ideal (MvPolynomial (Fin n) P)) :
    stageGroundIdeal (S := P) n I = I := by
  apply le_antisymm
  · intro g hg
    rw [mem_stageGroundIdeal_iff] at hg
    obtain ⟨b, hb0, hbfree, hbg⟩ := hg
    have hbvars : b.vars = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun j ↦ hbfree j j.isLt
    have hbC : b = MvPolynomial.C (b.coeff 0) :=
      MvPolynomial.vars_eq_empty_iff_eq_C.mp hbvars
    have hcoeff : b.coeff 0 ≠ 0 := by
      intro hzero
      apply hb0
      rw [hbC, hzero]
      exact map_zero MvPolynomial.C
    have hbUnit : IsUnit b := by
      rw [hbC]
      exact (isUnit_iff_ne_zero.mpr hcoeff).map MvPolynomial.C
    exact (Ideal.unit_mul_mem_iff_mem I hbUnit).mp hbg
  · exact RegularIdealDecomposition.le_stageGroundIdeal n I

/-- Reusable finite-window form of the repeated equation-(33) argument.
Starting with `g ∈ g_start`, `count` consecutive witnesses put the product
of their integral forms times `g` in `g_(start+count)`. -/
theorem equation33_product_mul_mem_laterStageGroundIdeal
    (I : Ideal (MvPolynomial (Fin n) P))
    (e : ℕ → MvPolynomial (Fin n) P) (start count : ℕ)
    (h : ∀ j < count, HasEquation33Witness I (start + j) (e j))
    {g : MvPolynomial (Fin n) P}
    (hg : g ∈ stageGroundIdeal (S := P) start I) :
    (∏ j ∈ Finset.range count, e j) * g ∈
      stageGroundIdeal (S := P) (start + count) I := by
  revert h
  induction count with
  | zero =>
      intro _h
      simpa
  | succ count ih =>
      intro h
      have hprev := ih
        (fun j hj ↦ h j (hj.trans (Nat.lt_succ_self count)))
      have hnext := equation33_mem_succStageGroundIdeal
        I (start + count) (e count)
        (h count (Nat.lt_succ_self count)) hprev
      simpa [Finset.prod_range_succ, Nat.add_assoc, mul_assoc, mul_comm,
        mul_left_comm] using hnext

/-- Prefix form of the printed induction after equation (33).  Nonzeroness of
`I` supplies `g₀ = ⊤`, so the product of the first `count` forms belongs to
the `count`-th ground ideal. -/
theorem equation33_partialProduct_mem_stageGroundIdeal
    (I : Ideal (MvPolynomial (Fin n) P)) (hI : I ≠ ⊥)
    (e : ℕ → MvPolynomial (Fin n) P) (count : ℕ)
    (h : ∀ j < count, HasEquation33Witness I j (e j)) :
    (∏ j ∈ Finset.range count, e j) ∈
      stageGroundIdeal (S := P) count I := by
  have hOne : (1 : MvPolynomial (Fin n) P) ∈
      stageGroundIdeal (S := P) 0 I := by
    rw [(RegularIdealDecomposition.stageGroundIdeal_zero_eq_top_iff I).2 hI]
    simp
  simpa using
    (equation33_product_mul_mem_laterStageGroundIdeal
      I e 0 count (by simpa using h) hOne)

/-- Conditional `E`-product half of equation (34): a complete supplied
equation-(33) witness family puts the product of the `n` integral forms in the
original ideal. -/
theorem equation33_fullProduct_mem
    (I : Ideal (MvPolynomial (Fin n) P)) (hI : I ≠ ⊥)
    (e : ℕ → MvPolynomial (Fin n) P)
    (h : ∀ j < n, HasEquation33Witness I j (e j)) :
    (∏ j ∈ Finset.range n, e j) ∈ I := by
  rw [← stageGroundIdeal_card_eq I]
  exact equation33_partialProduct_mem_stageGroundIdeal I hI e n h

/-- Tail-window endpoint used in the last paragraph of Satz VIII.  Whenever
the chosen window ends at the terminal stage, its product sends every element
of the starting ground ideal into the original ideal. -/
theorem equation33_product_mul_mem_of_add_eq_card
    (I : Ideal (MvPolynomial (Fin n) P))
    (e : ℕ → MvPolynomial (Fin n) P) (start count : ℕ)
    (hend : start + count = n)
    (h : ∀ j < count, HasEquation33Witness I (start + j) (e j))
    {g : MvPolynomial (Fin n) P}
    (hg : g ∈ stageGroundIdeal (S := P) start I) :
    (∏ j ∈ Finset.range count, e j) * g ∈ I := by
  have hterminal := equation33_product_mul_mem_laterStageGroundIdeal
    I e start count h hg
  simpa [hend, stageGroundIdeal_card_eq I] using hterminal

#print axioms hasEquation33Witness_iff_span_mul_le_succStageGroundIdeal
#print axioms stageGroundIdeal_card_eq
#print axioms equation33_product_mul_mem_laterStageGroundIdeal
#print axioms equation33_partialProduct_mem_stageGroundIdeal
#print axioms equation33_fullProduct_mem
#print axioms equation33_product_mul_mem_of_add_eq_card

end


end SatzVIIIOneStageDescent

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
