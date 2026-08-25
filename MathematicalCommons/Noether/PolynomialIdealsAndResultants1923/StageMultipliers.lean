/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.SatzVIBridge
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Hentzelt--Noether Definition V: stage multipliers

Controlled source: Kurt Hentzelt, freely edited and conceptually recast by
Emmy Noether, *Zur Theorie der Polynomideale und Resultanten*, witness
`NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
notation and Definition V at lines 13039--13052, especially equation (16).

The source numbers variables and multiplier stages from one: `b^(i)` is a
nonzero polynomial free of `x_1, ..., x_(i-1)`, for `1 <= i <= n`.  This file
uses `Fin n` for the variables, so variable `j : Fin n` represents source
`x_(j+1)`.  The natural-number argument `cutoff` is the number of initial
zero-based variables forbidden in a multiplier.  Thus source `b^(i)` uses
`cutoff = i - 1`; equivalently, zero-based ground stage `s` uses source
`b^(s+1)` and cutoff `s`.

The carrier is expressed through `MvPolynomial.vars`.  This states the
historical condition directly, avoids a choice of a smaller variable type,
and lets `vars_mul` prove multiplicative closure.  The coefficient ring is
assumed to have no zero divisors because Definition V asks for *nonzero*
multipliers, and nonzero elements form a submonoid only under that hypothesis.
The historical coefficient ring is a field, so this loses no source case.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open Ideal

section StageMultipliers

variable {S : Type*} [CommRing S] [NoZeroDivisors S] [Nontrivial S]
variable {n : ℕ}

/-- The nonzero polynomials involving only variables whose zero-based index
is at least `cutoff`.

For source stage `i` (`1 <= i <= n`), instantiate this with `cutoff = i - 1`.
For zero-based ground stage `s`, instantiate it with `cutoff = s`; its
elements are the source multipliers `b^(s+1)`. -/
def nonzeroLateVariableSubmonoid (cutoff : ℕ) :
    Submonoid (MvPolynomial (Fin n) S) where
  carrier := {p | p ≠ 0 ∧
    ∀ j : Fin n, j.1 < cutoff → j ∉ p.vars}
  one_mem' := by
    simp
  mul_mem' := by
    rintro p q ⟨hp0, hp⟩ ⟨hq0, hq⟩
    refine ⟨mul_ne_zero hp0 hq0, ?_⟩
    intro j hj hmem
    have hmem' := MvPolynomial.vars_mul p q hmem
    simp only [Finset.mem_union] at hmem'
    exact hmem'.elim (hp j hj) (hq j hj)

/-- Literal membership criterion for a stage multiplier. -/
@[simp]
theorem mem_nonzeroLateVariableSubmonoid_iff
    (cutoff : ℕ) (p : MvPolynomial (Fin n) S) :
    p ∈ nonzeroLateVariableSubmonoid (S := S) (n := n) cutoff ↔
      p ≠ 0 ∧ ∀ j : Fin n, j.1 < cutoff → j ∉ p.vars :=
  Iff.rfl

/-- Every variable actually occurring in an allowed multiplier has index at
least the cutoff. -/
theorem cutoff_le_of_mem_vars_of_mem_nonzeroLateVariableSubmonoid
    {cutoff : ℕ} {p : MvPolynomial (Fin n) S}
    (hp : p ∈ nonzeroLateVariableSubmonoid (S := S) (n := n) cutoff)
    {j : Fin n} (hj : j ∈ p.vars) :
    cutoff ≤ j.1 := by
  exact Nat.le_of_not_gt (fun hlt ↦ (hp.2 j hlt) hj)

/-- Support-level version of the freedom condition: every monomial of an
allowed multiplier has exponent zero at each forbidden early variable. -/
theorem exponent_eq_zero_of_mem_support_of_mem_nonzeroLateVariableSubmonoid
    {cutoff : ℕ} {p : MvPolynomial (Fin n) S}
    (hp : p ∈ nonzeroLateVariableSubmonoid (S := S) (n := n) cutoff)
    {d : Fin n →₀ ℕ} (hd : d ∈ p.support)
    {j : Fin n} (hj : j.1 < cutoff) :
    d j = 0 :=
  MvPolynomial.mem_support_notMem_vars_zero hd (hp.2 j hj)

/-- At cutoff zero, the only restriction is nonvanishing.  This is source
stage `i = 1`, whose multiplier `b^(1)` may involve every variable. -/
@[simp]
theorem mem_nonzeroLateVariableSubmonoid_zero_iff
    (p : MvPolynomial (Fin n) S) :
    p ∈ nonzeroLateVariableSubmonoid (S := S) (n := n) 0 ↔ p ≠ 0 := by
  simp [nonzeroLateVariableSubmonoid]

/-- A nonzero constant is an allowed multiplier at every stage. -/
@[simp]
theorem C_mem_nonzeroLateVariableSubmonoid_iff
    (cutoff : ℕ) (a : S) :
    MvPolynomial.C a ∈
        nonzeroLateVariableSubmonoid (S := S) (n := n) cutoff ↔
      a ≠ 0 := by
  simp [nonzeroLateVariableSubmonoid]

/-- A variable itself is an allowed multiplier exactly when its zero-based
index is not among the forbidden early indices. -/
@[simp]
theorem X_mem_nonzeroLateVariableSubmonoid_iff
    (cutoff : ℕ) (j : Fin n) :
    MvPolynomial.X j ∈
        nonzeroLateVariableSubmonoid (S := S) (n := n) cutoff ↔
      cutoff ≤ j.1 := by
  rw [mem_nonzeroLateVariableSubmonoid_iff]
  constructor
  · rintro ⟨_hX0, hfree⟩
    exact Nat.le_of_not_gt (fun hlt ↦ hfree j hlt (by simp))
  · intro hcutoff
    refine ⟨by simp, ?_⟩
    intro k hk hmem
    have hkj : k = j := by simpa using hmem
    subst k
    exact (Nat.not_lt_of_ge hcutoff) hk

/-- Increasing the cutoff removes possible multipliers.  This is the
multiplicative-class orientation behind the source observation that every
`b^(i+1)` is also a `b^(i)`. -/
theorem nonzeroLateVariableSubmonoid_antitone
    {i j : ℕ} (hij : i ≤ j) :
    nonzeroLateVariableSubmonoid (S := S) (n := n) j ≤
      nonzeroLateVariableSubmonoid (S := S) (n := n) i := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  intro k hk
  exact hp.2 k (hk.trans_le hij)

/-- At cutoff `n`, all variables are forbidden, so an allowed multiplier is
precisely a nonzero constant polynomial. -/
theorem mem_nonzeroLateVariableSubmonoid_card_iff
    (p : MvPolynomial (Fin n) S) :
    p ∈ nonzeroLateVariableSubmonoid (S := S) (n := n) n ↔
      p ≠ 0 ∧ p.vars = ∅ := by
  constructor
  · intro hp
    refine ⟨hp.1, Finset.eq_empty_iff_forall_notMem.mpr ?_⟩
    intro j
    exact hp.2 j j.isLt
  · rintro ⟨hp0, hvars⟩
    refine ⟨hp0, ?_⟩
    intro j _hj
    simp [hvars]

/-- Definition V's ground ideal at a zero-based cutoff: localize at all
nonzero late-variable polynomials and contract the extended ideal. -/
noncomputable def stageGroundIdeal
    (cutoff : ℕ) (I : Ideal (MvPolynomial (Fin n) S)) :
    Ideal (MvPolynomial (Fin n) S) :=
  groundIdealAlong
    (nonzeroLateVariableSubmonoid (S := S) (n := n) cutoff) I

/-- Equation (16), with the multiplier class made literal. -/
theorem mem_stageGroundIdeal_iff
    (cutoff : ℕ) (I : Ideal (MvPolynomial (Fin n) S))
    (G : MvPolynomial (Fin n) S) :
    G ∈ stageGroundIdeal (S := S) cutoff I ↔
      ∃ b : MvPolynomial (Fin n) S,
        b ≠ 0 ∧
        (∀ j : Fin n, j.1 < cutoff → j ∉ b.vars) ∧
        b * G ∈ I := by
  rw [stageGroundIdeal, mem_groundIdealAlong_iff]
  simp only [mem_nonzeroLateVariableSubmonoid_iff]
  aesop

/-- The ground ideals are antitone in the zero-based cutoff.  In source
indices this says `g_i <= g_(i-1)`, since the former uses `b^(i+1)` and the
latter `b^(i)`. -/
theorem stageGroundIdeal_antitone
    {i j : ℕ} (hij : i ≤ j) (I : Ideal (MvPolynomial (Fin n) S)) :
    stageGroundIdeal (S := S) j I ≤ stageGroundIdeal (S := S) i I := by
  intro G hG
  rw [mem_stageGroundIdeal_iff] at hG ⊢
  obtain ⟨b, hb0, hbvars, hbG⟩ := hG
  exact ⟨b, hb0, fun k hk ↦ hbvars k (hk.trans_le hij), hbG⟩

#print axioms nonzeroLateVariableSubmonoid
#print axioms mem_nonzeroLateVariableSubmonoid_iff
#print axioms cutoff_le_of_mem_vars_of_mem_nonzeroLateVariableSubmonoid
#print axioms exponent_eq_zero_of_mem_support_of_mem_nonzeroLateVariableSubmonoid
#print axioms mem_nonzeroLateVariableSubmonoid_zero_iff
#print axioms C_mem_nonzeroLateVariableSubmonoid_iff
#print axioms X_mem_nonzeroLateVariableSubmonoid_iff
#print axioms nonzeroLateVariableSubmonoid_antitone
#print axioms mem_nonzeroLateVariableSubmonoid_card_iff
#print axioms stageGroundIdeal
#print axioms mem_stageGroundIdeal_iff
#print axioms stageGroundIdeal_antitone

end StageMultipliers

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
