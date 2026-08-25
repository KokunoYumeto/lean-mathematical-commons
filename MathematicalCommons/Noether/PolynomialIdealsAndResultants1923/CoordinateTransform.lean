/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.Ring

/-!
# Elementary shears and the Hentzelt--Noether unitriangular transformation

Controlled source: Kurt Hentzelt, freely edited and conceptually recast by
Emmy Noether, *Zur Theorie der Polynomideale und Resultanten*, witness
`NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
equation (12) and Definition IV at lines 13004--13037.

The first part of this module formalizes the reusable
elementary pivot shear

`y_i = x_i - u_i x_p`,  `y_p = x_p`.

The construction works over an arbitrary commutative ring.  This elementary
shear is useful for factorizations, but it is not equation (12) of the source.
That equation is the full lower-unitriangular transformation

`y_i = x_i + ∑ j < i, u_ij x_j`,

formalized in the second part of this module.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open MvPolynomial

namespace CoordinateShear

noncomputable section

variable {R σ ι : Type*} [CommRing R] [DecidableEq σ]

/-- The forward images of the variables under the shear fixing `pivot`. -/
def forwardFamily (pivot : σ) (u : σ → R) (i : σ) : MvPolynomial σ R :=
  if i = pivot then X pivot else X i - C (u i) * X pivot

/-- The inverse images of the variables under the shear fixing `pivot`. -/
def inverseFamily (pivot : σ) (u : σ → R) (i : σ) : MvPolynomial σ R :=
  if i = pivot then X pivot else X i + C (u i) * X pivot

/-- The forward substitution as an algebra homomorphism. -/
def forwardHom (pivot : σ) (u : σ → R) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  bind₁ (forwardFamily pivot u)

/-- The inverse substitution as an algebra homomorphism. -/
def inverseHom (pivot : σ) (u : σ → R) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  bind₁ (inverseFamily pivot u)

@[simp]
theorem forwardHom_X (pivot : σ) (u : σ → R) (i : σ) :
    forwardHom pivot u (X i) = forwardFamily pivot u i := by
  simp [forwardHom]

@[simp]
theorem inverseHom_X (pivot : σ) (u : σ → R) (i : σ) :
    inverseHom pivot u (X i) = inverseFamily pivot u i := by
  simp [inverseHom]

theorem forward_comp_inverse (pivot : σ) (u : σ → R) :
    (forwardHom pivot u).comp (inverseHom pivot u) =
      AlgHom.id R (MvPolynomial σ R) := by
  ext i
  by_cases h : i = pivot
  · subst i
    simp [forwardHom, inverseHom, forwardFamily, inverseFamily]
  · simp [forwardHom, inverseHom, forwardFamily, inverseFamily, h]

theorem inverse_comp_forward (pivot : σ) (u : σ → R) :
    (inverseHom pivot u).comp (forwardHom pivot u) =
      AlgHom.id R (MvPolynomial σ R) := by
  ext i
  by_cases h : i = pivot
  · subst i
    simp [forwardHom, inverseHom, forwardFamily, inverseFamily]
  · simp [forwardHom, inverseHom, forwardFamily, inverseFamily, h]

/-- The unitriangular coordinate substitution as an algebra equivalence. -/
def equiv (pivot : σ) (u : σ → R) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (forwardHom pivot u) (inverseHom pivot u)
    (forward_comp_inverse pivot u) (inverse_comp_forward pivot u)

@[simp]
theorem equiv_apply (pivot : σ) (u : σ → R) (p : MvPolynomial σ R) :
    equiv pivot u p = forwardHom pivot u p :=
  rfl

@[simp]
theorem equiv_symm_apply (pivot : σ) (u : σ → R) (p : MvPolynomial σ R) :
    (equiv pivot u).symm p = inverseHom pivot u p :=
  rfl

@[simp]
theorem equiv_X (pivot : σ) (u : σ → R) (i : σ) :
    equiv pivot u (X i) = forwardFamily pivot u i := by
  simp [equiv]

@[simp]
theorem equiv_symm_X (pivot : σ) (u : σ → R) (i : σ) :
    (equiv pivot u).symm (X i) = inverseFamily pivot u i := by
  simp [equiv]

@[simp]
theorem equiv_X_pivot (pivot : σ) (u : σ → R) :
    equiv pivot u (X pivot) = X pivot := by
  simp [forwardFamily]

@[simp]
theorem equiv_symm_X_pivot (pivot : σ) (u : σ → R) :
    (equiv pivot u).symm (X pivot) = X pivot := by
  simp [inverseFamily]

theorem equiv_X_of_ne (pivot : σ) (u : σ → R) {i : σ} (hi : i ≠ pivot) :
    equiv pivot u (X i) = X i - C (u i) * X pivot := by
  simp [forwardFamily, hi]

theorem equiv_symm_X_of_ne (pivot : σ) (u : σ → R) {i : σ} (hi : i ≠ pivot) :
    (equiv pivot u).symm (X i) = X i + C (u i) * X pivot := by
  simp [inverseFamily, hi]

/-- Transport an ideal through the coordinate shear. -/
def transformIdeal (pivot : σ) (u : σ → R) (I : Ideal (MvPolynomial σ R)) :
    Ideal (MvPolynomial σ R) :=
  I.map (equiv pivot u).toRingEquiv

@[simp]
theorem equiv_apply_mem_transformIdeal_iff (pivot : σ) (u : σ → R)
    (I : Ideal (MvPolynomial σ R)) (p : MvPolynomial σ R) :
    equiv pivot u p ∈ transformIdeal pivot u I ↔ p ∈ I := by
  exact Ideal.apply_mem_of_equiv_iff

theorem mem_transformIdeal_iff_symm_mem (pivot : σ) (u : σ → R)
    (I : Ideal (MvPolynomial σ R)) (p : MvPolynomial σ R) :
    p ∈ transformIdeal pivot u I ↔ (equiv pivot u).symm p ∈ I := by
  exact Ideal.symm_apply_mem_of_equiv_iff.symm

@[simp]
theorem map_symm_transformIdeal (pivot : σ) (u : σ → R)
    (I : Ideal (MvPolynomial σ R)) :
    (transformIdeal pivot u I).map (equiv pivot u).symm.toRingEquiv = I := by
  exact Ideal.map_of_equiv (equiv pivot u).toRingEquiv

theorem transformIdeal_span (pivot : σ) (u : σ → R)
    (s : Set (MvPolynomial σ R)) :
    transformIdeal pivot u (Ideal.span s) =
      Ideal.span (equiv pivot u '' s) := by
  exact Ideal.map_span _ _

theorem transformIdeal_span_range (pivot : σ) (u : σ → R)
    (f : ι → MvPolynomial σ R) :
    transformIdeal pivot u (Ideal.span (Set.range f)) =
      Ideal.span (Set.range fun i ↦ equiv pivot u (f i)) := by
  rw [transformIdeal, Ideal.map_span]
  congr 1
  ext p
  simp

/-- Extend pivot-shear parameters by zero at the distinguished `Option` variable. -/
def optionParameters (u : σ → R) : Option σ → R
  | none => 0
  | some i => u i

/-- An `Option`-indexed elementary pivot shear, with `none` as the pivot.
This is a reusable component and is not Noether's full equation (12). -/
def optionPivotEquiv (u : σ → R) :
    MvPolynomial (Option σ) R ≃ₐ[R] MvPolynomial (Option σ) R :=
  equiv none (optionParameters u)

@[simp]
theorem optionPivotEquiv_X_some (u : σ → R) (i : σ) :
    optionPivotEquiv u (X (some i)) =
      X (some i) - C (u i) * X none := by
  simp [optionPivotEquiv, forwardFamily, optionParameters]

@[simp]
theorem optionPivotEquiv_X_none (u : σ → R) :
    optionPivotEquiv u (X none) = X none := by
  change equiv (R := R) none (optionParameters u) (X none) = X none
  exact equiv_X_pivot _ _

@[simp]
theorem optionPivotEquiv_symm_X_some (u : σ → R) (i : σ) :
    (optionPivotEquiv u).symm (X (some i)) =
      X (some i) + C (u i) * X none := by
  simp [optionPivotEquiv, inverseFamily, optionParameters]

@[simp]
theorem optionPivotEquiv_symm_X_none (u : σ → R) :
    (optionPivotEquiv u).symm (X none) = X none := by
  change (equiv (R := R) none (optionParameters u)).symm (X none) = X none
  exact equiv_symm_X_pivot _ _

section LowerUnitriangular

variable {n : ℕ}

/-- The source-faithful image of `x_i` in equation (12):
`x_i + ∑ j < i, u_ij x_j`.  Values of `u i j` with `i ≤ j` are ignored. -/
def lowerImage (u : Fin n → Fin n → R) (i : Fin n) : MvPolynomial (Fin n) R :=
  X i + ∑ j ∈ Finset.Iio i, C (u i j) * X j

/-- One row of the lower-unitriangular substitution. -/
def rowForwardFamily (u : Fin n → Fin n → R) (target i : Fin n) :
    MvPolynomial (Fin n) R :=
  if i = target then lowerImage u target else X i

/-- The inverse of one row substitution. -/
def rowInverseFamily (u : Fin n → Fin n → R) (target i : Fin n) :
    MvPolynomial (Fin n) R :=
  if i = target then
    X target - ∑ j ∈ Finset.Iio target, C (u target j) * X j
  else X i

def rowForwardHom (u : Fin n → Fin n → R) (target : Fin n) :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  bind₁ (rowForwardFamily u target)

def rowInverseHom (u : Fin n → Fin n → R) (target : Fin n) :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
  bind₁ (rowInverseFamily u target)

@[simp]
theorem rowForwardHom_X (u : Fin n → Fin n → R) (target i : Fin n) :
    rowForwardHom u target (X i) = rowForwardFamily u target i := by
  simp [rowForwardHom]

@[simp]
theorem rowInverseHom_X (u : Fin n → Fin n → R) (target i : Fin n) :
    rowInverseHom u target (X i) = rowInverseFamily u target i := by
  simp [rowInverseHom]

theorem rowForward_comp_inverse (u : Fin n → Fin n → R) (target : Fin n) :
    (rowForwardHom u target).comp (rowInverseHom u target) =
      AlgHom.id R (MvPolynomial (Fin n) R) := by
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hi : i = target
  · subst i
    have hfix :
        rowForwardHom u target
            (∑ j ∈ Finset.Iio target, C (u target j) * X j) =
          ∑ j ∈ Finset.Iio target, C (u target j) * X j := by
      simp only [map_sum, map_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [show rowForwardHom u target (C (u target j)) = C (u target j) from
        (rowForwardHom u target).commutes (u target j)]
      rw [rowForwardHom_X]
      simp [rowForwardFamily, ne_of_lt (Finset.mem_Iio.mp hj)]
    simp only [AlgHom.comp_apply, AlgHom.id_apply, rowInverseHom_X,
      rowInverseFamily, if_pos]
    rw [map_sub, hfix, rowForwardHom_X]
    simp [rowForwardFamily, lowerImage]
  · simp [rowForwardHom, rowInverseHom, rowForwardFamily, rowInverseFamily, hi]

theorem rowInverse_comp_forward (u : Fin n → Fin n → R) (target : Fin n) :
    (rowInverseHom u target).comp (rowForwardHom u target) =
      AlgHom.id R (MvPolynomial (Fin n) R) := by
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hi : i = target
  · subst i
    have hfix :
        rowInverseHom u target
            (∑ j ∈ Finset.Iio target, C (u target j) * X j) =
          ∑ j ∈ Finset.Iio target, C (u target j) * X j := by
      simp only [map_sum, map_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [show rowInverseHom u target (C (u target j)) = C (u target j) from
        (rowInverseHom u target).commutes (u target j)]
      rw [rowInverseHom_X]
      simp [rowInverseFamily, ne_of_lt (Finset.mem_Iio.mp hj)]
    simp only [AlgHom.comp_apply, AlgHom.id_apply, rowForwardHom_X,
      rowForwardFamily, if_pos]
    rw [lowerImage]
    rw [map_add, hfix, rowInverseHom_X]
    simp [rowInverseFamily]
  · simp [rowForwardHom, rowInverseHom, rowForwardFamily, rowInverseFamily, hi]

/-- The algebra equivalence changing exactly one row of the variables. -/
def rowEquiv (u : Fin n → Fin n → R) (target : Fin n) :
    MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R :=
  AlgEquiv.ofAlgHom (rowForwardHom u target) (rowInverseHom u target)
    (rowForward_comp_inverse u target) (rowInverse_comp_forward u target)

@[simp]
theorem rowEquiv_X (u : Fin n → Fin n → R) (target i : Fin n) :
    rowEquiv u target (X i) = rowForwardFamily u target i := by
  simp [rowEquiv]

@[simp]
theorem rowEquiv_X_target (u : Fin n → Fin n → R) (target : Fin n) :
    rowEquiv u target (X target) = lowerImage u target := by
  simp [rowForwardFamily]

theorem rowEquiv_X_of_ne (u : Fin n → Fin n → R) (target : Fin n)
    {i : Fin n} (hi : i ≠ target) : rowEquiv u target (X i) = X i := by
  simp [rowForwardFamily, hi]

/-- A later row fixes the complete image of every earlier variable. -/
theorem rowEquiv_lowerImage_of_lt (u : Fin n → Fin n → R)
    {i target : Fin n} (hit : i < target) :
    rowEquiv u target (lowerImage u i) = lowerImage u i := by
  simp only [lowerImage, map_add, map_sum, map_mul]
  rw [rowEquiv_X_of_ne u target (ne_of_lt hit)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [show rowEquiv u target (C (u i j)) = C (u i j) from
    (rowEquiv u target).commutes (u i j)]
  rw [rowEquiv_X_of_ne u target]
  exact ne_of_lt ((Finset.mem_Iio.mp hj).trans hit)

/-- Compose the first `m` row equivalences in increasing order.  The branch
outside `m ≤ n` makes the definition total; the source-facing construction
only uses `m = n`. -/
def lowerPrefixEquiv (u : Fin n → Fin n → R) : ℕ →
    MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R
  | 0 => AlgEquiv.refl
  | m + 1 => if h : m < n then
      (lowerPrefixEquiv u m).trans (rowEquiv u ⟨m, h⟩)
    else lowerPrefixEquiv u m

/-- After `m` rows, precisely the variables with index below `m` have acquired
their source-faithful lower-unitriangular images. -/
theorem lowerPrefixEquiv_X (u : Fin n → Fin n → R) (m : ℕ) (hm : m ≤ n)
    (i : Fin n) :
    lowerPrefixEquiv u m (X i) =
      if i.val < m then lowerImage u i else X i := by
  induction m with
  | zero => simp [lowerPrefixEquiv]
  | succ m ih =>
      have hmn : m < n := Nat.lt_of_succ_le hm
      rw [lowerPrefixEquiv]
      simp only [dif_pos hmn, AlgEquiv.trans_apply]
      rw [ih (Nat.le_of_lt hmn)]
      by_cases him : i.val < m
      · rw [if_pos him]
        rw [rowEquiv_lowerImage_of_lt u (show i < ⟨m, hmn⟩ from him)]
        rw [if_pos (him.trans (Nat.lt_succ_self m))]
      · rw [if_neg him]
        by_cases his : i.val < m + 1
        · have hieq : i = ⟨m, hmn⟩ := by
            apply Fin.ext
            exact Nat.le_antisymm (Nat.le_of_lt_succ his) (Nat.le_of_not_gt him)
          subst i
          rw [if_pos (Nat.lt_succ_self m)]
          exact rowEquiv_X_target u ⟨m, hmn⟩
        · have hine : i ≠ ⟨m, hmn⟩ := by
            intro hi
            subst i
            exact his (Nat.lt_succ_self m)
          rw [if_neg his]
          exact rowEquiv_X_of_ne u ⟨m, hmn⟩ hine

/-- Equation (12) of Hentzelt--Noether 1923 as an algebra equivalence. -/
def lowerUnitriangularEquiv (u : Fin n → Fin n → R) :
    MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R :=
  lowerPrefixEquiv u n

@[simp]
theorem lowerUnitriangularEquiv_X (u : Fin n → Fin n → R) (i : Fin n) :
    lowerUnitriangularEquiv u (X i) = lowerImage u i := by
  simpa [lowerUnitriangularEquiv, i.isLt] using lowerPrefixEquiv_X u n le_rfl i

/-- The inverse generator formula, recursively triangular in the lower
variables.  Together with `lowerUnitriangularEquiv_X`, this gives both
directions of the coordinate change without choosing matrix inverses. -/
theorem lowerUnitriangularEquiv_symm_X (u : Fin n → Fin n → R) (i : Fin n) :
    (lowerUnitriangularEquiv u).symm (X i) =
      X i - ∑ j ∈ Finset.Iio i,
        C (u i j) * (lowerUnitriangularEquiv u).symm (X j) := by
  have h := congrArg (lowerUnitriangularEquiv u).symm
    (lowerUnitriangularEquiv_X u i)
  simp only [AlgEquiv.symm_apply_apply, lowerImage, map_add, map_sum, map_mul] at h
  have hC : ∀ r : R, (lowerUnitriangularEquiv u).symm (C r) = C r := by
    intro r
    exact (lowerUnitriangularEquiv u).symm.commutes r
  simp only [hC] at h
  rw [eq_sub_iff_add_eq]
  exact h.symm

/-- Transport an ideal through the full lower-unitriangular transformation. -/
def lowerTransformIdeal (u : Fin n → Fin n → R)
    (I : Ideal (MvPolynomial (Fin n) R)) : Ideal (MvPolynomial (Fin n) R) :=
  I.map (lowerUnitriangularEquiv u).toRingEquiv

@[simp]
theorem lowerEquiv_apply_mem_transformIdeal_iff (u : Fin n → Fin n → R)
    (I : Ideal (MvPolynomial (Fin n) R)) (p : MvPolynomial (Fin n) R) :
    lowerUnitriangularEquiv u p ∈ lowerTransformIdeal u I ↔ p ∈ I := by
  exact Ideal.apply_mem_of_equiv_iff

theorem mem_lowerTransformIdeal_iff_symm_mem (u : Fin n → Fin n → R)
    (I : Ideal (MvPolynomial (Fin n) R)) (p : MvPolynomial (Fin n) R) :
    p ∈ lowerTransformIdeal u I ↔ (lowerUnitriangularEquiv u).symm p ∈ I := by
  exact Ideal.symm_apply_mem_of_equiv_iff.symm

@[simp]
theorem map_symm_lowerTransformIdeal (u : Fin n → Fin n → R)
    (I : Ideal (MvPolynomial (Fin n) R)) :
    (lowerTransformIdeal u I).map (lowerUnitriangularEquiv u).symm.toRingEquiv = I := by
  exact Ideal.map_of_equiv (lowerUnitriangularEquiv u).toRingEquiv

theorem lowerTransformIdeal_span (u : Fin n → Fin n → R)
    (s : Set (MvPolynomial (Fin n) R)) :
    lowerTransformIdeal u (Ideal.span s) =
      Ideal.span (lowerUnitriangularEquiv u '' s) := by
  exact Ideal.map_span _ _

theorem lowerTransformIdeal_span_range (u : Fin n → Fin n → R)
    (f : ι → MvPolynomial (Fin n) R) :
    lowerTransformIdeal u (Ideal.span (Set.range f)) =
      Ideal.span (Set.range fun i ↦ lowerUnitriangularEquiv u (f i)) := by
  rw [lowerTransformIdeal, Ideal.map_span]
  congr 1
  ext p
  simp

end LowerUnitriangular

#print axioms forwardFamily
#print axioms inverseFamily
#print axioms forwardHom
#print axioms inverseHom
#print axioms forwardHom_X
#print axioms inverseHom_X
#print axioms forward_comp_inverse
#print axioms inverse_comp_forward
#print axioms equiv
#print axioms equiv_apply
#print axioms equiv_symm_apply
#print axioms equiv_X
#print axioms equiv_symm_X
#print axioms equiv_X_pivot
#print axioms equiv_symm_X_pivot
#print axioms equiv_X_of_ne
#print axioms equiv_symm_X_of_ne
#print axioms transformIdeal
#print axioms equiv_apply_mem_transformIdeal_iff
#print axioms mem_transformIdeal_iff_symm_mem
#print axioms map_symm_transformIdeal
#print axioms transformIdeal_span
#print axioms transformIdeal_span_range
#print axioms optionParameters
#print axioms optionPivotEquiv
#print axioms optionPivotEquiv_X_some
#print axioms optionPivotEquiv_X_none
#print axioms optionPivotEquiv_symm_X_some
#print axioms optionPivotEquiv_symm_X_none
#print axioms lowerImage
#print axioms rowForwardFamily
#print axioms rowInverseFamily
#print axioms rowForwardHom
#print axioms rowInverseHom
#print axioms rowForwardHom_X
#print axioms rowInverseHom_X
#print axioms rowForward_comp_inverse
#print axioms rowInverse_comp_forward
#print axioms rowEquiv
#print axioms rowEquiv_X
#print axioms rowEquiv_X_target
#print axioms rowEquiv_X_of_ne
#print axioms rowEquiv_lowerImage_of_lt
#print axioms lowerPrefixEquiv
#print axioms lowerPrefixEquiv_X
#print axioms lowerUnitriangularEquiv
#print axioms lowerUnitriangularEquiv_X
#print axioms lowerUnitriangularEquiv_symm_X
#print axioms lowerTransformIdeal
#print axioms lowerEquiv_apply_mem_transformIdeal_iff
#print axioms mem_lowerTransformIdeal_iff_symm_mem
#print axioms map_symm_lowerTransformIdeal
#print axioms lowerTransformIdeal_span
#print axioms lowerTransformIdeal_span_range

end

end CoordinateShear

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

