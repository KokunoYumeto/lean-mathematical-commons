/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.GenericParameters
import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.RegularitySpecialization
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Generic coordinate regularity for Hentzelt--Noether equation (12)

Controlled source: Kurt Hentzelt, freely edited and conceptually recast by
Emmy Noether, *Zur Theorie der Polynomideale und Resultanten*, witness
`NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
especially equation (12), Definition IV, and the regular-coordinate argument
at lines 13004--13039.

This module proves that the full lower-unitriangular coordinate equivalence
preserves homogeneous degree.  It then defines the exact pure-power
coefficient whose nonvanishing makes the first variable regular over the
independent-parameter fraction field.  On generators, that coefficient is
computed explicitly: it is `1` for the first generator and the independent
parameter indexed by `(i,0)` for every later generator.

The remaining historical claim is intentionally not hidden here: for an
arbitrary nonzero homogeneous input, one must still prove that its generic
leading coefficient is nonzero.  This module packages that obligation and
derives source-shaped regularity once it is discharged.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open MvPolynomial
open RegularitySpecialization

namespace GenericRegularity

noncomputable section

variable {R : Type*} [CommRing R]
variable {n : ℕ}

/-- Every source-faithful lower image is a homogeneous linear form. -/
theorem lowerImage_isHomogeneous (u : Fin n → Fin n → R) (i : Fin n) :
    IsHomogeneous (CoordinateShear.lowerImage u i) 1 := by
  classical
  unfold CoordinateShear.lowerImage
  apply IsHomogeneous.add
  · exact isHomogeneous_X R i
  · apply IsHomogeneous.sum
    intro j hj
    have hC : IsHomogeneous
        (C (u i j) : MvPolynomial (Fin n) R) 0 :=
      isHomogeneous_C (σ := Fin n) (R := R) _
    have hX : IsHomogeneous (X j : MvPolynomial (Fin n) R) 1 :=
      isHomogeneous_X (R := R) j
    simpa using hC.mul hX

/-- The full lower-unitriangular equivalence preserves homogeneous degree. -/
theorem lowerUnitriangularEquiv_isHomogeneous
    (u : Fin n → Fin n → R) {F : MvPolynomial (Fin n) R} {r : ℕ}
    (hF : IsHomogeneous F r) :
    IsHomogeneous (CoordinateShear.lowerUnitriangularEquiv u F) r := by
  have hmap :
      (CoordinateShear.lowerUnitriangularEquiv u).toAlgHom =
        MvPolynomial.eval₂AlgHom R
          (fun i : Fin n => CoordinateShear.lowerImage u i) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [CoordinateShear.lowerUnitriangularEquiv_X]
  change IsHomogeneous
    ((CoordinateShear.lowerUnitriangularEquiv u).toAlgHom F) r
  rw [hmap]
  simpa using hF.eval₂ (algebraMap R (MvPolynomial (Fin n) R))
    (fun i : Fin n => CoordinateShear.lowerImage u i)
    (fun r => isHomogeneous_C _ _)
    (fun i => lowerImage_isHomogeneous u i)

/-- A homogeneous polynomial with a nonzero pure-power coefficient is regular
in the source sense used at P22 line 13039. -/
theorem regularity_of_homogeneous
    {i : Fin n} {r : ℕ} {F : MvPolynomial (Fin n) R}
    (hF : IsHomogeneous F r) (hcoeff : coeff (Finsupp.single i r) F ≠ 0) :
    IsRegularInDegree i r F := by
  refine ⟨?_, hcoeff⟩
  exact hF.totalDegree (by
    intro hzero
    rw [hzero] at hcoeff
    simp at hcoeff)

section Independent

open CoordinateShear.IndependentParameters

variable {P : Type*} [Field P]

/-- The rational function field in all strictly lower-triangular parameters. -/
abbrev ParameterField (n : ℕ) :=
  FractionRing (MvPolynomial (LowerParameter n) P)

/-- The source-faithful generic transform over the rational function field in
all strictly lower-triangular parameters. -/
noncomputable def independentGenericTransform
    (F : MvPolynomial (Fin n) P) :
    MvPolynomial (Fin n) (ParameterField (P := P) n) :=
  genericTransformHom (P := P) (U := LowerParameter n)
    (independentLowerUnitriangularEquiv (P := P) (n := n)) F

/-- The generic transform preserves the homogeneous degree of its input. -/
theorem independentGenericTransform_isHomogeneous
    {F : MvPolynomial (Fin n) P} {r : ℕ}
    (hF : IsHomogeneous F r) :
    IsHomogeneous (independentGenericTransform (P := P) F) r := by
  unfold independentGenericTransform genericTransformHom
  apply lowerUnitriangularEquiv_isHomogeneous
  exact hF.map (algebraMap P (ParameterField (P := P) n))

/-- The coefficient that Hentzelt--Noether's generic change must make
nonzero in order to make the first variable regular. -/
noncomputable def independentGenericLeadingCoefficient
    (hn : 0 < n) (F : MvPolynomial (Fin n) P) (r : ℕ) :
    ParameterField (P := P) n :=
  coeff (Finsupp.single (⟨0, hn⟩ : Fin n) r)
    (independentGenericTransform (P := P) F)

/-- A nonzero generic leading coefficient gives first-variable regularity over
the parameter fraction field.  The nonvanishing of this coefficient for an
arbitrary input is deliberately a separate algebraic obligation. -/
theorem independentGenericTransform_isRegularInDegree_of_leadingCoefficient_ne_zero
    (hn : 0 < n) {F : MvPolynomial (Fin n) P} {r : ℕ}
    (hF : IsHomogeneous F r)
    (hlead : independentGenericLeadingCoefficient (P := P) hn F r ≠ 0) :
    IsRegularInDegree (⟨0, hn⟩ : Fin n) r
      (independentGenericTransform (P := P) F) := by
  exact regularity_of_homogeneous
    (independentGenericTransform_isHomogeneous (P := P) hF) hlead

/-- Equation (12) sends the first generator to itself, so its generic leading
coefficient is the unit. -/
theorem independentGenericLeadingCoefficient_X_zero
    (hn : 0 < n) (r : ℕ) (hr : r = 1) :
    independentGenericLeadingCoefficient (P := P)
      hn (X (⟨0, hn⟩ : Fin n)) r = 1 := by
  subst r
  classical
  change coeff (Finsupp.single (⟨0, hn⟩ : Fin n) 1)
    (independentLowerUnitriangularEquiv (P := P) (n := n)
      (MvPolynomial.map
        (algebraMap P (ParameterField (P := P) n))
        (X (⟨0, hn⟩ : Fin n)))) = 1
  rw [MvPolynomial.map_X, independentLowerUnitriangularEquiv_X]
  rw [coeff_add, coeff_sum, coeff_X_same]
  have hsum :
      ∑ j ∈ Finset.Iio (⟨0, hn⟩ : Fin n),
        coeff (Finsupp.single (⟨0, hn⟩ : Fin n) 1)
          (C (independentLowerMatrix P (⟨0, hn⟩ : Fin n) j) * X j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hlt : j < (⟨0, hn⟩ : Fin n) := (Finset.mem_Iio).mp hj
    exact (Nat.not_lt_zero j.val hlt).elim
  rw [hsum, add_zero]

/-- For a lower generator `x_i` with `i > 0`, the first generic leading
coefficient is exactly the `(i,0)` parameter. -/
theorem independentGenericLeadingCoefficient_X_of_pos
    (hn : 0 < n) (i : Fin n) (hi : (⟨0, hn⟩ : Fin n) < i) :
    independentGenericLeadingCoefficient (P := P) hn (X i) 1 =
      algebraMap (MvPolynomial (LowerParameter n) P)
        (ParameterField (P := P) n)
        (X (⟨(i, ⟨0, hn⟩), hi⟩ : LowerParameter n)) := by
  classical
  let i0 : Fin n := ⟨0, hn⟩
  have hmem : i0 ∈ Finset.Iio i :=
    Finset.mem_Iio.mpr (by simpa [i0] using hi)
  have hneq : i ≠ i0 := by simpa [i0] using ne_of_gt hi
  have hsingle_i : Finsupp.single i 1 ≠ Finsupp.single i0 1 :=
    (Finsupp.single_left_injective one_ne_zero).ne hneq
  change coeff (Finsupp.single (⟨0, hn⟩ : Fin n) 1)
    (independentLowerUnitriangularEquiv (P := P) (n := n)
      (MvPolynomial.map
        (algebraMap P (ParameterField (P := P) n)) (X i))) = _
  rw [MvPolynomial.map_X, independentLowerUnitriangularEquiv_X]
  rw [coeff_add, coeff_sum, Finset.sum_eq_single i0]
  · simp [i0, hsingle_i, coeff_C_mul, coeff_X,
      independentLowerMatrix_of_lt (P := P) i i0 hi]
  · intro j hj hji
    have hsingle_j : Finsupp.single j 1 ≠ Finsupp.single i0 1 :=
      (Finsupp.single_left_injective one_ne_zero).ne hji
    simp [i0, coeff_C_mul, coeff_X, hsingle_j]
  · exact fun hnotmem => (hnotmem hmem).elim

end Independent

#print axioms lowerImage_isHomogeneous
#print axioms lowerUnitriangularEquiv_isHomogeneous
#print axioms regularity_of_homogeneous
#print axioms independentGenericTransform_isHomogeneous
#print axioms independentGenericTransform_isRegularInDegree_of_leadingCoefficient_ne_zero
#print axioms independentGenericLeadingCoefficient_X_zero
#print axioms independentGenericLeadingCoefficient_X_of_pos

end


end GenericRegularity

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
