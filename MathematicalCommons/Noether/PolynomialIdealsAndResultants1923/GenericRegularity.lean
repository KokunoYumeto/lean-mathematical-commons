/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.GenericParameters
import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.RegularitySpecialization
import Mathlib.Algebra.MvPolynomial.Polynomial
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
preserves homogeneous degree. It defines the exact pure-power coefficient
whose nonvanishing makes the first variable regular over the independent-
parameter fraction field. On generators, that coefficient is `1` for the
first generator and the independent parameter indexed by `(i,0)` for every
later generator.

The generic nonvanishing argument is also formalized. Setting the first
variable to one dehomogenizes a homogeneous polynomial injectively. Evaluating
that dehomogenization at the algebraically independent first-column parameters
is therefore nonzero. This identifies exactly with the generic leading
coefficient, so every nonzero homogeneous input becomes regular in the first
variable.
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

/-- Set the first variable to one while retaining all later variables. -/
def firstDehomogenization
    {N : ℕ} (F : MvPolynomial (Fin (N + 1)) P) :
    MvPolynomial (Fin N) P :=
  Polynomial.eval 1 (MvPolynomial.finSuccEquiv P N F)

/-- For a homogeneous polynomial, evaluation on the first coordinate axis is
its pure first-variable coefficient. -/
theorem eval_firstAxis_eq_purePowerCoefficient
    {N r : ℕ} {F : MvPolynomial (Fin (N + 1)) P}
    (hF : IsHomogeneous F r) :
    MvPolynomial.eval (Fin.cons 1 0) F =
      MvPolynomial.coeff (Finsupp.single (0 : Fin (N + 1)) r) F := by
  by_cases hF0 : F = 0
  · simp [hF0]
  have hdeg : (MvPolynomial.finSuccEquiv P N F).natDegree < r + 1 := by
    linarith [MvPolynomial.natDegree_finSuccEquiv F,
      MvPolynomial.degreeOf_le_totalDegree F 0, hF.totalDegree hF0]
  have aux : ∀ i ∈ Finset.range r,
      MvPolynomial.constantCoeff
        ((MvPolynomial.finSuccEquiv P N F).coeff i) = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    apply (hF.finSuccEquiv_coeff_isHomogeneous i (r - i) (by omega)).coeff_eq_zero
    simp only [map_zero]
    rw [← Nat.sub_ne_zero_iff_lt] at hi
    exact hi.symm
  have hcons : (0 : Fin N →₀ ℕ).cons r =
      Finsupp.single (0 : Fin (N + 1)) r := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  simp_rw [MvPolynomial.eval_eq_eval_mv_eval', Polynomial.eval_one_map,
    Polynomial.eval_eq_sum_range' hdeg, MvPolynomial.eval_zero, one_pow,
    mul_one, map_sum, Finset.sum_range_succ, Finset.sum_eq_zero aux, zero_add]
  have hcoeff :=
    MvPolynomial.finSuccEquiv_coeff_coeff (0 : Fin N →₀ ℕ) F r
  rw [hcons] at hcoeff
  simpa only [MvPolynomial.constantCoeff_eq] using hcoeff

/-- Dehomogenizing a nonzero homogeneous polynomial by setting the first
variable to one remains nonzero. -/
theorem firstDehomogenization_ne_zero
    {N r : ℕ} {F : MvPolynomial (Fin (N + 1)) P}
    (hF : IsHomogeneous F r) (hF0 : F ≠ 0) :
    firstDehomogenization F ≠ 0 := by
  let p := MvPolynomial.finSuccEquiv P N F
  have hp0 : p ≠ 0 := (MvPolynomial.finSuccEquiv P N).injective.ne hF0
  obtain ⟨i, hi⟩ : ∃ i : ℕ, p.coeff i ≠ 0 := by
    contrapose! hp0
    exact Polynomial.ext (by simpa using hp0)
  have hdeg : p.natDegree < r + 1 := by
    dsimp [p]
    linarith [MvPolynomial.natDegree_finSuccEquiv F,
      MvPolynomial.degreeOf_le_totalDegree F 0, hF.totalDegree hF0]
  have hiNat : i ≤ p.natDegree := Polynomial.le_natDegree_of_ne_zero hi
  have hir : i ≤ r := Nat.lt_succ_iff.mp (hiNat.trans_lt hdeg)
  intro hzero
  have heval := hzero
  rw [firstDehomogenization, Polynomial.eval_eq_sum_range' hdeg] at heval
  simp only [one_pow, mul_one] at heval
  have hprojection := congrArg
    (fun q : MvPolynomial (Fin N) P ↦ MvPolynomial.homogeneousComponent (r - i) q)
    heval
  simp only [map_sum, map_zero] at hprojection
  have hsingle :
      ∑ j ∈ Finset.range (r + 1),
          MvPolynomial.homogeneousComponent (r - i) (p.coeff j) =
        p.coeff i := by
    have hihom : IsHomogeneous (p.coeff i) (r - i) := by
      dsimp [p]
      exact hF.finSuccEquiv_coeff_isHomogeneous i (r - i) (by omega)
    have hicomponent :
        MvPolynomial.homogeneousComponent (r - i) (p.coeff i) = p.coeff i := by
      rw [MvPolynomial.homogeneousComponent_of_mem hihom]
      simp
    rw [← hicomponent]
    apply Finset.sum_eq_single i
    · intro j hj hji
      have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hjhom : IsHomogeneous (p.coeff j) (r - j) := by
        dsimp [p]
        exact hF.finSuccEquiv_coeff_isHomogeneous j (r - j) (by omega)
      rw [MvPolynomial.homogeneousComponent_of_mem hjhom, if_neg (by omega)]
    · intro hiNot
      exact (hiNot (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hir))).elim
  rw [hsingle] at hprojection
  exact hi hprojection

/-- The independent parameter in row `j+1` and the first column. -/
def firstColumnParameter {N : ℕ} (j : Fin N) : LowerParameter (N + 1) :=
  ⟨(j.succ, 0), by
    change 0 < j.val + 1
    omega⟩

theorem firstColumnParameter_injective {N : ℕ} :
    Function.Injective (firstColumnParameter (N := N)) := by
  intro i j hij
  have hs : i.succ = j.succ :=
    congrArg (fun p : LowerParameter (N + 1) ↦ p.1.1) hij
  exact Fin.succ_injective N hs

/-- The corresponding parameter variable in the generic coefficient field. -/
def firstColumnValue {N : ℕ} (j : Fin N) : ParameterField (P := P) (N + 1) :=
  algebraMap (MvPolynomial (LowerParameter (N + 1)) P)
    (ParameterField (P := P) (N + 1)) (X (firstColumnParameter j))

theorem firstColumnValue_algebraicIndependent {N : ℕ} :
    AlgebraicIndependent P (firstColumnValue (P := P) (N := N)) := by
  change AlgebraicIndependent P
    ((fun p : LowerParameter (N + 1) ↦
        algebraMap (MvPolynomial (LowerParameter (N + 1)) P)
          (FractionRing (MvPolynomial (LowerParameter (N + 1)) P)) (X p)) ∘
      firstColumnParameter (N := N))
  exact (independentParameterVariables_algebraicIndependent
    (P := P) (n := N + 1)).comp
      (firstColumnParameter (N := N)) firstColumnParameter_injective

/-- Evaluating a lower image on the first coordinate axis retains only its
first-column entry. -/
theorem eval_firstAxis_lowerImage
    {R : Type*} [CommRing R] {N : ℕ}
    (u : Fin (N + 1) → Fin (N + 1) → R) (i : Fin (N + 1)) :
    MvPolynomial.eval (Fin.cons 1 0) (CoordinateShear.lowerImage u i) =
      Fin.cases 1 (fun j : Fin N ↦ u j.succ 0) i := by
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · simp [CoordinateShear.lowerImage]
    apply Finset.sum_eq_zero
    intro j hj
    have hlt : j < (0 : Fin (N + 1)) := Finset.mem_Iio.mp hj
    exact (not_lt_of_ge (Fin.zero_le j) hlt).elim
  · rw [CoordinateShear.lowerImage]
    simp only [map_add, MvPolynomial.eval_X, Fin.cons_succ, Pi.zero_apply,
      map_sum, map_mul, MvPolynomial.eval_C, zero_add]
    rw [Finset.sum_eq_single (0 : Fin (N + 1))]
    · simp
    · intro j _hj hne
      obtain hj0 | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
      · exact (hne hj0).elim
      · simp
    · intro hnot
      exact (hnot (Finset.mem_Iio.mpr (by
        change 0 < k.val + 1
        omega))).elim

theorem eval_firstAxis_independentGenericTransform
    {N : ℕ} (F : MvPolynomial (Fin (N + 1)) P) :
    MvPolynomial.eval (Fin.cons 1 0)
        (independentGenericTransform (P := P) F) =
      MvPolynomial.eval₂ (algebraMap P (ParameterField (P := P) (N + 1)))
        (Fin.cases 1 (firstColumnValue (P := P) (N := N))) F := by
  have hhom :
      (MvPolynomial.eval
        (Fin.cons 1 0 : Fin (N + 1) → ParameterField (P := P) (N + 1))).comp
          (genericTransformHom (P := P) (U := LowerParameter (N + 1))
            (independentLowerUnitriangularEquiv (P := P) (n := N + 1))) =
        MvPolynomial.eval₂Hom
          (algebraMap P (ParameterField (P := P) (N + 1)))
          (Fin.cases 1 (firstColumnValue (P := P) (N := N))) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change MvPolynomial.eval (Fin.cons 1 0)
        (independentLowerUnitriangularEquiv (P := P) (n := N + 1)
          (MvPolynomial.map
            (algebraMap P (ParameterField (P := P) (N + 1))) (C c))) = _
      rw [MvPolynomial.map_C]
      have hc :=
        (independentLowerUnitriangularEquiv (P := P) (n := N + 1)).commutes
          (algebraMap P (ParameterField (P := P) (N + 1)) c)
      change independentLowerUnitriangularEquiv (P := P) (n := N + 1)
          (C (algebraMap P (ParameterField (P := P) (N + 1)) c)) =
        C (algebraMap P (ParameterField (P := P) (N + 1)) c) at hc
      rw [hc]
      simp
    · intro i
      change MvPolynomial.eval (Fin.cons 1 0)
        (independentLowerUnitriangularEquiv (P := P) (n := N + 1)
          (MvPolynomial.map
            (algebraMap P (ParameterField (P := P) (N + 1))) (X i))) = _
      rw [MvPolynomial.map_X, independentLowerUnitriangularEquiv_X]
      change MvPolynomial.eval (Fin.cons 1 0)
        (CoordinateShear.lowerImage (independentLowerMatrix P) i) = _
      rw [eval_firstAxis_lowerImage]
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp
      · simp [firstColumnValue, firstColumnParameter,
          independentLowerMatrix_of_lt]
  change ((MvPolynomial.eval (Fin.cons 1 0)).comp
    (genericTransformHom (P := P) (U := LowerParameter (N + 1))
      (independentLowerUnitriangularEquiv (P := P) (n := N + 1)))) F = _
  exact RingHom.congr_fun hhom F

theorem aeval_firstDehomogenization
    {N : ℕ} (F : MvPolynomial (Fin (N + 1)) P) :
    MvPolynomial.aeval (firstColumnValue (P := P) (N := N))
        (firstDehomogenization F) =
      MvPolynomial.eval₂ (algebraMap P (ParameterField (P := P) (N + 1)))
        (Fin.cases 1 (firstColumnValue (P := P) (N := N))) F := by
  let L : MvPolynomial (Fin (N + 1)) P →+*
      ParameterField (P := P) (N + 1) :=
    (MvPolynomial.aeval
      (firstColumnValue (P := P) (N := N))).toRingHom.comp
        ((Polynomial.evalRingHom 1).comp
          (MvPolynomial.finSuccEquiv P N).toRingEquiv.toRingHom)
  have hL : L = MvPolynomial.eval₂Hom
      (algebraMap P (ParameterField (P := P) (N + 1)))
      (Fin.cases 1 (firstColumnValue (P := P) (N := N))) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      dsimp [L]
      change MvPolynomial.aeval (firstColumnValue (P := P) (N := N))
        (Polynomial.eval 1 (MvPolynomial.finSuccEquiv P N (C c))) = _
      simp [MvPolynomial.finSuccEquiv_apply]
    · intro i
      simp only [L, RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · change MvPolynomial.aeval (firstColumnValue (P := P) (N := N))
          (Polynomial.eval 1 (MvPolynomial.finSuccEquiv P N (X 0))) = 1
        rw [MvPolynomial.finSuccEquiv_X_zero]
        simp
      · change MvPolynomial.aeval (firstColumnValue (P := P) (N := N))
          (Polynomial.eval 1 (MvPolynomial.finSuccEquiv P N (X j.succ))) =
            firstColumnValue j
        rw [MvPolynomial.finSuccEquiv_X_succ]
        simp
  change L F = _
  exact RingHom.congr_fun hL F

/-- The generic leading coefficient is the dehomogenized input evaluated at
the algebraically independent first-column parameters. -/
theorem independentGenericLeadingCoefficient_eq_aeval_firstDehomogenization
    {N r : ℕ} {F : MvPolynomial (Fin (N + 1)) P}
    (hF : IsHomogeneous F r) :
    independentGenericLeadingCoefficient (P := P) (Nat.succ_pos N) F r =
      MvPolynomial.aeval (firstColumnValue (P := P) (N := N))
        (firstDehomogenization F) := by
  rw [aeval_firstDehomogenization]
  unfold independentGenericLeadingCoefficient
  change MvPolynomial.coeff
    (Finsupp.single (0 : Fin (N + 1)) r)
      (independentGenericTransform (P := P) F) = _
  rw [← eval_firstAxis_eq_purePowerCoefficient
    (independentGenericTransform_isHomogeneous (P := P) hF)]
  exact eval_firstAxis_independentGenericTransform F

/-- The missing generic nonvanishing step: every nonzero homogeneous input
has a nonzero generic first-variable leading coefficient. -/
theorem independentGenericLeadingCoefficient_ne_zero
    {N r : ℕ} {F : MvPolynomial (Fin (N + 1)) P}
    (hF : IsHomogeneous F r) (hF0 : F ≠ 0) :
    independentGenericLeadingCoefficient (P := P) (Nat.succ_pos N) F r ≠ 0 := by
  rw [independentGenericLeadingCoefficient_eq_aeval_firstDehomogenization hF]
  have hdehom := firstDehomogenization_ne_zero hF hF0
  intro hzero
  apply hdehom
  apply firstColumnValue_algebraicIndependent (P := P) (N := N)
  simpa using hzero

/-- Every nonzero homogeneous polynomial becomes regular in the first variable
under the source-faithful independent generic transform. -/
theorem independentGenericTransform_isRegularInDegree
    {N r : ℕ} {F : MvPolynomial (Fin (N + 1)) P}
    (hF : IsHomogeneous F r) (hF0 : F ≠ 0) :
    IsRegularInDegree (0 : Fin (N + 1)) r
      (independentGenericTransform (P := P) F) := by
  exact independentGenericTransform_isRegularInDegree_of_leadingCoefficient_ne_zero
    (Nat.succ_pos N) hF (independentGenericLeadingCoefficient_ne_zero hF hF0)

/-- The highest homogeneous component of a polynomial. -/
def topHomogeneousComponent (F : MvPolynomial (Fin (N + 1)) P) :
    MvPolynomial (Fin (N + 1)) P :=
  MvPolynomial.homogeneousComponent F.totalDegree F

theorem topHomogeneousComponent_isHomogeneous
    (F : MvPolynomial (Fin (N + 1)) P) :
    IsHomogeneous (topHomogeneousComponent F) F.totalDegree := by
  exact MvPolynomial.homogeneousComponent_isHomogeneous _ _

theorem topHomogeneousComponent_ne_zero
    {F : MvPolynomial (Fin (N + 1)) P} (hF0 : F ≠ 0) :
    topHomogeneousComponent F ≠ 0 := by
  have hs : F.support.Nonempty := MvPolynomial.support_nonempty.mpr hF0
  have hsup := Finset.sup_mem_of_nonempty
    (f := fun s : Fin (N + 1) →₀ ℕ ↦ s.sum fun _ e ↦ e) hs
  obtain ⟨d, hd, hdegree⟩ := hsup
  have hcoeff : MvPolynomial.coeff d F ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  intro hzero
  have hz := congrArg (MvPolynomial.coeff d) hzero
  rw [topHomogeneousComponent, MvPolynomial.coeff_homogeneousComponent] at hz
  have hdtotal : d.degree = F.totalDegree := by
    change (d.sum fun _ e ↦ e) =
      F.support.sup fun s ↦ s.sum fun _ e ↦ e
    exact hdegree
  rw [if_pos hdtotal] at hz
  exact hcoeff (by simpa using hz)

/-- The top component really is the component at the polynomial's total
degree. -/
theorem homogeneousComponent_totalDegree_eq_top
    (F : MvPolynomial (Fin (N + 1)) P) :
    MvPolynomial.homogeneousComponent F.totalDegree F =
      topHomogeneousComponent F := rfl

/-- A linear homogeneous coordinate transform cannot increase total degree. -/
theorem independentGenericTransform_totalDegree_le
    (F : MvPolynomial (Fin (N + 1)) P) :
    (independentGenericTransform (P := P) F).totalDegree ≤ F.totalDegree := by
  have htransform : independentGenericTransform (P := P) F =
      ∑ i ∈ Finset.range (F.totalDegree + 1),
        independentGenericTransform (P := P)
          (MvPolynomial.homogeneousComponent i F) := by
    calc
      independentGenericTransform (P := P) F =
          independentGenericTransform (P := P)
            (∑ i ∈ Finset.range (F.totalDegree + 1),
              MvPolynomial.homogeneousComponent i F) :=
        congrArg (independentGenericTransform (P := P))
          F.sum_homogeneousComponent.symm
      _ = _ := by simp only [independentGenericTransform, map_sum]
  calc
    (independentGenericTransform (P := P) F).totalDegree =
        (∑ i ∈ Finset.range (F.totalDegree + 1),
          independentGenericTransform (P := P)
            (MvPolynomial.homogeneousComponent i F)).totalDegree :=
      congrArg MvPolynomial.totalDegree htransform
    _ ≤ F.totalDegree := by
      apply MvPolynomial.totalDegree_finsetSum_le
      intro i hi
      have hir : i ≤ F.totalDegree :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hhom : IsHomogeneous
          (independentGenericTransform (P := P)
            (MvPolynomial.homogeneousComponent i F)) i :=
        independentGenericTransform_isHomogeneous (P := P)
          (MvPolynomial.homogeneousComponent_isHomogeneous i F)
      by_cases hz : independentGenericTransform (P := P)
          (MvPolynomial.homogeneousComponent i F) = 0
      · simp [hz]
      · exact (hhom.totalDegree hz).le.trans hir

/-- At top degree, the pure first-variable coefficient depends only on the
top homogeneous component. -/
theorem independentGenericLeadingCoefficient_eq_topHomogeneousComponent
    (F : MvPolynomial (Fin (N + 1)) P) :
    independentGenericLeadingCoefficient (P := P) (Nat.succ_pos N)
        F F.totalDegree =
      independentGenericLeadingCoefficient (P := P) (Nat.succ_pos N)
        (topHomogeneousComponent F) F.totalDegree := by
  unfold independentGenericLeadingCoefficient
  have htransform : independentGenericTransform (P := P) F =
      ∑ i ∈ Finset.range (F.totalDegree + 1),
        independentGenericTransform (P := P)
          (MvPolynomial.homogeneousComponent i F) := by
    calc
      independentGenericTransform (P := P) F =
          independentGenericTransform (P := P)
            (∑ i ∈ Finset.range (F.totalDegree + 1),
              MvPolynomial.homogeneousComponent i F) :=
        congrArg (independentGenericTransform (P := P))
          F.sum_homogeneousComponent.symm
      _ = _ := by simp only [independentGenericTransform, map_sum]
  rw [htransform, MvPolynomial.coeff_sum,
    Finset.sum_eq_single F.totalDegree]
  · rfl
  · intro i hi hine
    have hhom : IsHomogeneous
        (independentGenericTransform (P := P)
          (MvPolynomial.homogeneousComponent i F)) i :=
      independentGenericTransform_isHomogeneous (P := P)
        (MvPolynomial.homogeneousComponent_isHomogeneous i F)
    apply hhom.coeff_eq_zero
    simpa only [Finsupp.degree_single] using hine.symm
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_self _))).elim

/-- The generic pure first-variable coefficient at total degree is nonzero for
every nonzero polynomial, without a homogeneity assumption. -/
theorem independentGenericLeadingCoefficient_totalDegree_ne_zero
    {F : MvPolynomial (Fin (N + 1)) P} (hF0 : F ≠ 0) :
    independentGenericLeadingCoefficient (P := P) (Nat.succ_pos N)
      F F.totalDegree ≠ 0 := by
  rw [independentGenericLeadingCoefficient_eq_topHomogeneousComponent]
  exact independentGenericLeadingCoefficient_ne_zero
    (topHomogeneousComponent_isHomogeneous F)
    (topHomogeneousComponent_ne_zero hF0)

/-- The source-faithful independent generic transform preserves total degree
of every nonzero polynomial. -/
theorem independentGenericTransform_totalDegree
    {F : MvPolynomial (Fin (N + 1)) P} (hF0 : F ≠ 0) :
    (independentGenericTransform (P := P) F).totalDegree = F.totalDegree := by
  apply le_antisymm
  · exact independentGenericTransform_totalDegree_le F
  · have hcoeff := independentGenericLeadingCoefficient_totalDegree_ne_zero
      (P := P) hF0
    have hmem : Finsupp.single (0 : Fin (N + 1)) F.totalDegree ∈
        (independentGenericTransform (P := P) F).support := by
      rw [MvPolynomial.mem_support_iff]
      exact hcoeff
    simpa using MvPolynomial.le_totalDegree hmem

/-- Every nonzero polynomial becomes regular in the first variable at its
total degree under the generic equation-(12) transform. -/
theorem independentGenericTransform_isRegular
    {F : MvPolynomial (Fin (N + 1)) P} (hF0 : F ≠ 0) :
    IsRegularInDegree (0 : Fin (N + 1)) F.totalDegree
      (independentGenericTransform (P := P) F) := by
  exact ⟨independentGenericTransform_totalDegree hF0,
    independentGenericLeadingCoefficient_totalDegree_ne_zero hF0⟩

/-- The ideal obtained by applying the independent equation-(12) transform to
all members of a source ideal. -/
noncomputable def independentGenericTransformIdeal
    (I : Ideal (MvPolynomial (Fin (N + 1)) P)) :
    Ideal (MvPolynomial (Fin (N + 1)) (ParameterField (P := P) (N + 1))) :=
  genericTransformIdeal (P := P)
    (CoordinateShear.IndependentParameters.independentLowerUnitriangularEquiv
      (P := P) (n := N + 1)) I

/-- The transform of each source-ideal member belongs to the transformed
ideal. -/
theorem independentGenericTransform_mem_independentGenericTransformIdeal
    (I : Ideal (MvPolynomial (Fin (N + 1)) P))
    {F : MvPolynomial (Fin (N + 1)) P} (hFI : F ∈ I) :
    independentGenericTransform (P := P) F ∈
      independentGenericTransformIdeal (P := P) I := by
  exact Ideal.mem_map_of_mem _ hFI

/-- Every nonzero source ideal has a member whose source-faithful generic
transform is regular in the first variable. -/
theorem exists_regular_member_independentGenericTransformIdeal
    (I : Ideal (MvPolynomial (Fin (N + 1)) P)) (hI : I ≠ ⊥) :
    ∃ r G, G ∈ independentGenericTransformIdeal (P := P) I ∧
      IsRegularInDegree (0 : Fin (N + 1)) r G := by
  obtain ⟨F, hFI, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  exact ⟨F.totalDegree, independentGenericTransform (P := P) F,
    independentGenericTransform_mem_independentGenericTransformIdeal I hFI,
    independentGenericTransform_isRegular hF0⟩

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
#print axioms eval_firstAxis_eq_purePowerCoefficient
#print axioms firstDehomogenization_ne_zero
#print axioms firstColumnParameter_injective
#print axioms firstColumnValue_algebraicIndependent
#print axioms eval_firstAxis_lowerImage
#print axioms eval_firstAxis_independentGenericTransform
#print axioms aeval_firstDehomogenization
#print axioms independentGenericLeadingCoefficient_eq_aeval_firstDehomogenization
#print axioms independentGenericLeadingCoefficient_ne_zero
#print axioms independentGenericTransform_isRegularInDegree
#print axioms topHomogeneousComponent_isHomogeneous
#print axioms topHomogeneousComponent_ne_zero
#print axioms independentGenericTransform_totalDegree_le
#print axioms independentGenericLeadingCoefficient_eq_topHomogeneousComponent
#print axioms independentGenericLeadingCoefficient_totalDegree_ne_zero
#print axioms independentGenericTransform_totalDegree
#print axioms independentGenericTransform_isRegular
#print axioms independentGenericTransform_mem_independentGenericTransformIdeal
#print axioms exists_regular_member_independentGenericTransformIdeal
#print axioms independentGenericLeadingCoefficient_X_zero
#print axioms independentGenericLeadingCoefficient_X_of_pos

end


end GenericRegularity

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
