/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.FirstSmithIntegralNumerator
import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.SatzVIIIEquation33Iteration

/-!
# Hentzelt--Noether Satz VIII: from the first integral Smith numerator to equation (33)

Module for P22, controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
lines 13323--13380.

`FirstSmithIntegralNumerator` constructs a nonzero numerator over
`P[x₃, ...][x₂]` and proves its denominator action on every bounded
cutoff-one ground-module coordinate.  This file supplies the missing exact
coordinate transport.  Regular division represents an arbitrary element of
the full cutoff-one ground ideal by a bounded coordinate modulo the original
ideal; the two inverse `finSuccEquiv` maps then transport the bounded action
back to the original multivariate ring.  A genuinely late-variable
denominator becomes a polynomial free of the first two original variables,
which is precisely the multiplier required by equation (33).

The resulting numerator represents the selected localized greatest Smith
coefficient and satisfies `HasEquation33Witness I 1`.  It is not asserted to
be primitive, normalized, canonical, or independent of the Smith choices.
The file does not construct later Smith stages or the parallel `R^(i)`
resultant product.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open MvPolynomial
open RegularityDivision
open RegularitySpecialization

namespace RegularIdealDecomposition

noncomputable section

variable {P : Type*} [Field P]
variable {n k : ℕ}

set_option backward.defeqAttrib.useBackward true
attribute [local instance]
  RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- A constant polynomial transported back through `finSuccEquiv` is the
same polynomial with every variable shifted by one place. -/
@[simp]
theorem finSuccEquiv_symm_C_eq_rename_succ
    (b : MvPolynomial (Fin n) P) :
    (MvPolynomial.finSuccEquiv P n).symm (Polynomial.C b) =
      MvPolynomial.rename Fin.succ b := by
  apply (MvPolynomial.finSuccEquiv P n).injective
  simp only [AlgEquiv.apply_symm_apply]
  let f : MvPolynomial (Fin n) P →ₐ[P]
      Polynomial (MvPolynomial (Fin n) P) :=
    (MvPolynomial.finSuccEquiv P n).toAlgHom.comp
      (MvPolynomial.rename (R := P) Fin.succ)
  have hf : f =
      (Polynomial.CAlgHom : MvPolynomial (Fin n) P →ₐ[P]
        Polynomial (MvPolynomial (Fin n) P)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [f, MvPolynomial.finSuccEquiv_X_succ]
  exact (DFunLike.congr_fun hf b).symm

/-- Embed an integral polynomial in `x₂` with coefficients in the genuinely
later variables into the original ring in variables `x₁, x₂, x₃, ...`.

The inner inverse `finSuccEquiv` restores `x₂`; `Polynomial.C` makes the
result independent of `x₁`; the outer inverse restores the full variable
indexing. -/
noncomputable def secondVariableIntegralLift :
    Polynomial (MvPolynomial (Fin n) P) →+*
      MvPolynomial (Fin (n + 2)) P :=
  (MvPolynomial.finSuccEquiv P (n + 1)).symm.toRingEquiv.toRingHom.comp
    ((Polynomial.C : MvPolynomial (Fin (n + 1)) P →+*
      Polynomial (MvPolynomial (Fin (n + 1)) P)).comp
      (secondVariableCoefficientEquiv (P := P) (n := n)).symm.toRingHom)

/-- On a genuinely late-variable constant, the integral lift is the literal
double shift of variables. -/
@[simp]
theorem secondVariableIntegralLift_C
    (b : MvPolynomial (Fin n) P) :
    secondVariableIntegralLift (P := P) (n := n) (Polynomial.C b) =
      MvPolynomial.rename Fin.succ (MvPolynomial.rename Fin.succ b) := by
  simp [secondVariableIntegralLift, secondVariableCoefficientEquiv]

/-- The two coordinate equivalences and the constant-polynomial embedding do
not identify distinct integral numerators. -/
theorem secondVariableIntegralLift_injective :
    Function.Injective
      (secondVariableIntegralLift (P := P) (n := n)) := by
  intro a b hab
  have houter := congrArg (MvPolynomial.finSuccEquiv P (n + 1)) hab
  change
    MvPolynomial.finSuccEquiv P (n + 1)
        ((MvPolynomial.finSuccEquiv P (n + 1)).symm
          (Polynomial.C
            ((secondVariableCoefficientEquiv
              (P := P) (n := n)).symm a))) =
      MvPolynomial.finSuccEquiv P (n + 1)
        ((MvPolynomial.finSuccEquiv P (n + 1)).symm
          (Polynomial.C
            ((secondVariableCoefficientEquiv
              (P := P) (n := n)).symm b))) at houter
  rw [(MvPolynomial.finSuccEquiv P (n + 1)).apply_symm_apply,
    (MvPolynomial.finSuccEquiv P (n + 1)).apply_symm_apply] at houter
  exact (secondVariableCoefficientEquiv (P := P) (n := n)).symm.injective
    (Polynomial.C_injective houter)

/-- In particular, a nonzero integral numerator has a nonzero lift to the
original multivariate ring. -/
theorem secondVariableIntegralLift_ne_zero
    {a : Polynomial (MvPolynomial (Fin n) P)} (ha : a ≠ 0) :
    secondVariableIntegralLift (P := P) (n := n) a ≠ 0 := by
  simpa using
    (secondVariableIntegralLift_injective (P := P) (n := n)).ne ha

/-- Recover the full multivariate polynomial represented by a bounded
second-variable coordinate vector. -/
noncomputable def secondVariableBoundedFull
    (k : ℕ) (x : secondVariableBoundedAmbient P n k) :
    MvPolynomial (Fin (n + 2)) P :=
  (MvPolynomial.finSuccEquiv P (n + 1)).symm
    ((((secondVariableBoundedCoordinateEquiv
      (P := P) (n := n) k).symm x) :
        Polynomial.degreeLT (MvPolynomial (Fin (n + 1)) P) k) :
      Polynomial (MvPolynomial (Fin (n + 1)) P))

/-- Exposing the first variable after rebuilding a bounded coordinate simply
recovers the inverse coordinate polynomial. -/
@[simp]
theorem finSuccEquiv_secondVariableBoundedFull
    (k : ℕ) (x : secondVariableBoundedAmbient P n k) :
    MvPolynomial.finSuccEquiv P (n + 1)
        (secondVariableBoundedFull (P := P) (n := n) k x) =
      ((((secondVariableBoundedCoordinateEquiv
        (P := P) (n := n) k).symm x) :
          Polynomial.degreeLT (MvPolynomial (Fin (n + 1)) P) k) :
        Polynomial (MvPolynomial (Fin (n + 1)) P)) := by
  simp [secondVariableBoundedFull]

/-- Rebuilding the coordinates of a bounded polynomial returns its original
full multivariate representative. -/
@[simp]
theorem secondVariableBoundedFull_coordinate
    (r : Polynomial.degreeLT (MvPolynomial (Fin (n + 1)) P) k) :
    secondVariableBoundedFull (P := P) (n := n) k
        (secondVariableBoundedCoordinateEquiv
          (P := P) (n := n) k r) =
      (MvPolynomial.finSuccEquiv P (n + 1)).symm
        (r : Polynomial (MvPolynomial (Fin (n + 1)) P)) := by
  simp [secondVariableBoundedFull]

/-- Scalar multiplication of bounded coordinates agrees with multiplication
by the integral scalar lift in the original multivariate ring. -/
theorem secondVariableBoundedFull_smul
    (a : Polynomial (MvPolynomial (Fin n) P))
    (x : secondVariableBoundedAmbient P n k) :
    secondVariableBoundedFull (P := P) (n := n) k (a • x) =
      secondVariableIntegralLift (P := P) (n := n) a *
        secondVariableBoundedFull (P := P) (n := n) k x := by
  apply (MvPolynomial.finSuccEquiv P (n + 1)).injective
  rw [map_mul, finSuccEquiv_secondVariableBoundedFull,
    finSuccEquiv_secondVariableBoundedFull]
  change
    _ = MvPolynomial.finSuccEquiv P (n + 1)
        ((MvPolynomial.finSuccEquiv P (n + 1)).symm
          (Polynomial.C
            ((secondVariableCoefficientEquiv
              (P := P) (n := n)).symm a))) * _
  rw [(MvPolynomial.finSuccEquiv P (n + 1)).apply_symm_apply]
  have hsmul :=
    (secondVariableBoundedCoordinateEquiv
      (P := P) (n := n) k).symm.map_smulₛₗ a x
  have hval := congrArg Subtype.val hsmul
  change
    (↑((secondVariableBoundedCoordinateEquiv
      (P := P) (n := n) k).symm (a • x)) :
        Polynomial (MvPolynomial (Fin (n + 1)) P)) =
      (secondVariableCoefficientEquiv
        (P := P) (n := n)).symm a •
        (↑((secondVariableBoundedCoordinateEquiv
          (P := P) (n := n) k).symm x) :
          Polynomial (MvPolynomial (Fin (n + 1)) P)) at hval
  simpa only [Algebra.smul_def, Polynomial.algebraMap_eq] using hval

/-- Membership in the bounded original module transports back to membership
of the rebuilt representative in the original ideal. -/
theorem secondVariableBoundedFull_mem_original
    (I : Ideal (MvPolynomial (Fin (n + 2)) P))
    {x : secondVariableBoundedAmbient P n k}
    (hx : x ∈ secondVariableOriginalModule I k) :
    secondVariableBoundedFull (P := P) (n := n) k x ∈ I := by
  rw [secondVariableOriginalModule] at hx
  rcases hx with ⟨r, hr, rfl⟩
  change
    (MvPolynomial.finSuccEquiv P (n + 1)).symm
        (↑((secondVariableBoundedCoordinateEquiv
          (P := P) (n := n) k).symm
          (secondVariableBoundedCoordinateEquiv
            (P := P) (n := n) k r)) :
          Polynomial (MvPolynomial (Fin (n + 1)) P)) ∈ I
  rw [(secondVariableBoundedCoordinateEquiv
    (P := P) (n := n) k).symm_apply_apply]
  exact Ideal.symm_apply_mem_of_equiv_iff.mpr
    ((mem_boundedPartInDegreeLT_iff
      (finSuccIdeal (n := n + 1) I) r).mp hr)

/-- Regular division gives every cutoff-one ground-ideal element a bounded
second-variable coordinate representative modulo the original ideal. -/
theorem exists_secondVariableBoundedRepresentative_mod_original
    (I : Ideal (MvPolynomial (Fin (n + 2)) P))
    (C : MvPolynomial (Fin (n + 2)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 2)) k C)
    (hCI : C ∈ I)
    {g : MvPolynomial (Fin (n + 2)) P}
    (hg : g ∈ stageGroundIdeal (S := P) 1 I) :
    ∃ x : secondVariableBoundedAmbient P n k,
      x ∈ secondVariableGroundModule I k ∧
      g - secondVariableBoundedFull (P := P) (n := n) k x ∈ I := by
  let outer := MvPolynomial.finSuccEquiv P (n + 1)
  let rFull := boundedRepresentative C k g
  let r : Polynomial.degreeLT (MvPolynomial (Fin (n + 1)) P) k :=
    ⟨outer rFull, by
      exact Polynomial.mem_degreeLT.mpr (by
        simpa [outer, rFull] using
          degree_finSuccEquiv_boundedRepresentative_lt C g hC)⟩
  let x : secondVariableBoundedAmbient P n k :=
    secondVariableBoundedCoordinateEquiv (P := P) (n := n) k r
  have hCstage : outer C ∈ stageOneGroundIdeal I := by
    exact finSuccIdeal_le_stageOneGroundIdeal I
      (finSuccEquiv_mem_finSuccIdeal (n := n + 1) I hCI)
  have hgstage : outer g ∈ stageOneGroundIdeal I := by
    rw [stageOneGroundIdeal]
    exact Ideal.apply_mem_of_equiv_iff.mpr hg
  have hrStage :
      (r : Polynomial (MvPolynomial (Fin (n + 1)) P)) ∈
        stageOneGroundIdeal I := by
    have hrem := regularRemainder_mem_ideal
      (stageOneGroundIdeal I) C g k hCstage hgstage
    simpa [r, rFull, outer, boundedRepresentative] using hrem
  have hrBounded : r ∈
      boundedPartInDegreeLT (stageOneGroundIdeal I) k :=
    (mem_boundedPartInDegreeLT_iff (stageOneGroundIdeal I) r).mpr hrStage
  have hxGround : x ∈ secondVariableGroundModule I k := by
    rw [secondVariableGroundModule]
    exact ⟨r, hrBounded, rfl⟩
  have hfull :
      secondVariableBoundedFull (P := P) (n := n) k x = rFull := by
    simp [x, r, outer]
  obtain ⟨Q, hQ⟩ := exists_eq_boundedRepresentative_add_mul C g k
  have hdiff : g - rFull ∈ I := by
    have hCQ : C * Q ∈ I := I.mul_mem_right Q hCI
    have heq : g - rFull = C * Q := by
      rw [hQ]
      ring
    rwa [heq]
  exact ⟨x, hxGround, by simpa [hfull] using hdiff⟩

/-- A denominator in the genuinely later coefficient ring lifts to a
nonzero multiplier free of the first two original variables. -/
theorem secondVariableIntegralLift_denominator_mem_nonzeroLateVariableSubmonoid
    (d : lateVariableDenominators (P := P) (n := n)) :
    secondVariableIntegralLift (P := P) (n := n)
        (d : Polynomial (MvPolynomial (Fin n) P)) ∈
      nonzeroLateVariableSubmonoid (S := P) (n := n + 2) 2 := by
  rcases d.property with ⟨b, hb, hbd⟩
  rw [← hbd]
  change secondVariableIntegralLift (P := P) (n := n) (Polynomial.C b) ∈ _
  rw [mem_nonzeroLateVariableSubmonoid_iff,
    secondVariableIntegralLift_C]
  refine ⟨?_, ?_⟩
  · have hb0 : b ≠ 0 := nonZeroDivisors.coe_ne_zero ⟨b, hb⟩
    intro hzero
    apply hb0
    apply MvPolynomial.rename_injective Fin.succ (Fin.succ_injective _)
    apply MvPolynomial.rename_injective Fin.succ (Fin.succ_injective _)
    simpa using hzero
  · intro j hj hvars
    obtain ⟨q, hqvars, hqj⟩ :=
      MvPolynomial.mem_vars_rename Fin.succ _ hvars
    obtain ⟨i, _hivars, hiq⟩ :=
      MvPolynomial.mem_vars_rename Fin.succ _ hqvars
    have hqjval := congrArg Fin.val hqj
    have hiqval := congrArg Fin.val hiq
    simp at hqjval hiqval
    omega

/-- The bounded denominator action becomes the full elementwise
equation-(33) witness after regular bounded-representative transport. -/
theorem boundedAction_to_equation33Witness
    (I : Ideal (MvPolynomial (Fin (n + 2)) P))
    (C : MvPolynomial (Fin (n + 2)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 2)) k C)
    (hCI : C ∈ I)
    (a : Polynomial (MvPolynomial (Fin n) P))
    (hAction :
      ∀ x : secondVariableBoundedAmbient P n k,
        x ∈ secondVariableGroundModule I k →
          ∃ d : lateVariableDenominators (P := P) (n := n),
            (d : Polynomial (MvPolynomial (Fin n) P)) • (a • x) ∈
              secondVariableOriginalModule I k) :
    SatzVIIIOneStageDescent.HasEquation33Witness I 1
      (secondVariableIntegralLift (P := P) (n := n) a) := by
  intro g hg
  obtain ⟨x, hxGround, hgxI⟩ :=
    exists_secondVariableBoundedRepresentative_mod_original
      I C hC hCI hg
  obtain ⟨d, hdAction⟩ := hAction x hxGround
  let b : MvPolynomial (Fin (n + 2)) P :=
    secondVariableIntegralLift (P := P) (n := n)
      (d : Polynomial (MvPolynomial (Fin n) P))
  refine ⟨b,
    secondVariableIntegralLift_denominator_mem_nonzeroLateVariableSubmonoid d,
    ?_⟩
  have hbounded :
      b * (secondVariableIntegralLift (P := P) (n := n) a *
        secondVariableBoundedFull (P := P) (n := n) k x) ∈ I := by
    have hfull := secondVariableBoundedFull_mem_original I hdAction
    rw [secondVariableBoundedFull_smul,
      secondVariableBoundedFull_smul] at hfull
    simpa [b, mul_assoc] using hfull
  have hdiff :
      (b * secondVariableIntegralLift (P := P) (n := n) a) *
        (g - secondVariableBoundedFull (P := P) (n := n) k x) ∈ I :=
    I.mul_mem_left _ hgxI
  have hdecomp :
      b * (secondVariableIntegralLift (P := P) (n := n) a * g) =
        b * (secondVariableIntegralLift (P := P) (n := n) a *
          secondVariableBoundedFull (P := P) (n := n) k x) +
        (b * secondVariableIntegralLift (P := P) (n := n) a) *
          (g - secondVariableBoundedFull (P := P) (n := n) k x) := by
    ring
  rw [hdecomp]
  exact I.add_mem hbounded hdiff

/-- The selected greatest first Smith coefficient has a nonzero integral
numerator whose lift satisfies the full cutoff-one equation-(33) witness.
The retained equality records exactly which localized coefficient the
numerator represents. -/
theorem exists_nonzero_integralSmithNumerator_hasEquation33Witness
    (I : Ideal (MvPolynomial (Fin (n + 2)) P))
    (C : MvPolynomial (Fin (n + 2)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 2)) k C)
    (hCI : C ∈ I)
    (i : localizedSecondVariableSmithIndex I k)
    (hgreat : localizedSecondVariableIsGreatestRemainingDivisor I k ∅ i) :
    ∃ a : Polynomial (MvPolynomial (Fin n) P),
      a ≠ 0 ∧
      secondVariableIntegralLift (P := P) (n := n) a ≠ 0 ∧
      (∃ s : lateVariableDenominators (P := P) (n := n),
        localizedSecondVariableSmithCoefficients I k i *
            Polynomial.map
              (algebraMap (MvPolynomial (Fin n) P)
                (FractionRing (MvPolynomial (Fin n) P)))
              (s : Polynomial (MvPolynomial (Fin n) P)) =
          Polynomial.map
            (algebraMap (MvPolynomial (Fin n) P)
              (FractionRing (MvPolynomial (Fin n) P))) a) ∧
      SatzVIIIOneStageDescent.HasEquation33Witness I 1
        (secondVariableIntegralLift (P := P) (n := n) a) := by
  obtain ⟨a, ha, s, hclear, hAction⟩ :=
    exists_nonzero_integralSmithNumerator_with_denominator_action
      I k i hgreat
  refine ⟨a, ha, secondVariableIntegralLift_ne_zero ha,
    ⟨s, hclear⟩, ?_⟩
  exact boundedAction_to_equation33Witness I C hC hCI a hAction

#print axioms finSuccEquiv_symm_C_eq_rename_succ
#print axioms secondVariableIntegralLift
#print axioms secondVariableIntegralLift_C
#print axioms secondVariableIntegralLift_injective
#print axioms secondVariableIntegralLift_ne_zero
#print axioms secondVariableBoundedFull
#print axioms finSuccEquiv_secondVariableBoundedFull
#print axioms secondVariableBoundedFull_coordinate
#print axioms secondVariableBoundedFull_smul
#print axioms secondVariableBoundedFull_mem_original
#print axioms exists_secondVariableBoundedRepresentative_mod_original
#print axioms secondVariableIntegralLift_denominator_mem_nonzeroLateVariableSubmonoid
#print axioms boundedAction_to_equation33Witness
#print axioms exists_nonzero_integralSmithNumerator_hasEquation33Witness

end

end RegularIdealDecomposition

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
