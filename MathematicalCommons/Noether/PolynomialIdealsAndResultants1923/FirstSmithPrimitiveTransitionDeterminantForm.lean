/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.FirstSmithPrimitiveCoefficientProductForm

/-!
# Hentzelt--Noether Satz VIII: a primitive selected-transition determinant form

Module for P22, controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
lines 13323--13327.

At source stage `i = 2`, those lines identify the product of the elementary
divisors with the determinant of a transition substitution and then name the
resulting historical form `R^(2)`.  The present file records the portion that
the constructed localized Smith pair already supports: in its selected Smith
bases, the transition determinant is exactly the finite product of the
selected Smith coefficients.  It is therefore associated, after localizing
the late-variable coefficient ring, with the primitive integral product
representative constructed in the preceding module.  Changing the linear
equivalence used to identify the localized ground and denominator modules
changes this determinant only by association.

This is still selected-basis packaging.  It does not identify the primitive
representative with historical `R^(2)`, define the source's module norm, or
prove a resultant or maximal-minor-gcd characterization.  It also proves no
canonical normalization, no independence of the underlying Smith object, and
no later-stage statement.  The local zero-based cutoff `1` remains source
stage `i = 2`.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open RegularitySpecialization

namespace RegularIdealDecomposition

noncomputable section

variable {P : Type*} [Field P]
variable {n k : ℕ}

/-- Determinant of a chosen linear equivalence from the localized ground module
to its relative denominator.  This is not a definition of the source's
historical module norm. -/
noncomputable def localizedSecondVariableTransitionDeterminant
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (u : localizedSecondVariableGroundModule I k ≃ₗ[secondVariablePID P n]
      CommonTailQuotient.relativeDenominator
        (R := secondVariablePID P n)
        (E := localizedSecondVariableBoundedAmbient P n k)
        (localizedSecondVariableGroundModule I k)
        (localizedSecondVariableOriginalModule I k)) :
    secondVariablePID P n :=
  letI : Semiring (secondVariablePID P n) :=
    (inferInstance : CommRing (secondVariablePID P n)).toSemiring
  letI : AddCommMonoid (localizedSecondVariableBoundedAmbient P n k) :=
    (inferInstance : AddCommGroup (localizedSecondVariableBoundedAmbient P n k)).toAddCommMonoid
  letI : AddCommGroup (localizedSecondVariableGroundModule I k) :=
    (localizedSecondVariableGroundModule I k).toAddSubgroup.toAddCommGroup
  letI : AddCommMonoid (localizedSecondVariableGroundModule I k) :=
    (inferInstance : AddCommGroup (localizedSecondVariableGroundModule I k)).toAddCommMonoid
  letI : AddCommGroup
      (CommonTailQuotient.relativeDenominator
        (R := secondVariablePID P n)
        (E := localizedSecondVariableBoundedAmbient P n k)
        (localizedSecondVariableGroundModule I k)
        (localizedSecondVariableOriginalModule I k)) :=
    (CommonTailQuotient.relativeDenominator
      (R := secondVariablePID P n)
      (E := localizedSecondVariableBoundedAmbient P n k)
      (localizedSecondVariableGroundModule I k)
      (localizedSecondVariableOriginalModule I k)).toAddSubgroup.toAddCommGroup
  letI : AddCommMonoid
      (CommonTailQuotient.relativeDenominator
        (R := secondVariablePID P n)
        (E := localizedSecondVariableBoundedAmbient P n k)
        (localizedSecondVariableGroundModule I k)
        (localizedSecondVariableOriginalModule I k)) :=
    (inferInstance : AddCommGroup
      (CommonTailQuotient.relativeDenominator
        (R := secondVariablePID P n)
        (E := localizedSecondVariableBoundedAmbient P n k)
        (localizedSecondVariableGroundModule I k)
        (localizedSecondVariableOriginalModule I k))).toAddCommMonoid
  LinearMap.det
    ((CommonTailQuotient.relativeDenominator
      (R := secondVariablePID P n)
      (E := localizedSecondVariableBoundedAmbient P n k)
      (localizedSecondVariableGroundModule I k)
      (localizedSecondVariableOriginalModule I k)).subtype.comp
        u.toLinearMap)

/-- The selected-basis transition determinant used in the source-facing
packaging. -/
noncomputable def localizedSecondVariableSelectedSmithTransitionDeterminant
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    secondVariablePID P n :=
  localizedSecondVariableTransitionDeterminant I k
    ((localizedSecondVariableEtaBasis I k).equiv
      (localizedSecondVariableDenominatorBasis I k)
      (Equiv.refl (localizedSecondVariableSmithIndex I k)))

/-- In the selected localized Smith bases, the transition determinant is
exactly the finite product of the selected Smith coefficients. -/
theorem det_localizedSecondVariableSelectedSmithTransition_eq_product
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    localizedSecondVariableSelectedSmithTransitionDeterminant I k =
      localizedSecondVariableSmithCoefficientProduct I k := by
  simpa only [localizedSecondVariableSelectedSmithTransitionDeterminant,
    localizedSecondVariableTransitionDeterminant,
    localizedSecondVariableSmithCoefficientProduct,
    SmithAnnihilatorBounds.coefficientProduct,
    localizedSecondVariableEtaBasis,
    localizedSecondVariableDenominatorBasis,
    localizedSecondVariableSmithCoefficients] using
    (det_localizedSecondVariableSmithBasisTransition_eq_prod
      (P := P) (n := n) I k)

/-- Any other linear equivalence from the localized ground module to its
relative denominator gives a transition determinant associated to the one
from the selected Smith bases.  This is basis-change control only; it does not
make the selected Smith object itself canonical. -/
theorem localizedSecondVariable_transitionDet_associated_selectedSmithTransition
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (u : localizedSecondVariableGroundModule I k ≃ₗ[secondVariablePID P n]
      CommonTailQuotient.relativeDenominator
        (R := secondVariablePID P n)
        (E := localizedSecondVariableBoundedAmbient P n k)
        (localizedSecondVariableGroundModule I k)
        (localizedSecondVariableOriginalModule I k)) :
    Associated
      (localizedSecondVariableTransitionDeterminant I k u)
      (localizedSecondVariableSelectedSmithTransitionDeterminant I k) := by
  unfold localizedSecondVariableTransitionDeterminant
  -- The determinant API uses the coherent `CommRing`/`AddCommGroup`
  -- parent instances; the local aliases make the subtype maps share them.
  letI : Semiring (secondVariablePID P n) :=
    (inferInstance : CommRing (secondVariablePID P n)).toSemiring
  letI : AddCommMonoid (localizedSecondVariableBoundedAmbient P n k) :=
    (inferInstance : AddCommGroup (localizedSecondVariableBoundedAmbient P n k)).toAddCommMonoid
  letI : AddCommGroup (localizedSecondVariableGroundModule I k) :=
    (localizedSecondVariableGroundModule I k).toAddSubgroup.toAddCommGroup
  letI : AddCommMonoid (localizedSecondVariableGroundModule I k) :=
    (inferInstance : AddCommGroup (localizedSecondVariableGroundModule I k)).toAddCommMonoid
  letI : AddCommGroup
      (CommonTailQuotient.relativeDenominator
        (R := secondVariablePID P n)
        (E := localizedSecondVariableBoundedAmbient P n k)
        (localizedSecondVariableGroundModule I k)
        (localizedSecondVariableOriginalModule I k)) :=
    (CommonTailQuotient.relativeDenominator
      (R := secondVariablePID P n)
      (E := localizedSecondVariableBoundedAmbient P n k)
      (localizedSecondVariableGroundModule I k)
      (localizedSecondVariableOriginalModule I k)).toAddSubgroup.toAddCommGroup
  letI : AddCommMonoid
      (CommonTailQuotient.relativeDenominator
        (R := secondVariablePID P n)
        (E := localizedSecondVariableBoundedAmbient P n k)
        (localizedSecondVariableGroundModule I k)
        (localizedSecondVariableOriginalModule I k)) :=
    (inferInstance : AddCommGroup
      (CommonTailQuotient.relativeDenominator
        (R := secondVariablePID P n)
        (E := localizedSecondVariableBoundedAmbient P n k)
        (localizedSecondVariableGroundModule I k)
        (localizedSecondVariableOriginalModule I k))).toAddCommMonoid
  exact LinearMap.associated_det_comp_equiv
    (CommonTailQuotient.relativeDenominator
      (R := secondVariablePID P n)
      (E := localizedSecondVariableBoundedAmbient P n k)
      (localizedSecondVariableGroundModule I k)
      (localizedSecondVariableOriginalModule I k)).subtype
    u
    ((localizedSecondVariableEtaBasis I k).equiv
      (localizedSecondVariableDenominatorBasis I k)
      (Equiv.refl (localizedSecondVariableSmithIndex I k)))

/-- Primitive integral representatives for the selected cutoff-one Smith
coefficient and product, with the product representative additionally linked
to the selected-basis transition determinant after localization.

All conclusions of
`exists_primitive_integralSmithCoefficientProductRepresentatives_hasEquation33Witness`
are retained.  The added determinant association is obtained solely from the
exact selected-basis determinant/product equality above; it is not an
identification with historical `R^(2)`. -/
theorem
    exists_primitive_integralSmithTransitionDeterminantRepresentatives_hasEquation33Witness
    (I : Ideal (MvPolynomial (Fin (n + 2)) P))
    (C : MvPolynomial (Fin (n + 2)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 2)) k C)
    (hCI : C ∈ I)
    (i : localizedSecondVariableSmithIndex I k)
    (hgreat : localizedSecondVariableIsGreatestRemainingDivisor I k ∅ i) :
    ∃ e r : Polynomial (MvPolynomial (Fin n) P),
      e.IsPrimitive ∧
      r.IsPrimitive ∧
      e ≠ 0 ∧
      r ≠ 0 ∧
      secondVariableIntegralLift (P := P) (n := n) e ≠ 0 ∧
      secondVariableIntegralLift (P := P) (n := n) r ≠ 0 ∧
      Associated
        (localizedSecondVariableSmithCoefficients I k i)
        (Polynomial.map
          (algebraMap (MvPolynomial (Fin n) P)
            (FractionRing (MvPolynomial (Fin n) P))) e) ∧
      Associated
        (localizedSecondVariableSmithCoefficientProduct I k)
        (Polynomial.map
          (algebraMap (MvPolynomial (Fin n) P)
            (FractionRing (MvPolynomial (Fin n) P))) r) ∧
      Associated
        (localizedSecondVariableSelectedSmithTransitionDeterminant I k)
        (Polynomial.map
          (algebraMap (MvPolynomial (Fin n) P)
            (FractionRing (MvPolynomial (Fin n) P))) r) ∧
      e ∣ r ∧
      r ∣ e ^ localizedSecondVariableSmithRank I k ∧
      SatzVIIIOneStageDescent.HasEquation33Witness I 1
        (secondVariableIntegralLift (P := P) (n := n) e) ∧
      SatzVIIIOneStageDescent.HasEquation33Witness I 1
        (secondVariableIntegralLift (P := P) (n := n) r) := by
  obtain ⟨e, r, hePrimitive, hrPrimitive, he, hr, heLift, hrLift,
      hcoefficient, hproduct, her, hre, h33e, h33r⟩ :=
    exists_primitive_integralSmithCoefficientProductRepresentatives_hasEquation33Witness
      I C hC hCI i hgreat
  have hdeterminant :
      Associated
        (localizedSecondVariableSelectedSmithTransitionDeterminant I k)
        (Polynomial.map
          (algebraMap (MvPolynomial (Fin n) P)
            (FractionRing (MvPolynomial (Fin n) P))) r) := by
    rw [det_localizedSecondVariableSelectedSmithTransition_eq_product]
    exact hproduct
  exact ⟨e, r, hePrimitive, hrPrimitive, he, hr, heLift, hrLift,
    hcoefficient, hproduct, hdeterminant, her, hre, h33e, h33r⟩

#print axioms localizedSecondVariableSelectedSmithTransitionDeterminant
#print axioms localizedSecondVariableTransitionDeterminant
#print axioms det_localizedSecondVariableSelectedSmithTransition_eq_product
#print axioms localizedSecondVariable_transitionDet_associated_selectedSmithTransition
#print axioms exists_primitive_integralSmithTransitionDeterminantRepresentatives_hasEquation33Witness

end

end RegularIdealDecomposition

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
