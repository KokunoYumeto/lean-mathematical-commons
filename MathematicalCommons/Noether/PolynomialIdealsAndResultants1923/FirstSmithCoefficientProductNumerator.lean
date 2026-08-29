/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.FirstSmithEquation33Bridge

/-!
# Hentzelt--Noether Satz VIII: an integral numerator for the first Smith-coefficient product

Module for P22, controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
lines 13323--13380.

The local zero-based cutoff `1` is the source's stage `i = 2`: its
equation-(33) multiplier is free of the first two original variables.  The
preceding bridge constructs a nonzero integral numerator for an explicitly
selected greatest localized Smith coefficient at this cutoff.  Here the
localized divisibility of that coefficient into the finite product of all
selected Smith coefficients is cleared integrally.  The resulting numerator
is a multiple of the first numerator and therefore inherits its
equation-(33) witness.

This is deliberately called the *integral selected-Smith-coefficient-product
numerator*.  It is not identified with Hentzelt's primitive historical
`R^(2)`, a resultant, a normalized or canonical form, or an object independent
of the chosen Smith data.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open RegularitySpecialization

namespace SatzVIIIOneStageDescent

section WitnessMultiplication

variable {P : Type*} [Field P]
variable {n : ℕ}

/-- An equation-(33) witness remains valid after multiplying its displayed
integral form on the right by any polynomial.  Indeed, multiply the tested
ground-ideal element by that polynomial before applying the old witness. -/
theorem hasEquation33Witness_mul_right
    (I : Ideal (MvPolynomial (Fin n) P)) (cutoff : ℕ)
    {e : MvPolynomial (Fin n) P}
    (h : HasEquation33Witness I cutoff e)
    (c : MvPolynomial (Fin n) P) :
    HasEquation33Witness I cutoff (e * c) := by
  intro g hg
  obtain ⟨b, hb, hmem⟩ := h (c * g)
    ((stageGroundIdeal (S := P) cutoff I).mul_mem_left c hg)
  exact ⟨b, hb, by simpa [mul_assoc] using hmem⟩

end WitnessMultiplication

end SatzVIIIOneStageDescent

namespace LocalizationNumerator

section Divisibility

variable {A L : Type*} [CommRing A] [CommRing L] [Algebra A L]

/-- Clear a localized quotient along `x ∣ y` and multiply an existing
integral numerator for `x` by the newly obtained numerator.  The returned
denominator is the product of the old and new localization denominators. -/
theorem exists_integralNumerator_multiple_of_dvd
    (D : Submonoid A) [IsLocalization D L]
    {x y : L} {a : A} (hxy : x ∣ y)
    (ha : ∃ s : D,
      x * algebraMap A L (s : A) = algebraMap A L a) :
    ∃ r : A, a ∣ r ∧
      ∃ t : D,
        y * algebraMap A L (t : A) = algebraMap A L r := by
  obtain ⟨q, hq⟩ := hxy
  obtain ⟨s, hs⟩ := ha
  obtain ⟨⟨c, t⟩, ht⟩ := IsLocalization.surj D q
  refine ⟨a * c, ⟨c, rfl⟩, s * t, ?_⟩
  rw [hq]
  calc
    (x * q) * algebraMap A L (((s * t : D) : A)) =
        (x * algebraMap A L (s : A)) *
          (q * algebraMap A L (t : A)) := by
      change (x * q) * algebraMap A L ((s : A) * (t : A)) = _
      rw [map_mul]
      ring
    _ = algebraMap A L a * algebraMap A L c := by rw [hs, ht]
    _ = algebraMap A L (a * c) :=
      (map_mul (algebraMap A L) a c).symm

end Divisibility

end LocalizationNumerator

namespace RegularIdealDecomposition

noncomputable section

variable {P : Type*} [Field P]
variable {n k : ℕ}

attribute [local instance] Polynomial.algebra

local instance lateVariablePolynomialIsLocalizationForCoefficientProductNumerator :
    IsLocalization (lateVariableDenominators (P := P) (n := n))
      (Polynomial (FractionRing (MvPolynomial (Fin n) P))) :=
  Polynomial.isLocalization
    (nonZeroDivisors (MvPolynomial (Fin n) P))
    (FractionRing (MvPolynomial (Fin n) P))

/-- The finite product of the selected localized Smith coefficients is
nonzero because every selected coefficient is nonzero. -/
theorem localizedSecondVariableSmithCoefficientProduct_ne_zero
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    localizedSecondVariableSmithCoefficientProduct I k ≠ 0 := by
  classical
  rw [localizedSecondVariableSmithCoefficientProduct,
    SmithAnnihilatorBounds.coefficientProduct]
  exact Finset.prod_ne_zero_iff.mpr fun j _hj ↦
    localizedSecondVariableSmithCoefficients_ne_zero I k j

/-- Under a regular member and an explicitly selected greatest cutoff-one
Smith coefficient, both that coefficient and the finite selected-coefficient
product possess compatible nonzero integral numerators.

Here cutoff `1` is source stage `i = 2`.  The product numerator is divisible
by the coefficient numerator, both lifted numerators satisfy equation (33),
and the localized product-divides-power conclusion is retained.  No primitive,
resultant, normalization, canonicity, or choice-independence claim is made. -/
theorem
    exists_nonzero_integralSmithCoefficientProductNumerator_hasEquation33Witness
    (I : Ideal (MvPolynomial (Fin (n + 2)) P))
    (C : MvPolynomial (Fin (n + 2)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 2)) k C)
    (hCI : C ∈ I)
    (i : localizedSecondVariableSmithIndex I k)
    (hgreat : localizedSecondVariableIsGreatestRemainingDivisor I k ∅ i) :
    ∃ a r : Polynomial (MvPolynomial (Fin n) P),
      a ≠ 0 ∧
      r ≠ 0 ∧
      secondVariableIntegralLift (P := P) (n := n) a ≠ 0 ∧
      secondVariableIntegralLift (P := P) (n := n) r ≠ 0 ∧
      a ∣ r ∧
      (∃ s : lateVariableDenominators (P := P) (n := n),
        localizedSecondVariableSmithCoefficients I k i *
            Polynomial.map
              (algebraMap (MvPolynomial (Fin n) P)
                (FractionRing (MvPolynomial (Fin n) P)))
              (s : Polynomial (MvPolynomial (Fin n) P)) =
          Polynomial.map
            (algebraMap (MvPolynomial (Fin n) P)
              (FractionRing (MvPolynomial (Fin n) P))) a) ∧
      (∃ t : lateVariableDenominators (P := P) (n := n),
        localizedSecondVariableSmithCoefficientProduct I k *
            Polynomial.map
              (algebraMap (MvPolynomial (Fin n) P)
                (FractionRing (MvPolynomial (Fin n) P)))
              (t : Polynomial (MvPolynomial (Fin n) P)) =
          Polynomial.map
            (algebraMap (MvPolynomial (Fin n) P)
              (FractionRing (MvPolynomial (Fin n) P))) r) ∧
      SatzVIIIOneStageDescent.HasEquation33Witness I 1
        (secondVariableIntegralLift (P := P) (n := n) a) ∧
      SatzVIIIOneStageDescent.HasEquation33Witness I 1
        (secondVariableIntegralLift (P := P) (n := n) r) ∧
      localizedSecondVariableSmithCoefficientProduct I k ∣
        localizedSecondVariableSmithCoefficients I k i ^
          localizedSecondVariableSmithRank I k := by
  obtain ⟨a, ha, haLift, ⟨s, hs⟩, h33a⟩ :=
    exists_nonzero_integralSmithNumerator_hasEquation33Witness
      I C hC hCI i hgreat
  let A := Polynomial (MvPolynomial (Fin n) P)
  let L := secondVariablePID P n
  let D := lateVariableDenominators (P := P) (n := n)
  have hdiv :=
    localizedSecondVariableSmith_greatest_product_divisibilities
      I k i hgreat
  have hs' :
      localizedSecondVariableSmithCoefficients I k i *
          algebraMap A L (s : A) = algebraMap A L a := by
    simpa [A, L] using hs
  obtain ⟨r, har, t, hrt⟩ :=
    LocalizationNumerator.exists_integralNumerator_multiple_of_dvd
      (A := A) (L := L) D hdiv.1 ⟨s, hs'⟩
  have hrt' :
      localizedSecondVariableSmithCoefficientProduct I k *
          Polynomial.map
            (algebraMap (MvPolynomial (Fin n) P)
              (FractionRing (MvPolynomial (Fin n) P)))
            (t : Polynomial (MvPolynomial (Fin n) P)) =
        Polynomial.map
          (algebraMap (MvPolynomial (Fin n) P)
            (FractionRing (MvPolynomial (Fin n) P))) r := by
    simpa [A, L] using hrt
  have hproduct0 :
      localizedSecondVariableSmithCoefficientProduct I k ≠ 0 :=
    localizedSecondVariableSmithCoefficientProduct_ne_zero I k
  have ht0 : algebraMap A L (t : A) ≠ 0 :=
    (IsLocalization.map_units L t).ne_zero
  have hr : r ≠ 0 := by
    intro hr0
    have hleft :
        localizedSecondVariableSmithCoefficientProduct I k *
          algebraMap A L (t : A) ≠ 0 :=
      mul_ne_zero hproduct0 ht0
    apply hleft
    exact hrt.trans (by simp [hr0])
  have h33r :
      SatzVIIIOneStageDescent.HasEquation33Witness I 1
        (secondVariableIntegralLift (P := P) (n := n) r) := by
    rcases har with ⟨c, hac⟩
    rw [hac, map_mul]
    exact SatzVIIIOneStageDescent.hasEquation33Witness_mul_right
      I 1 h33a (secondVariableIntegralLift (P := P) (n := n) c)
  exact ⟨a, r, ha, hr, haLift,
    secondVariableIntegralLift_ne_zero hr, har,
    ⟨s, hs⟩, ⟨t, hrt'⟩, h33a, h33r, hdiv.2⟩

#print axioms SatzVIIIOneStageDescent.hasEquation33Witness_mul_right
#print axioms LocalizationNumerator.exists_integralNumerator_multiple_of_dvd
#print axioms localizedSecondVariableSmithCoefficientProduct_ne_zero
#print axioms exists_nonzero_integralSmithCoefficientProductNumerator_hasEquation33Witness

end


end RegularIdealDecomposition

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
