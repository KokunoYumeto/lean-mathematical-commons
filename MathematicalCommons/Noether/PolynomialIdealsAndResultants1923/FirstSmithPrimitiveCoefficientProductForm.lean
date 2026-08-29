/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.FirstSmithCoefficientProductNumerator
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Hentzelt--Noether Satz VIII: primitive forms of the selected first Smith data

Module for P22, controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
lines 13323--13350.

The local zero-based cutoff `1` is the source's stage `i = 2`.  Starting from
the integral numerators already constructed for the selected greatest Smith
coefficient and the finite product of all selected Smith coefficients, this
module removes their contents.  The resulting representatives are primitive,
remain associated with the selected localized objects, satisfy both integral
divisibilities, and retain their equation-(33) witnesses.

These are still *selected-coefficient proxies*.  They are not yet identified
with the historical `E^(2)` or with the determinant/module-norm/minor-gcd form
`R^(2)`, and no canonicity or independence of the chosen Smith data is
asserted.  In particular, primitivity here must not be read as completing the
source's determinant or minor-gcd characterization.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open RegularitySpecialization

namespace SatzVIIIOneStageDescent

section ContentAbsorption

variable {P : Type*} [Field P]
variable {n : ℕ}

/-- Remove a permitted nonzero late-variable factor from the displayed form
in an equation-(33) witness by absorbing that factor into the multiplier. -/
theorem hasEquation33Witness_of_mul_left
    (I : Ideal (MvPolynomial (Fin n) P)) (cutoff : ℕ)
    {c e : MvPolynomial (Fin n) P}
    (hc : c ∈
      nonzeroLateVariableSubmonoid (S := P) (n := n) (cutoff + 1))
    (h : HasEquation33Witness I cutoff (c * e)) :
    HasEquation33Witness I cutoff e := by
  intro g hg
  obtain ⟨b, hb, hmem⟩ := h g hg
  refine ⟨b * c,
    (nonzeroLateVariableSubmonoid
      (S := P) (n := n) (cutoff + 1)).mul_mem hb hc, ?_⟩
  simpa [mul_assoc] using hmem

end ContentAbsorption

end SatzVIIIOneStageDescent

namespace LocalizationNumerator

section PrimitivePart

variable {A K : Type*} [CommRing A] [IsDomain A]
variable [NormalizedGCDMonoid A]
variable [Field K] [Algebra A K] [IsFractionRing A K]

/-- A nonzero polynomial and its primitive part become associated after
mapping the coefficient domain into its fraction field. -/
theorem fractionMap_associated_primPart
    {p : Polynomial A} (hp : p ≠ 0) :
    Associated
      (Polynomial.map (algebraMap A K) p)
      (Polynomial.map (algebraMap A K) p.primPart) := by
  have hcontent : p.content ≠ 0 := by
    simpa only [Ne, Polynomial.content_eq_zero_iff] using hp
  have hmapContent : algebraMap A K p.content ≠ 0 := by
    simpa using (IsFractionRing.injective A K).ne hcontent
  have hfactor :=
    congrArg (Polynomial.map (algebraMap A K))
      p.eq_C_content_mul_primPart
  have hmap :
      Polynomial.map (algebraMap A K) p =
        Polynomial.C (algebraMap A K p.content) *
          Polynomial.map (algebraMap A K) p.primPart := by
    simpa only [Polynomial.map_mul, Polynomial.map_C] using hfactor
  rw [hmap]
  exact associated_unit_mul_left _ _
    (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hmapContent))

end PrimitivePart

end LocalizationNumerator

namespace RegularIdealDecomposition

noncomputable section

variable {P : Type*} [Field P]
variable {n k : ℕ}

attribute [local instance] Polynomial.algebra

local instance lateCoefficientNormalizedGCDMonoid :
    NormalizedGCDMonoid (MvPolynomial (Fin n) P) :=
  Nonempty.some inferInstance

local instance lateVariablePolynomialIsLocalizationForPrimitiveCoefficientProductForm :
    IsLocalization (lateVariableDenominators (P := P) (n := n))
      (Polynomial (FractionRing (MvPolynomial (Fin n) P))) :=
  Polynomial.isLocalization
    (nonZeroDivisors (MvPolynomial (Fin n) P))
    (FractionRing (MvPolynomial (Fin n) P))

/-- Passing from a nonzero integral second-variable numerator to its primitive
part preserves its cutoff-one equation-(33) witness.  Its content is a
nonzero genuinely late-variable denominator, so the preceding absorption
lemma applies after the integral lift. -/
theorem hasEquation33Witness_secondVariableIntegralLift_primPart
    (I : Ideal (MvPolynomial (Fin (n + 2)) P))
    {a : Polynomial (MvPolynomial (Fin n) P)}
    (ha : a ≠ 0)
    (h : SatzVIIIOneStageDescent.HasEquation33Witness I 1
      (secondVariableIntegralLift (P := P) (n := n) a)) :
    SatzVIIIOneStageDescent.HasEquation33Witness I 1
      (secondVariableIntegralLift (P := P) (n := n) a.primPart) := by
  have hcontent : a.content ≠ 0 := by
    simpa only [Ne, Polynomial.content_eq_zero_iff] using ha
  let d : lateVariableDenominators (P := P) (n := n) :=
    ⟨Polynomial.C a.content,
      ⟨a.content,
        (mem_nonZeroDivisors_iff_ne_zero.mpr hcontent), rfl⟩⟩
  have hcontentLift :
      secondVariableIntegralLift (P := P) (n := n)
          (Polynomial.C a.content) ∈
        nonzeroLateVariableSubmonoid (S := P) (n := n + 2) 2 := by
    simpa [d] using
      (secondVariableIntegralLift_denominator_mem_nonzeroLateVariableSubmonoid
        d)
  rw [a.eq_C_content_mul_primPart, map_mul] at h
  exact SatzVIIIOneStageDescent.hasEquation33Witness_of_mul_left
    I 1 (by simpa using hcontentLift) h

/-- Primitive integral representatives for the selected cutoff-one Smith
coefficient and its selected-coefficient product.

Cutoff `1` is source stage `i = 2`.  Both representatives are nonzero and
remain associated with the corresponding localized selected objects.  The
coefficient representative divides the product representative; conversely,
the product representative divides the rank power of the coefficient
representative.  Both integral lifts retain equation (33).

This theorem concerns the selected proxies only: it does not identify them
with the historical `E^(2)` or `R^(2)`, a determinant, a module norm, or a gcd
of maximal minors, and it makes no choice-independence claim. -/
theorem
    exists_primitive_integralSmithCoefficientProductRepresentatives_hasEquation33Witness
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
      e ∣ r ∧
      r ∣ e ^ localizedSecondVariableSmithRank I k ∧
      SatzVIIIOneStageDescent.HasEquation33Witness I 1
        (secondVariableIntegralLift (P := P) (n := n) e) ∧
      SatzVIIIOneStageDescent.HasEquation33Witness I 1
        (secondVariableIntegralLift (P := P) (n := n) r) := by
  obtain ⟨a, r, ha, hr, _haLift, _hrLift, har,
      ⟨s, hs⟩, ⟨t, ht⟩, h33a, h33r, hproductDvdPower⟩ :=
    exists_nonzero_integralSmithCoefficientProductNumerator_hasEquation33Witness
      I C hC hCI i hgreat
  let B := MvPolynomial (Fin n) P
  let K := FractionRing B
  let L := Polynomial K
  have hsUnit :
      IsUnit
        (Polynomial.map (algebraMap B K)
          (s : Polynomial B)) := by
    simpa [B, K, L] using (IsLocalization.map_units L s)
  have htUnit :
      IsUnit
        (Polynomial.map (algebraMap B K)
          (t : Polynomial B)) := by
    simpa [B, K, L] using (IsLocalization.map_units L t)
  have hcoefficientAssociatedNumerator :
      Associated
        (localizedSecondVariableSmithCoefficients I k i)
        (Polynomial.map
          (algebraMap (MvPolynomial (Fin n) P)
            (FractionRing (MvPolynomial (Fin n) P))) a) := by
    rw [← hs]
    exact associated_mul_unit_right _ _ (by simpa [B, K] using hsUnit)
  have hproductAssociatedNumerator :
      Associated
        (localizedSecondVariableSmithCoefficientProduct I k)
        (Polynomial.map
          (algebraMap (MvPolynomial (Fin n) P)
            (FractionRing (MvPolynomial (Fin n) P))) r) := by
    rw [← ht]
    exact associated_mul_unit_right _ _ (by simpa [B, K] using htUnit)
  have hcoefficientAssociatedPrimitive :
      Associated
        (localizedSecondVariableSmithCoefficients I k i)
        (Polynomial.map
          (algebraMap (MvPolynomial (Fin n) P)
            (FractionRing (MvPolynomial (Fin n) P))) a.primPart) :=
    hcoefficientAssociatedNumerator.trans
      (LocalizationNumerator.fractionMap_associated_primPart
        (K := FractionRing (MvPolynomial (Fin n) P)) ha)
  have hproductAssociatedPrimitive :
      Associated
        (localizedSecondVariableSmithCoefficientProduct I k)
        (Polynomial.map
          (algebraMap (MvPolynomial (Fin n) P)
            (FractionRing (MvPolynomial (Fin n) P))) r.primPart) :=
    hproductAssociatedNumerator.trans
      (LocalizationNumerator.fractionMap_associated_primPart
        (K := FractionRing (MvPolynomial (Fin n) P)) hr)
  have hprimitiveCoefficientDvdPrimitiveProduct :
      a.primPart ∣ r.primPart :=
    (a.isPrimitive_primPart.dvd_primPart_iff_dvd hr).mpr
      (a.primPart_dvd.trans har)
  have hmapPrimitiveProductDvdPower :
      Polynomial.map
          (algebraMap (MvPolynomial (Fin n) P)
            (FractionRing (MvPolynomial (Fin n) P))) r.primPart ∣
        (Polynomial.map
          (algebraMap (MvPolynomial (Fin n) P)
            (FractionRing (MvPolynomial (Fin n) P))) a.primPart) ^
          localizedSecondVariableSmithRank I k :=
    hcoefficientAssociatedPrimitive.pow_pow.dvd_iff_dvd_right.mp
      (hproductAssociatedPrimitive.dvd_iff_dvd_left.mp hproductDvdPower)
  have hprimitivePower :
      (a.primPart ^ localizedSecondVariableSmithRank I k).IsPrimitive := by
    induction localizedSecondVariableSmithRank I k with
    | zero => simpa only [pow_zero] using
        (Polynomial.isPrimitive_one :
          (1 : Polynomial (MvPolynomial (Fin n) P)).IsPrimitive)
    | succ m ih =>
        rw [pow_succ]
        exact ih.mul a.isPrimitive_primPart
  have hprimitiveProductDvdPower :
      r.primPart ∣
        a.primPart ^ localizedSecondVariableSmithRank I k := by
    apply r.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map
      (K := FractionRing (MvPolynomial (Fin n) P)) hprimitivePower
    simpa using hmapPrimitiveProductDvdPower
  exact ⟨a.primPart, r.primPart,
    a.isPrimitive_primPart, r.isPrimitive_primPart,
    a.primPart_ne_zero, r.primPart_ne_zero,
    secondVariableIntegralLift_ne_zero a.primPart_ne_zero,
    secondVariableIntegralLift_ne_zero r.primPart_ne_zero,
    hcoefficientAssociatedPrimitive, hproductAssociatedPrimitive,
    hprimitiveCoefficientDvdPrimitiveProduct, hprimitiveProductDvdPower,
    hasEquation33Witness_secondVariableIntegralLift_primPart I ha h33a,
    hasEquation33Witness_secondVariableIntegralLift_primPart I hr h33r⟩

#print axioms SatzVIIIOneStageDescent.hasEquation33Witness_of_mul_left
#print axioms LocalizationNumerator.fractionMap_associated_primPart
#print axioms hasEquation33Witness_secondVariableIntegralLift_primPart
#print axioms exists_primitive_integralSmithCoefficientProductRepresentatives_hasEquation33Witness

end

end RegularIdealDecomposition

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
