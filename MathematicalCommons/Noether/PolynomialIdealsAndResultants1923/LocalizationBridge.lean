/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Localization bridge for Hentzelt--Noether Satz VI

Controlled source: Kurt Hentzelt, freely edited and conceptually recast by
Emmy Noether, *Zur Theorie der Polynomideale und Resultanten*, witness
`NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
especially lines 13015 and 13088--13102 around equations (13), (19), and (20).

This module records the exact extension--contraction facts
needed when the auxiliary parameters are passed from a coefficient ring to a
localization.  The central point is explicit: membership after localization
means membership after multiplication by one denominator.  Descent without a
denominator therefore requires a saturation hypothesis (or, for example, a
primary ideal disjoint from the denominator submonoid).
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

section GeneralLocalization

variable {R S : Type*} [CommRing R] [CommRing S]
variable [Algebra R S] (M : Submonoid R) [IsLocalization M S]

/-- A ground-ring element belongs to an extended ideal after localization
exactly when one denominator multiple belongs to the original ideal. -/
theorem algebraMap_mem_localizedIdeal_iff_exists_denominator
    (I : Ideal R) (x : R) :
    algebraMap R S x ∈ Ideal.map (algebraMap R S) I ↔
      ∃ m : M, (m : R) * x ∈ I := by
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff M]
  constructor
  · rintro ⟨m, hm, hx⟩
    exact ⟨⟨m, hm⟩, hx⟩
  · rintro ⟨m, hx⟩
    exact ⟨m, m.property, hx⟩

/-- Exact extension--contraction under the honest saturation condition for
the chosen denominator submonoid. -/
theorem under_map_eq_of_denominator_saturated
    (I : Ideal R)
    (hsat : ∀ (m : M) (x : R), (m : R) * x ∈ I → x ∈ I) :
    (Ideal.map (algebraMap R S) I).under R = I := by
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_comap,
      algebraMap_mem_localizedIdeal_iff_exists_denominator M I x] at hx
    obtain ⟨m, hm⟩ := hx
    exact hsat m x hm
  · exact Ideal.le_comap_map

/-- Regularity of every denominator in the quotient ring is a semantic
sufficient condition for denominator saturation. -/
theorem denominator_saturated_of_isRegular_quotient
    (I : Ideal R)
    (hregular : ∀ m : M,
      IsRegular (Ideal.Quotient.mk I (m : R))) :
    ∀ (m : M) (x : R), (m : R) * x ∈ I → x ∈ I := by
  intro m x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hx ⊢
  rw [map_mul] at hx
  exact (hregular m).left (by simpa using hx)

/-- Elementwise descent from a localized ideal under denominator
saturation. -/
theorem mem_of_algebraMap_mem_localizedIdeal_of_denominator_saturated
    (I : Ideal R)
    (hsat : ∀ (m : M) (x : R), (m : R) * x ∈ I → x ∈ I)
    {x : R} (hx : algebraMap R S x ∈ Ideal.map (algebraMap R S) I) :
    x ∈ I := by
  rw [algebraMap_mem_localizedIdeal_iff_exists_denominator M I x] at hx
  obtain ⟨m, hm⟩ := hx
  exact hsat m x hm

/-- Primary ideals disjoint from the denominator submonoid satisfy exact
extension--contraction.  This is the standard sufficient hypothesis supplied
by Mathlib's localization API. -/
theorem under_map_eq_of_isPrimary_disjoint
    (I : Ideal R) (hI : I.IsPrimary)
    (hdisj : Disjoint (M : Set R) (I : Set R)) :
    (Ideal.map (algebraMap R S) I).under R = I :=
  IsLocalization.under_map_of_isPrimary_disjoint M S hI hdisj

end GeneralLocalization

section MvPolynomialLocalization

variable {R S σ : Type*} [CommRing R] [CommRing S]
variable [Algebra R S] (M : Submonoid R) [IsLocalization M S]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Local copy of Mathlib's `MvPolynomial.isLocalization` construction.  The
selective dependency cache used by this project contains all of its inputs but
not the object file for the wrapper module where the upstream instance lives. -/
local instance mvPolynomialIsLocalization :
    IsLocalization (M.map
      (MvPolynomial.C : R →+* MvPolynomial σ R).toMonoidHom)
      (MvPolynomial σ S) :=
  isLocalizedModule_iff_isLocalization.mp <|
    (isLocalizedModule_iff_isBaseChange M S _).mpr <|
      .of_equiv (MvPolynomial.algebraTensorAlgEquiv _ _).toLinearEquiv fun _ ↦ by simp

/-- Polynomial form of denominator clearing.  Mapping coefficients to a
localization puts a ground polynomial in the extended ideal exactly when a
single coefficient-ring denominator, embedded as a constant polynomial,
puts the original polynomial in the ground ideal. -/
theorem mvPolynomial_map_mem_localizedIdeal_iff_exists_denominator
    (I : Ideal (MvPolynomial σ R)) (p : MvPolynomial σ R) :
    MvPolynomial.map (algebraMap R S) p ∈
        Ideal.map (MvPolynomial.map (algebraMap R S)) I ↔
      ∃ m : M, MvPolynomial.C (m : R) * p ∈ I := by
  change algebraMap (MvPolynomial σ R) (MvPolynomial σ S) p ∈
      Ideal.map (algebraMap (MvPolynomial σ R) (MvPolynomial σ S)) I ↔ _
  rw [algebraMap_mem_localizedIdeal_iff_exists_denominator
    (M.map (MvPolynomial.C : R →+* MvPolynomial σ R).toMonoidHom) I p]
  constructor
  · rintro ⟨⟨c, hc⟩, hm⟩
    obtain ⟨r, hrM, rfl⟩ := hc
    exact ⟨⟨r, hrM⟩, hm⟩
  · rintro ⟨m, hm⟩
    refine ⟨⟨MvPolynomial.C (m : R), ?_⟩, hm⟩
    exact Submonoid.mem_map_of_mem
      (MvPolynomial.C : R →+* MvPolynomial σ R).toMonoidHom
      m.property

/-- Exact polynomial extension--contraction under saturation by constant
polynomials coming from the coefficient denominators. -/
theorem mvPolynomial_under_map_eq_of_coefficient_denominator_saturated
    (I : Ideal (MvPolynomial σ R))
    (hsat : ∀ (m : M) (p : MvPolynomial σ R),
      MvPolynomial.C (m : R) * p ∈ I → p ∈ I) :
    (Ideal.map (MvPolynomial.map (algebraMap R S)) I).under
        (MvPolynomial σ R) = I := by
  change (Ideal.map
      (algebraMap (MvPolynomial σ R) (MvPolynomial σ S)) I).under
        (MvPolynomial σ R) = I
  apply under_map_eq_of_denominator_saturated
    (M.map (MvPolynomial.C : R →+* MvPolynomial σ R).toMonoidHom) I
  rintro ⟨c, hc⟩ p hp
  obtain ⟨r, hrM, rfl⟩ := hc
  exact hsat ⟨r, hrM⟩ p hp

/-- A direct polynomial specialization of primary extension--contraction:
primary ground ideals disjoint from all constant denominators contract
exactly after coefficient localization. -/
theorem mvPolynomial_under_map_eq_of_isPrimary_disjoint
    (I : Ideal (MvPolynomial σ R)) (hI : I.IsPrimary)
    (hdisj : Disjoint
      ((M.map (MvPolynomial.C : R →+* MvPolynomial σ R).toMonoidHom) :
        Set (MvPolynomial σ R))
      (I : Set (MvPolynomial σ R))) :
    (Ideal.map (MvPolynomial.map (algebraMap R S)) I).under
        (MvPolynomial σ R) = I := by
  change (Ideal.map
      (algebraMap (MvPolynomial σ R) (MvPolynomial σ S)) I).under
        (MvPolynomial σ R) = I
  exact IsLocalization.under_map_of_isPrimary_disjoint
    (M.map (MvPolynomial.C : R →+* MvPolynomial σ R).toMonoidHom)
    (MvPolynomial σ S) hI hdisj

/-- Ground-polynomial membership descends from the localized extension once
constant-denominator saturation is available. -/
theorem mvPolynomial_mem_of_map_mem_localizedIdeal
    (I : Ideal (MvPolynomial σ R))
    (hsat : ∀ (m : M) (p : MvPolynomial σ R),
      MvPolynomial.C (m : R) * p ∈ I → p ∈ I)
    {p : MvPolynomial σ R}
    (hp : MvPolynomial.map (algebraMap R S) p ∈
      Ideal.map (MvPolynomial.map (algebraMap R S)) I) :
    p ∈ I := by
  rw [mvPolynomial_map_mem_localizedIdeal_iff_exists_denominator M I p] at hp
  obtain ⟨m, hm⟩ := hp
  exact hsat m p hm

end MvPolynomialLocalization

section TwoVariableSets

variable {P U Y : Type*} [Field P]

attribute [local instance] MvPolynomial.algebraMvPolynomial

local instance parameterFractionMvPolynomialIsLocalization :
    IsLocalization
      ((nonZeroDivisors (MvPolynomial U P)).map
        (MvPolynomial.C :
          MvPolynomial U P →+* MvPolynomial Y (MvPolynomial U P)).toMonoidHom)
      (MvPolynomial Y (FractionRing (MvPolynomial U P))) :=
  isLocalizedModule_iff_isLocalization.mp <|
    (isLocalizedModule_iff_isBaseChange
      (nonZeroDivisors (MvPolynomial U P))
      (FractionRing (MvPolynomial U P)) _).mpr <|
      .of_equiv
        (MvPolynomial.algebraTensorAlgEquiv _ _).toLinearEquiv fun _ ↦ by simp

/-- Exchange the two nested sets of polynomial variables.  We choose the
orientation whose simplification rule sends a ground polynomial in the `Y`
variables, extended coefficientwise to `P[U][Y]`, to the same polynomial as a
constant in the `U` variables. -/
noncomputable def nestedVariableSwapEquiv :
    MvPolynomial Y (MvPolynomial U P) ≃ₐ[P]
      MvPolynomial U (MvPolynomial Y P) :=
  (MvPolynomial.commAlgEquiv P U Y).symm

/-- Under the variable swap, coefficientwise extension of a polynomial in
the `Y` variables becomes a constant polynomial in the parameter variables. -/
@[simp]
theorem nestedVariableSwapEquiv_map_C (p : MvPolynomial Y P) :
    nestedVariableSwapEquiv (P := P) (U := U) (Y := Y)
        (MvPolynomial.map
          (MvPolynomial.C : P →+* MvPolynomial U P) p) =
      MvPolynomial.C p := by
  change (MvPolynomial.commAlgEquiv P U Y).symm
      (MvPolynomial.map (MvPolynomial.C : P →+* MvPolynomial U P) p) =
    MvPolynomial.C p
  rw [← MvPolynomial.commAlgEquiv_C]
  exact (MvPolynomial.commAlgEquiv P U Y).symm_apply_apply _

/-- The direct coefficient map from the ground field into the rational
function field in the auxiliary parameters. -/
noncomputable def groundToParameterFraction :
    P →+* FractionRing (MvPolynomial U P) :=
  (algebraMap (MvPolynomial U P)
      (FractionRing (MvPolynomial U P))).comp
    (MvPolynomial.C : P →+* MvPolynomial U P)

/-- Extending a ground ideal first to the parameter-polynomial ring and then
to its fraction field agrees with extending it directly along the composite
coefficient map. -/
theorem map_groundIdeal_through_parameterRing
    (I : Ideal (MvPolynomial Y P)) :
    Ideal.map
        (MvPolynomial.map
          (algebraMap (MvPolynomial U P)
            (FractionRing (MvPolynomial U P))))
        (Ideal.map
          (MvPolynomial.map
            (MvPolynomial.C : P →+* MvPolynomial U P)) I) =
      Ideal.map
        (MvPolynomial.map
          (groundToParameterFraction (P := P) (U := U))) I := by
  rw [Ideal.map_map]
  congr 1
  ext <;> simp [groundToParameterFraction]

/-- Denominator clearing for the two variable sets in Hentzelt--Noether.

If a polynomial over `P[U]` enters the extension of a ground ideal after
passing to the rational function field `Frac(P[U])`, then one nonzero
parameter polynomial clears all denominators and puts the representative in
the polynomial extension of the original ideal. -/
theorem exists_nonzero_parameter_denominator_of_mem_fractionExtension
    (I : Ideal (MvPolynomial Y P))
    (q : MvPolynomial Y (MvPolynomial U P))
    (hq : MvPolynomial.map
        (algebraMap (MvPolynomial U P)
          (FractionRing (MvPolynomial U P))) q ∈
      Ideal.map
        (MvPolynomial.map
          (groundToParameterFraction (P := P) (U := U))) I) :
    ∃ s : MvPolynomial U P, s ≠ 0 ∧
      MvPolynomial.C s * q ∈
        Ideal.map
          (MvPolynomial.map
            (MvPolynomial.C : P →+* MvPolynomial U P)) I := by
  let A := MvPolynomial U P
  let K := FractionRing A
  let IA : Ideal (MvPolynomial Y A) :=
    Ideal.map
      (MvPolynomial.map (MvPolynomial.C : P →+* A)) I
  have hfactor :
      MvPolynomial.map (algebraMap A K) q ∈
        Ideal.map (MvPolynomial.map (algebraMap A K)) IA := by
    change MvPolynomial.map
        (algebraMap (MvPolynomial U P)
          (FractionRing (MvPolynomial U P))) q ∈
      Ideal.map
        (MvPolynomial.map
          (algebraMap (MvPolynomial U P)
            (FractionRing (MvPolynomial U P))))
        (Ideal.map
          (MvPolynomial.map
            (MvPolynomial.C : P →+* MvPolynomial U P)) I)
    rwa [map_groundIdeal_through_parameterRing]
  obtain ⟨m, hm⟩ :=
    (mvPolynomial_map_mem_localizedIdeal_iff_exists_denominator
      (R := A) (S := K) ( σ := Y) (nonZeroDivisors A) IA q).mp hfactor
  exact ⟨(m : A), nonZeroDivisors.coe_ne_zero m, hm⟩

/-- Arbitrary-element form of simultaneous denominator clearing.  Every
member of the fraction-field extension has one nonzero parameter denominator
and a numerator already in the extension over `P[U]`. -/
theorem exists_nonzero_parameter_denominator_and_numerator
    (I : Ideal (MvPolynomial Y P))
    {z : MvPolynomial Y (FractionRing (MvPolynomial U P))}
    (hz : z ∈ Ideal.map
      (MvPolynomial.map
        (groundToParameterFraction (P := P) (U := U))) I) :
    ∃ s : MvPolynomial U P, s ≠ 0 ∧
      ∃ q : MvPolynomial Y (MvPolynomial U P),
        q ∈ Ideal.map
          (MvPolynomial.map
            (MvPolynomial.C : P →+* MvPolynomial U P)) I ∧
        MvPolynomial.C
            (algebraMap (MvPolynomial U P)
              (FractionRing (MvPolynomial U P)) s) * z =
          MvPolynomial.map
            (algebraMap (MvPolynomial U P)
              (FractionRing (MvPolynomial U P))) q := by
  let A := MvPolynomial U P
  let K := FractionRing A
  let IA : Ideal (MvPolynomial Y A) :=
    Ideal.map
      (MvPolynomial.map (MvPolynomial.C : P →+* A)) I
  have hz' : z ∈
      Ideal.map (MvPolynomial.map (algebraMap A K)) IA := by
    change z ∈
      Ideal.map
        (MvPolynomial.map
          (algebraMap (MvPolynomial U P)
            (FractionRing (MvPolynomial U P))))
        (Ideal.map
          (MvPolynomial.map
            (MvPolynomial.C : P →+* MvPolynomial U P)) I)
    rwa [map_groundIdeal_through_parameterRing]
  change z ∈
    Ideal.map
      (algebraMap (MvPolynomial Y A) (MvPolynomial Y K)) IA at hz'
  rw [IsLocalization.mem_map_algebraMap_iff
    ((nonZeroDivisors A).map
      (MvPolynomial.C : A →+* MvPolynomial Y A).toMonoidHom)] at hz'
  obtain ⟨⟨⟨q, hq⟩, ⟨c, hc⟩⟩, heq⟩ := hz'
  obtain ⟨s, hs, rfl⟩ := hc
  refine ⟨s, nonZeroDivisors.ne_zero hs, q, hq, ?_⟩
  change MvPolynomial.C (algebraMap A K s) * z =
    MvPolynomial.map (algebraMap A K) q
  have heq' : z * MvPolynomial.C (algebraMap A K s) =
      MvPolynomial.map (algebraMap A K) q := by
    simpa using heq
  simpa [mul_comm] using heq'

end TwoVariableSets

#print axioms algebraMap_mem_localizedIdeal_iff_exists_denominator
#print axioms under_map_eq_of_denominator_saturated
#print axioms denominator_saturated_of_isRegular_quotient
#print axioms mem_of_algebraMap_mem_localizedIdeal_of_denominator_saturated
#print axioms under_map_eq_of_isPrimary_disjoint
#print axioms mvPolynomial_map_mem_localizedIdeal_iff_exists_denominator
#print axioms mvPolynomial_under_map_eq_of_coefficient_denominator_saturated
#print axioms mvPolynomial_under_map_eq_of_isPrimary_disjoint
#print axioms mvPolynomial_mem_of_map_mem_localizedIdeal
#print axioms nestedVariableSwapEquiv
#print axioms nestedVariableSwapEquiv_map_C
#print axioms groundToParameterFraction
#print axioms map_groundIdeal_through_parameterRing
#print axioms exists_nonzero_parameter_denominator_of_mem_fractionExtension
#print axioms exists_nonzero_parameter_denominator_and_numerator

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
