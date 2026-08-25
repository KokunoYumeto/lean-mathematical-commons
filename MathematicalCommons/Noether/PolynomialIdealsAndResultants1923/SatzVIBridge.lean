/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Localization.Ideal

/-!
# Hentzelt--Noether Satz VI: parameter coefficients and ground ideals

Controlled source: Kurt Hentzelt, freely edited and conceptually recast by
Emmy Noether, *Zur Theorie der Polynomideale und Resultanten*, witness
`NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
Satz VI and equations (18)--(20) at lines 13080--13107.

This module turns the literal coefficient-module equation (17) into the
parameter-coefficient ground-ideal membership used in equations (19)--(20).
It works over the rational function field in the auxiliary parameters, keeps
the stage denominator submonoid explicit, and imposes no prime, primary,
saturation, or finiteness hypothesis on the original ideal.  Identification
of the entire historical stage ground ideal in both directions remains a
separate theorem.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open Ideal

section ParameterTransforms

variable {P U X : Type*} [Field P]

/-- Reinterpret a polynomial in parameters with polynomial coefficients as a
polynomial in the geometric variables over the rational function field in
those parameters. -/
noncomputable def parameterToCoefficient :
    MvPolynomial U (MvPolynomial X P) →+*
      MvPolynomial X (FractionRing (MvPolynomial U P)) :=
  (MvPolynomial.map
      (algebraMap (MvPolynomial U P)
        (FractionRing (MvPolynomial U P)))).comp
    (MvPolynomial.commAlgEquiv P U X).toRingEquiv.toRingHom

@[simp]
theorem parameterToCoefficient_C (f : MvPolynomial X P) :
    parameterToCoefficient (P := P) (U := U) (X := X)
        (MvPolynomial.C f) =
      MvPolynomial.map
        (algebraMap P (FractionRing (MvPolynomial U P))) f := by
  rw [parameterToCoefficient, RingHom.comp_apply]
  change
    MvPolynomial.map
        (algebraMap (MvPolynomial U P)
          (FractionRing (MvPolynomial U P)))
        (MvPolynomial.commAlgEquiv P U X (MvPolynomial.C f)) = _
  rw [MvPolynomial.commAlgEquiv_C, MvPolynomial.map_map]
  congr 1

/-- The base-polynomial map obtained after the generic coordinate change. -/
noncomputable def genericTransformHom
    (tau : MvPolynomial X (FractionRing (MvPolynomial U P))
      ≃ₐ[FractionRing (MvPolynomial U P)]
      MvPolynomial X (FractionRing (MvPolynomial U P))) :
    MvPolynomial X P →+*
      MvPolynomial X (FractionRing (MvPolynomial U P)) :=
  tau.toRingEquiv.toRingHom.comp
    (MvPolynomial.map
      (algebraMap P (FractionRing (MvPolynomial U P))))

/-- The same transform on parameter polynomials with base-polynomial
coefficients. -/
noncomputable def parameterTransformHom
    (tau : MvPolynomial X (FractionRing (MvPolynomial U P))
      ≃ₐ[FractionRing (MvPolynomial U P)]
      MvPolynomial X (FractionRing (MvPolynomial U P))) :
    MvPolynomial U (MvPolynomial X P) →+*
      MvPolynomial X (FractionRing (MvPolynomial U P)) :=
  tau.toRingEquiv.toRingHom.comp
    (parameterToCoefficient (P := P) (U := U) (X := X))

/-- The extension of a base ideal followed by the generic coordinate
equivalence. -/
noncomputable def genericTransformIdeal
    (tau : MvPolynomial X (FractionRing (MvPolynomial U P))
      ≃ₐ[FractionRing (MvPolynomial U P)]
      MvPolynomial X (FractionRing (MvPolynomial U P)))
    (I : Ideal (MvPolynomial X P)) :
    Ideal (MvPolynomial X (FractionRing (MvPolynomial U P))) :=
  Ideal.map (genericTransformHom (P := P) (U := U) tau) I

@[simp]
theorem parameterTransformHom_C
    (tau : MvPolynomial X (FractionRing (MvPolynomial U P))
      ≃ₐ[FractionRing (MvPolynomial U P)]
      MvPolynomial X (FractionRing (MvPolynomial U P)))
    (f : MvPolynomial X P) :
    parameterTransformHom (P := P) (U := U) tau (MvPolynomial.C f) =
      genericTransformHom (P := P) (U := U) tau f := by
  simp [parameterTransformHom, genericTransformHom]

end ParameterTransforms

section CoefficientExtraction

variable {S U : Type*} [CommRing S]

/-- Every coefficient belongs to the integer-linear coefficient module. -/
theorem coeff_mem_mvCoefficientModule_int
    (p : MvPolynomial U S) (d : U →₀ ℕ) :
    p.coeff d ∈ mvCoefficientModule (A := ℤ) p := by
  by_cases hcoeff : p.coeff d = 0
  · rw [hcoeff]
    exact Submodule.zero_mem _
  · exact Submodule.subset_span (MvPolynomial.coeff_mem_coeffs d hcoeff)

/-- If a polynomial in parameters belongs to the coefficient extension of
an ideal, its integer-linear coefficient module is contained in that ideal. -/
theorem mvCoefficientModule_le_restrictScalars_of_mem_map_C
    (I : Ideal S) (p : MvPolynomial U S)
    (hp : p ∈ Ideal.map (MvPolynomial.C : S →+* MvPolynomial U S) I) :
    mvCoefficientModule (A := ℤ) p ≤ I.restrictScalars ℤ := by
  rw [mvCoefficientModule, Submodule.span_le]
  intro c hc
  obtain ⟨d, _hd, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
  exact (Submodule.restrictScalars_mem ℤ I _).2
    ((MvPolynomial.mem_map_C_iff.mp hp) d)

/-- Equations (17)--(20), before coordinate transport: a coefficient of the
second factor is killed into the extended ideal by a positive power of the
first factor whenever their product already lies in that extension. -/
theorem exists_pow_mul_C_mem_coefficientExtension_of_mul_mem
    {n : ℕ} (I : Ideal S) (f g : MvPolynomial (Fin n) S)
    (hfg : f * g ∈
      Ideal.map (MvPolynomial.C : S →+* MvPolynomial (Fin n) S) I)
    {gamma : S} (hgamma : gamma ∈ g.coeffs) :
    ∃ q : ℕ, 1 ≤ q ∧
      f ^ q * MvPolynomial.C gamma ∈
        Ideal.map (MvPolynomial.C : S →+* MvPolynomial (Fin n) S) I := by
  obtain ⟨q, hq, hDM⟩ :=
    exists_dedekindMertens_mvCoefficientModule (A := ℤ) f g
  refine ⟨q, hq, ?_⟩
  exact mvPolynomial_pow_mul_C_mem_coefficientExtension I hDM
    (mvCoefficientModule_le_restrictScalars_of_mem_map_C I (f * g) hfg)
    f (coeff_mem_mvCoefficientModule_int f)
    (Submodule.subset_span hgamma)

end CoefficientExtraction

section GroundIdeal

variable {R : Type*} [CommRing R]

/-- Saturation of an ideal along a submonoid, expressed as extension to the
localization followed by contraction. This is the modern model of Noether's
stage ground ideal once the submonoid is chosen to be the nonzero polynomials
in the permitted late variables. -/
noncomputable def groundIdealAlong (M : Submonoid R) (I : Ideal R) : Ideal R :=
  Ideal.comap (algebraMap R (Localization M))
    (Ideal.map (algebraMap R (Localization M)) I)

/-- Witness form of membership in the localized-contracted ground ideal. -/
theorem mem_groundIdealAlong_iff (M : Submonoid R) (I : Ideal R) (x : R) :
    x ∈ groundIdealAlong M I ↔ ∃ m ∈ M, m * x ∈ I := by
  change algebraMap R (Localization M) x ∈
      Ideal.map (algebraMap R (Localization M)) I ↔ _
  exact IsLocalization.algebraMap_mem_map_algebraMap_iff
    M (Localization M) I x

end GroundIdeal

section ParameterCoefficientGroundBridge

variable {P X : Type*} {m : ℕ} [Field P]

/-- Source equations (19)--(20) in abstract transformed/saturated form.  If
the first parameter polynomial transforms to an allowed ground multiplier,
then every base-polynomial coefficient of the second factor belongs to the
ground ideal. -/
theorem parameterCoefficient_mem_groundIdealAlong
    (M : Submonoid
      (MvPolynomial X (FractionRing (MvPolynomial (Fin m) P))))
    (I : Ideal (MvPolynomial X P))
    (tau : MvPolynomial X (FractionRing (MvPolynomial (Fin m) P))
      ≃ₐ[FractionRing (MvPolynomial (Fin m) P)]
      MvPolynomial X (FractionRing (MvPolynomial (Fin m) P)))
    (phi Gamma : MvPolynomial (Fin m) (MvPolynomial X P))
    (hphi : parameterTransformHom (P := P) (U := Fin m) tau phi ∈ M)
    (hprod : phi * Gamma ∈
      Ideal.map
        (MvPolynomial.C : MvPolynomial X P →+*
          MvPolynomial (Fin m) (MvPolynomial X P)) I)
    {gamma : MvPolynomial X P} (hgamma : gamma ∈ Gamma.coeffs) :
    genericTransformHom (P := P) (U := Fin m) tau gamma ∈
      groundIdealAlong M
        (genericTransformIdeal (P := P) (U := Fin m) tau I) := by
  obtain ⟨q, _hq, hcoefficient⟩ :=
    exists_pow_mul_C_mem_coefficientExtension_of_mul_mem
      I phi Gamma hprod hgamma
  rw [mem_groundIdealAlong_iff]
  refine ⟨parameterTransformHom (P := P) (U := Fin m) tau phi ^ q,
    M.pow_mem hphi q, ?_⟩
  have hmapped :=
    Ideal.mem_map_of_mem
      (parameterTransformHom (P := P) (U := Fin m) tau) hcoefficient
  have hcomp :
      (parameterTransformHom (P := P) (U := Fin m) tau).comp
          (MvPolynomial.C : MvPolynomial X P →+*
            MvPolynomial (Fin m) (MvPolynomial X P)) =
        genericTransformHom (P := P) (U := Fin m) tau := by
    apply DFunLike.ext _ _
    intro f
    exact parameterTransformHom_C tau f
  rw [Ideal.map_map, hcomp] at hmapped
  simpa only [map_mul, map_pow, parameterTransformHom_C,
    genericTransformIdeal] using hmapped

end ParameterCoefficientGroundBridge

#print axioms parameterToCoefficient
#print axioms parameterToCoefficient_C
#print axioms genericTransformHom
#print axioms parameterTransformHom
#print axioms genericTransformIdeal
#print axioms parameterTransformHom_C
#print axioms coeff_mem_mvCoefficientModule_int
#print axioms mvCoefficientModule_le_restrictScalars_of_mem_map_C
#print axioms exists_pow_mul_C_mem_coefficientExtension_of_mul_mem
#print axioms groundIdealAlong
#print axioms mem_groundIdealAlong_iff
#print axioms parameterCoefficient_mem_groundIdealAlong

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

