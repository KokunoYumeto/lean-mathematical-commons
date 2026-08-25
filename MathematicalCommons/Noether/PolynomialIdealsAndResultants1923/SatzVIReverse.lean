/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.LocalizationBridge
import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.FiniteParameterBridge

/-!
# Denominator absorption and coefficient reconstruction for Satz VI

Controlled source: Kurt Hentzelt, freely edited and conceptually recast by
Emmy Noether, *Zur Theorie der Polynomideale und Resultanten*, witness
`NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
Satz VI and equations (17)--(20) at lines 13057--13107.

This module proves denominator absorption and coefficient reconstruction for
an arbitrary finite parameter type `U`. No enumeration of `U` appears in a
public statement. No primary, saturation, or denominator-cancellation
hypothesis is imposed on the original ideal; the final cancellation is only
of a genuine nonzero scalar in the rational function field.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

noncomputable section

section GenericDenominatorAbsorption

variable {P U X : Type*} [Field P] [Fintype U]

/-- Embed a parameter polynomial into the swapped source-shaped polynomial
ring. -/
noncomputable def liftParameterPolynomial :
    MvPolynomial U P →+* MvPolynomial U (MvPolynomial X P) :=
  (nestedVariableSwapEquiv (P := P) (U := U) (Y := X)).toRingEquiv.toRingHom.comp
    (MvPolynomial.C :
      MvPolynomial U P →+* MvPolynomial X (MvPolynomial U P))

omit [Fintype U] in
@[simp] theorem parameterToCoefficient_liftParameterPolynomial
    (s : MvPolynomial U P) :
    parameterToCoefficient (P := P) (U := U) (X := X)
        (liftParameterPolynomial (P := P) (U := U) (X := X) s) =
      MvPolynomial.C
        (algebraMap (MvPolynomial U P)
          (FractionRing (MvPolynomial U P)) s) := by
  simp [liftParameterPolynomial, parameterToCoefficient,
    nestedVariableSwapEquiv]

omit [Fintype U] in
@[simp] theorem parameterTransformHom_liftParameterPolynomial
    (tau : MvPolynomial X (FractionRing (MvPolynomial U P))
      ≃ₐ[FractionRing (MvPolynomial U P)]
      MvPolynomial X (FractionRing (MvPolynomial U P)))
    (s : MvPolynomial U P) :
    parameterTransformHom (P := P) (U := U) tau
        (liftParameterPolynomial (P := P) (U := U) (X := X) s) =
      MvPolynomial.C
        (algebraMap (MvPolynomial U P)
          (FractionRing (MvPolynomial U P)) s) := by
  rw [parameterTransformHom, RingHom.comp_apply,
    parameterToCoefficient_liftParameterPolynomial]
  exact tau.commutes _

omit [Fintype U] in
/-- Mapping the parameter-polynomial extension of a ground ideal through the
variable swap gives the constant-polynomial extension in the parameter
variables. -/
theorem nestedVariableSwapEquiv_mem_parameterExtension
    (I : Ideal (MvPolynomial X P))
    {q : MvPolynomial X (MvPolynomial U P)}
    (hq : q ∈ Ideal.map
      (MvPolynomial.map (MvPolynomial.C : P →+* MvPolynomial U P)) I) :
    nestedVariableSwapEquiv (P := P) (U := U) (Y := X) q ∈
      Ideal.map
        (MvPolynomial.C : MvPolynomial X P →+*
          MvPolynomial U (MvPolynomial X P)) I := by
  have hmapped := Ideal.mem_map_of_mem
    (nestedVariableSwapEquiv
      (P := P) (U := U) (Y := X)).toRingEquiv.toRingHom hq
  have hcomp :
      (nestedVariableSwapEquiv
        (P := P) (U := U) (Y := X)).toRingEquiv.toRingHom.comp
          (MvPolynomial.map (MvPolynomial.C : P →+* MvPolynomial U P)) =
        (MvPolynomial.C : MvPolynomial X P →+*
          MvPolynomial U (MvPolynomial X P)) := by
    apply DFunLike.ext _ _
    intro p
    exact nestedVariableSwapEquiv_map_C p
  rw [Ideal.map_map, hcomp] at hmapped
  exact hmapped

omit [Fintype U] in
/-- Clear a product's parameter denominator and absorb it into the first
factor, for an arbitrary finite parameter type. -/
theorem exists_nonzero_parameter_denominator_mul_mem_coefficientExtension
    (I : Ideal (MvPolynomial X P))
    (phi Gamma : MvPolynomial U (MvPolynomial X P))
    (hfrac :
      parameterToCoefficient (P := P) (U := U) (X := X) (phi * Gamma) ∈
        Ideal.map
          (MvPolynomial.map
            (groundToParameterFraction (P := P) (U := U))) I) :
    ∃ s : MvPolynomial U P, s ≠ 0 ∧
      (liftParameterPolynomial (P := P) (U := U) (X := X) s * phi) * Gamma ∈
        Ideal.map
          (MvPolynomial.C : MvPolynomial X P →+*
            MvPolynomial U (MvPolynomial X P)) I := by
  obtain ⟨s, hs, q, hq, heq⟩ :=
    exists_nonzero_parameter_denominator_and_numerator I hfrac
  have hqSwap := nestedVariableSwapEquiv_mem_parameterExtension I hq
  have heqBeforeLocalization :
      MvPolynomial.C s *
          MvPolynomial.commAlgEquiv P U X (phi * Gamma) = q := by
    apply MvPolynomial.map_injective
      (algebraMap (MvPolynomial U P) (FractionRing (MvPolynomial U P)))
      (IsFractionRing.injective
        (MvPolynomial U P) (FractionRing (MvPolynomial U P)))
    simpa [parameterToCoefficient] using heq
  have heqAfterSwap := congrArg
    (nestedVariableSwapEquiv (P := P) (U := U) (Y := X))
    heqBeforeLocalization
  have habsorb :
      liftParameterPolynomial (P := P) (U := U) (X := X) s *
          (phi * Gamma) =
        nestedVariableSwapEquiv (P := P) (U := U) (Y := X) q := by
    simpa [liftParameterPolynomial, nestedVariableSwapEquiv] using heqAfterSwap
  refine ⟨s, hs, ?_⟩
  simpa only [mul_assoc, habsorb] using hqSwap

/-- After denominator absorption, every coefficient of the second factor has
its generic transform in the chosen ground ideal. -/
theorem parameterCoefficient_mem_groundIdealAlong_of_fractionProduct
    (M : Submonoid (MvPolynomial X (FractionRing (MvPolynomial U P))))
    (I : Ideal (MvPolynomial X P))
    (tau : MvPolynomial X (FractionRing (MvPolynomial U P))
      ≃ₐ[FractionRing (MvPolynomial U P)]
      MvPolynomial X (FractionRing (MvPolynomial U P)))
    (phi Gamma : MvPolynomial U (MvPolynomial X P))
    (hconstants : ∀ {c : FractionRing (MvPolynomial U P)},
      c ≠ 0 → MvPolynomial.C c ∈ M)
    (hphi : parameterTransformHom (P := P) (U := U) tau phi ∈ M)
    (hfrac :
      parameterToCoefficient (P := P) (U := U) (X := X) (phi * Gamma) ∈
        Ideal.map
          (MvPolynomial.map
            (groundToParameterFraction (P := P) (U := U))) I)
    {gamma : MvPolynomial X P} (hgamma : gamma ∈ Gamma.coeffs) :
    genericTransformHom (P := P) (U := U) tau gamma ∈
      groundIdealAlong M (genericTransformIdeal (P := P) (U := U) tau I) := by
  obtain ⟨s, hs, hprod⟩ :=
    exists_nonzero_parameter_denominator_mul_mem_coefficientExtension
      I phi Gamma hfrac
  apply FiniteParameterBridge.parameterCoefficient_mem_groundIdealAlong_finite
    M I tau
    (liftParameterPolynomial (P := P) (U := U) (X := X) s * phi) Gamma
  · rw [map_mul, parameterTransformHom_liftParameterPolynomial]
    have hsFraction :
        algebraMap (MvPolynomial U P) (FractionRing (MvPolynomial U P)) s ≠ 0 := by
      simpa using
        ((IsFractionRing.injective
          (MvPolynomial U P) (FractionRing (MvPolynomial U P))).ne hs)
    exact M.mul_mem (hconstants hsFraction) hphi
  · exact hprod
  · exact hgamma

/-- Reconstruct the entire transformed second factor over the contraction of
the ground ideal, with no chosen enumeration of the parameter type. -/
theorem parameterTransformHom_mem_genericTransformIdeal_of_fractionProduct
    (M : Submonoid (MvPolynomial X (FractionRing (MvPolynomial U P))))
    (I : Ideal (MvPolynomial X P))
    (tau : MvPolynomial X (FractionRing (MvPolynomial U P))
      ≃ₐ[FractionRing (MvPolynomial U P)]
      MvPolynomial X (FractionRing (MvPolynomial U P)))
    (phi Gamma : MvPolynomial U (MvPolynomial X P))
    (hconstants : ∀ {c : FractionRing (MvPolynomial U P)},
      c ≠ 0 → MvPolynomial.C c ∈ M)
    (hphi : parameterTransformHom (P := P) (U := U) tau phi ∈ M)
    (hfrac :
      parameterToCoefficient (P := P) (U := U) (X := X) (phi * Gamma) ∈
        Ideal.map
          (MvPolynomial.map
            (groundToParameterFraction (P := P) (U := U))) I) :
    parameterTransformHom (P := P) (U := U) tau Gamma ∈
      genericTransformIdeal (P := P) (U := U) tau
        (Ideal.comap (genericTransformHom (P := P) (U := U) tau)
          (groundIdealAlong M
            (genericTransformIdeal (P := P) (U := U) tau I))) := by
  let J := groundIdealAlong M
    (genericTransformIdeal (P := P) (U := U) tau I)
  let J0 := Ideal.comap (genericTransformHom (P := P) (U := U) tau) J
  have hGamma : Gamma ∈
      Ideal.map
        (MvPolynomial.C : MvPolynomial X P →+*
          MvPolynomial U (MvPolynomial X P)) J0 := by
    rw [MvPolynomial.mem_map_C_iff]
    intro d
    by_cases hd : Gamma.coeff d = 0
    · simp [hd]
    · change genericTransformHom (P := P) (U := U) tau
          (Gamma.coeff d) ∈ J
      exact parameterCoefficient_mem_groundIdealAlong_of_fractionProduct
        M I tau phi Gamma hconstants hphi hfrac
        (MvPolynomial.coeff_mem_coeffs d hd)
  have hmapped := Ideal.mem_map_of_mem
    (parameterTransformHom (P := P) (U := U) tau) hGamma
  have hcomp :
      (parameterTransformHom (P := P) (U := U) tau).comp
          (MvPolynomial.C : MvPolynomial X P →+*
            MvPolynomial U (MvPolynomial X P)) =
        genericTransformHom (P := P) (U := U) tau := by
    apply DFunLike.ext _ _
    intro f
    exact parameterTransformHom_C tau f
  rw [Ideal.map_map, hcomp] at hmapped
  exact hmapped

/-- Elementwise reverse inclusion after a nonzero common-denominator
presentation of the second factor. -/
theorem mem_genericTransformIdeal_comap_ground_of_fractionProduct
    (M : Submonoid (MvPolynomial X (FractionRing (MvPolynomial U P))))
    (I : Ideal (MvPolynomial X P))
    (tau : MvPolynomial X (FractionRing (MvPolynomial U P))
      ≃ₐ[FractionRing (MvPolynomial U P)]
      MvPolynomial X (FractionRing (MvPolynomial U P)))
    (phi Gamma : MvPolynomial U (MvPolynomial X P))
    (hconstants : ∀ {c : FractionRing (MvPolynomial U P)},
      c ≠ 0 → MvPolynomial.C c ∈ M)
    (hphi : parameterTransformHom (P := P) (U := U) tau phi ∈ M)
    (hfrac :
      parameterToCoefficient (P := P) (U := U) (X := X) (phi * Gamma) ∈
        Ideal.map
          (MvPolynomial.map
            (groundToParameterFraction (P := P) (U := U))) I)
    {G : MvPolynomial X (FractionRing (MvPolynomial U P))}
    {c : FractionRing (MvPolynomial U P)} (hc : c ≠ 0)
    (hGamma : MvPolynomial.C c * G =
      parameterTransformHom (P := P) (U := U) tau Gamma) :
    G ∈ genericTransformIdeal (P := P) (U := U) tau
      (Ideal.comap (genericTransformHom (P := P) (U := U) tau)
        (groundIdealAlong M
          (genericTransformIdeal (P := P) (U := U) tau I))) := by
  have hmem :=
    parameterTransformHom_mem_genericTransformIdeal_of_fractionProduct
      M I tau phi Gamma hconstants hphi hfrac
  rw [← hGamma] at hmem
  exact (Ideal.unit_mul_mem_iff_mem _
    ((isUnit_iff_ne_zero.mpr hc).map
      (MvPolynomial.C : FractionRing (MvPolynomial U P) →+*
        MvPolynomial X (FractionRing (MvPolynomial U P))))).mp hmem

end GenericDenominatorAbsorption

#print axioms liftParameterPolynomial
#print axioms parameterToCoefficient_liftParameterPolynomial
#print axioms parameterTransformHom_liftParameterPolynomial
#print axioms nestedVariableSwapEquiv_mem_parameterExtension
#print axioms exists_nonzero_parameter_denominator_mul_mem_coefficientExtension
#print axioms parameterCoefficient_mem_groundIdealAlong_of_fractionProduct
#print axioms parameterTransformHom_mem_genericTransformIdeal_of_fractionProduct
#print axioms mem_genericTransformIdeal_comap_ground_of_fractionProduct

end

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

