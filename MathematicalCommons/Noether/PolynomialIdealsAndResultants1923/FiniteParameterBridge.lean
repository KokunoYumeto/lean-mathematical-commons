/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.SatzVIBridge

/-!
# Hentzelt--Noether Satz VI over an arbitrary finite parameter type

Controlled source: Kurt Hentzelt, freely edited and conceptually recast by
Emmy Noether, *Zur Theorie der Polynomideale und Resultanten*, witness
`NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
equation (17) and Satz VI at lines 13057--13107.

This module removes the definitional `Fin m` restriction from the
coefficient-extraction and parameter-coefficient ground-ideal bridge.  The
proof renames an arbitrary finite parameter type to `Fin (Fintype.card U)`,
uses the established theorem there, and transports the result back through the
renaming equivalence.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open Ideal

namespace FiniteParameterBridge

noncomputable section

/-- The coefficient-extension consequence of equation (17) for any finite
parameter type.  No chosen enumeration occurs in the statement. -/
theorem exists_pow_mul_C_mem_coefficientExtension_of_mul_mem_finite
    {S U : Type*} [CommRing S] [Fintype U]
    (I : Ideal S) (f g : MvPolynomial U S)
    (hfg : f * g ∈
      Ideal.map (MvPolynomial.C : S →+* MvPolynomial U S) I)
    {gamma : S} (hgamma : gamma ∈ g.coeffs) :
    ∃ q : ℕ, 1 ≤ q ∧
      f ^ q * MvPolynomial.C gamma ∈
        Ideal.map (MvPolynomial.C : S →+* MvPolynomial U S) I := by
  classical
  let e : U ≃ Fin (Fintype.card U) := Fintype.equivFin U
  let E : MvPolynomial U S ≃ₐ[S]
      MvPolynomial (Fin (Fintype.card U)) S :=
    MvPolynomial.renameEquiv S e
  have hfg' : E f * E g ∈
      Ideal.map
        (MvPolynomial.C : S →+* MvPolynomial (Fin (Fintype.card U)) S) I := by
    have hmapped := Ideal.mem_map_of_mem E.toRingEquiv.toRingHom hfg
    have hcomp :
        E.toRingEquiv.toRingHom.comp
            (MvPolynomial.C : S →+* MvPolynomial U S) =
          (MvPolynomial.C : S →+*
            MvPolynomial (Fin (Fintype.card U)) S) := by
      apply DFunLike.ext _ _
      intro s
      exact E.commutes s
    rw [Ideal.map_map, hcomp] at hmapped
    have hE_apply : ∀ p : MvPolynomial U S,
        E.toRingEquiv.toRingHom p = E p := fun _ ↦ rfl
    simpa only [map_mul, hE_apply] using hmapped
  have hgamma' : gamma ∈ (E g).coeffs := by
    obtain ⟨d, hd, hgammaCoeff⟩ := MvPolynomial.mem_coeffs_iff.mp hgamma
    rw [MvPolynomial.mem_coeffs_iff]
    refine ⟨d.mapDomain e, ?_, ?_⟩
    · change d.mapDomain e ∈ (MvPolynomial.rename e g).support
      rw [MvPolynomial.support_rename_of_injective e.injective]
      exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
    · change gamma = (MvPolynomial.rename e g).coeff (d.mapDomain e)
      rw [MvPolynomial.coeff_rename_mapDomain e e.injective]
      exact hgammaCoeff
  obtain ⟨q, hq, hcoefficient⟩ :=
    exists_pow_mul_C_mem_coefficientExtension_of_mul_mem
      I (E f) (E g) hfg' hgamma'
  refine ⟨q, hq, ?_⟩
  have hmapped :=
    Ideal.mem_map_of_mem E.symm.toRingEquiv.toRingHom hcoefficient
  have hcomp :
      E.symm.toRingEquiv.toRingHom.comp
          (MvPolynomial.C : S →+*
          MvPolynomial (Fin (Fintype.card U)) S) =
        (MvPolynomial.C : S →+* MvPolynomial U S) := by
    apply DFunLike.ext _ _
    intro s
    exact E.symm.commutes s
  rw [Ideal.map_map, hcomp] at hmapped
  have hE_apply : ∀ p : MvPolynomial (Fin (Fintype.card U)) S,
      E.symm.toRingEquiv.toRingHom p = E.symm p := fun _ ↦ rfl
  have hCgamma : E.symm (MvPolynomial.C gamma) = MvPolynomial.C gamma :=
    E.symm.commutes gamma
  simpa only [map_mul, map_pow, hE_apply, E.symm_apply_apply, hCgamma] using hmapped

/-- Source equations (19)--(20) with an arbitrary finite parameter type.
This is the enumeration-free form of
`parameterCoefficient_mem_groundIdealAlong`. -/
theorem parameterCoefficient_mem_groundIdealAlong_finite
    {P X U : Type*} [Field P] [Fintype U]
    (M : Submonoid
      (MvPolynomial X (FractionRing (MvPolynomial U P))))
    (I : Ideal (MvPolynomial X P))
    (tau : MvPolynomial X (FractionRing (MvPolynomial U P))
      ≃ₐ[FractionRing (MvPolynomial U P)]
      MvPolynomial X (FractionRing (MvPolynomial U P)))
    (phi Gamma : MvPolynomial U (MvPolynomial X P))
    (hphi : parameterTransformHom (P := P) (U := U) tau phi ∈ M)
    (hprod : phi * Gamma ∈
      Ideal.map
        (MvPolynomial.C : MvPolynomial X P →+*
          MvPolynomial U (MvPolynomial X P)) I)
    {gamma : MvPolynomial X P} (hgamma : gamma ∈ Gamma.coeffs) :
    genericTransformHom (P := P) (U := U) tau gamma ∈
      groundIdealAlong M (genericTransformIdeal (P := P) (U := U) tau I) := by
  obtain ⟨q, _hq, hcoefficient⟩ :=
    exists_pow_mul_C_mem_coefficientExtension_of_mul_mem_finite
      I phi Gamma hprod hgamma
  rw [mem_groundIdealAlong_iff]
  refine ⟨parameterTransformHom (P := P) (U := U) tau phi ^ q,
    M.pow_mem hphi q, ?_⟩
  have hmapped :=
    Ideal.mem_map_of_mem
      (parameterTransformHom (P := P) (U := U) tau) hcoefficient
  have hcomp :
      (parameterTransformHom (P := P) (U := U) tau).comp
          (MvPolynomial.C : MvPolynomial X P →+*
            MvPolynomial U (MvPolynomial X P)) =
        genericTransformHom (P := P) (U := U) tau := by
    apply DFunLike.ext _ _
    intro f
    exact parameterTransformHom_C tau f
  rw [Ideal.map_map, hcomp] at hmapped
  simpa only [map_mul, map_pow, parameterTransformHom_C,
    genericTransformIdeal] using hmapped

#print axioms exists_pow_mul_C_mem_coefficientExtension_of_mul_mem_finite
#print axioms parameterCoefficient_mem_groundIdealAlong_finite

end

end FiniteParameterBridge

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

