/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.SatzVIReverse
import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.StageMultipliers
import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.GenericParameters

/-!
# Common parameter presentations and the transformed-ground-ideal equality

Controlled source: Kurt Hentzelt, freely edited and conceptually recast by
Emmy Noether, *Zur Theorie der Polynomideale und Resultanten*, witness
`NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
Satz VI and equations (18)--(20) at lines 13080--13107.

This module gives two rational-function polynomials one common parameter
denominator, proves that scalar clearing preserves the literal late-variable
multiplier class, and establishes both directions of Satz VI's transformed-
ground-ideal assertion. The final theorem specializes directly to the
source's algebraically independent lower-pair parameters; no `Fin` enumeration
is exposed.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

noncomputable section

section GenericCommonParameterPresentation

variable {P U X : Type*} [Field P]

attribute [local instance] MvPolynomial.algebraMvPolynomial

local instance commonParameterFractionMvPolynomialIsLocalization :
    IsLocalization
      ((nonZeroDivisors (MvPolynomial U P)).map
        (MvPolynomial.C : MvPolynomial U P →+*
          MvPolynomial X (MvPolynomial U P)).toMonoidHom)
      (MvPolynomial X (FractionRing (MvPolynomial U P))) :=
  isLocalizedModule_iff_isLocalization.mp <|
    (isLocalizedModule_iff_isBaseChange
      (nonZeroDivisors (MvPolynomial U P))
      (FractionRing (MvPolynomial U P)) _).mpr <|
      .of_equiv
        (MvPolynomial.algebraTensorAlgEquiv _ _).toLinearEquiv fun _ ↦ by simp

/-- Simultaneous common-denominator presentation over an arbitrary parameter
type.  Finiteness is not needed for this localization fact. -/
theorem exists_common_parameterPresentation
    (F G : MvPolynomial X (FractionRing (MvPolynomial U P))) :
    ∃ d : MvPolynomial U P, d ≠ 0 ∧
      ∃ phi Gamma : MvPolynomial U (MvPolynomial X P),
        MvPolynomial.C
            (algebraMap (MvPolynomial U P)
              (FractionRing (MvPolynomial U P)) d) * F =
          parameterToCoefficient (P := P) (U := U) (X := X) phi ∧
        MvPolynomial.C
            (algebraMap (MvPolynomial U P)
              (FractionRing (MvPolynomial U P)) d) * G =
          parameterToCoefficient (P := P) (U := U) (X := X) Gamma := by
  let A := MvPolynomial U P
  let K := FractionRing A
  let Q := MvPolynomial X A
  let M := (nonZeroDivisors A).map
    (MvPolynomial.C : A →+* Q).toMonoidHom
  obtain ⟨f, g, denominator, hF, hG⟩ :=
    IsLocalization.surj₂ M (MvPolynomial X K) F G
  obtain ⟨d, hd, hdenominator⟩ := denominator.property
  rw [← hdenominator] at hF hG
  refine ⟨d, nonZeroDivisors.ne_zero hd,
    nestedVariableSwapEquiv (P := P) (U := U) (Y := X) f,
    nestedVariableSwapEquiv (P := P) (U := U) (Y := X) g, ?_, ?_⟩
  · simpa [A, K, Q, M, parameterToCoefficient,
      nestedVariableSwapEquiv, mul_comm] using hF
  · simpa [A, K, Q, M, parameterToCoefficient,
      nestedVariableSwapEquiv, mul_comm] using hG

end GenericCommonParameterPresentation

section GenericStageReverseInclusion

variable {P U : Type*} [Field P] [Fintype U]
variable {n : ℕ}

omit [Fintype U] in
/-- Multiplying by a nonzero parameter-field constant preserves the concrete
late-variable stage multiplier condition. -/
theorem parameterTransformHom_mem_nonzeroLateVariableSubmonoid_of_eq
    (cutoff : ℕ)
    (tau : MvPolynomial (Fin n) (FractionRing (MvPolynomial U P))
      ≃ₐ[FractionRing (MvPolynomial U P)]
      MvPolynomial (Fin n) (FractionRing (MvPolynomial U P)))
    (phi : MvPolynomial U (MvPolynomial (Fin n) P))
    (b : MvPolynomial (Fin n) (FractionRing (MvPolynomial U P)))
    (hb : b ∈ nonzeroLateVariableSubmonoid
      (S := FractionRing (MvPolynomial U P)) (n := n) cutoff)
    {c : FractionRing (MvPolynomial U P)} (hc : c ≠ 0)
    (hpresentation : MvPolynomial.C c * b =
      parameterTransformHom (P := P) (U := U) tau phi) :
    parameterTransformHom (P := P) (U := U) tau phi ∈
      nonzeroLateVariableSubmonoid
        (S := FractionRing (MvPolynomial U P)) (n := n) cutoff := by
  rw [← hpresentation]
  exact
    (nonzeroLateVariableSubmonoid
      (S := FractionRing (MvPolynomial U P)) (n := n) cutoff).mul_mem
      ((C_mem_nonzeroLateVariableSubmonoid_iff
        (S := FractionRing (MvPolynomial U P)) (n := n) cutoff c).2 hc) hb

/-- The hard reverse inclusion for an arbitrary finite parameter type. -/
theorem mem_genericTransformIdeal_comap_stageGround_of_mem_stageGround
    (cutoff : ℕ)
    (I : Ideal (MvPolynomial (Fin n) P))
    (tau : MvPolynomial (Fin n) (FractionRing (MvPolynomial U P))
      ≃ₐ[FractionRing (MvPolynomial U P)]
      MvPolynomial (Fin n) (FractionRing (MvPolynomial U P)))
    {G : MvPolynomial (Fin n) (FractionRing (MvPolynomial U P))}
    (hG : G ∈ stageGroundIdeal
      (S := FractionRing (MvPolynomial U P)) cutoff
      (genericTransformIdeal (P := P) (U := U) tau I)) :
    G ∈ genericTransformIdeal (P := P) (U := U) tau
      (Ideal.comap (genericTransformHom (P := P) (U := U) tau)
        (stageGroundIdeal (S := FractionRing (MvPolynomial U P)) cutoff
          (genericTransformIdeal (P := P) (U := U) tau I))) := by
  rw [mem_stageGroundIdeal_iff] at hG
  obtain ⟨b, hb0, hbvars, hbG⟩ := hG
  let M := nonzeroLateVariableSubmonoid
    (S := FractionRing (MvPolynomial U P)) (n := n) cutoff
  have hbM : b ∈ M := ⟨hb0, hbvars⟩
  obtain ⟨d, hd, phi, Gamma, hbPresentation, hGPresentation⟩ :=
    exists_common_parameterPresentation
      (P := P) (U := U) (X := Fin n) (tau.symm b) (tau.symm G)
  let c : FractionRing (MvPolynomial U P) :=
    algebraMap (MvPolynomial U P) (FractionRing (MvPolynomial U P)) d
  have hc : c ≠ 0 := by
    dsimp [c]
    simpa using
      ((IsFractionRing.injective
        (MvPolynomial U P) (FractionRing (MvPolynomial U P))).ne hd)
  have htauC : tau (MvPolynomial.C c) = MvPolynomial.C c := tau.commutes c
  have hphiPresentation :
      MvPolynomial.C c * b =
        parameterTransformHom (P := P) (U := U) tau phi := by
    calc
      MvPolynomial.C c * b =
          tau (MvPolynomial.C c) * tau (tau.symm b) := by
            rw [htauC, tau.apply_symm_apply]
      _ = tau (MvPolynomial.C c * tau.symm b) := by rw [map_mul]
      _ = tau
          (parameterToCoefficient (P := P) (U := U) (X := Fin n) phi) :=
            congrArg tau hbPresentation
      _ = parameterTransformHom (P := P) (U := U) tau phi := rfl
  have hGammaPresentation :
      MvPolynomial.C c * G =
        parameterTransformHom (P := P) (U := U) tau Gamma := by
    calc
      MvPolynomial.C c * G =
          tau (MvPolynomial.C c) * tau (tau.symm G) := by
            rw [htauC, tau.apply_symm_apply]
      _ = tau (MvPolynomial.C c * tau.symm G) := by rw [map_mul]
      _ = tau
          (parameterToCoefficient (P := P) (U := U) (X := Fin n) Gamma) :=
            congrArg tau hGPresentation
      _ = parameterTransformHom (P := P) (U := U) tau Gamma := rfl
  have hphiM : parameterTransformHom (P := P) (U := U) tau phi ∈ M :=
    parameterTransformHom_mem_nonzeroLateVariableSubmonoid_of_eq
      cutoff tau phi b hbM hc hphiPresentation
  have hpreimage := Ideal.mem_map_of_mem
    tau.symm.toRingEquiv.toRingHom hbG
  have hgroundMap :
      algebraMap P (FractionRing (MvPolynomial U P)) =
        groundToParameterFraction (P := P) (U := U) := by
    apply DFunLike.ext _ _
    intro x
    change algebraMap P (FractionRing (MvPolynomial U P)) x =
      algebraMap (MvPolynomial U P) (FractionRing (MvPolynomial U P))
        (MvPolynomial.C x)
    rw [IsScalarTower.algebraMap_apply P (MvPolynomial U P)
      (FractionRing (MvPolynomial U P))]
    rfl
  have hcomp :
      tau.symm.toRingEquiv.toRingHom.comp
          (genericTransformHom (P := P) (U := U) tau) =
        MvPolynomial.map
          (groundToParameterFraction (P := P) (U := U)) := by
    apply DFunLike.ext _ _
    intro f
    change tau.symm
        (tau (MvPolynomial.map
          (algebraMap P (FractionRing (MvPolynomial U P))) f)) =
      MvPolynomial.map
        (groundToParameterFraction (P := P) (U := U)) f
    rw [tau.symm_apply_apply, hgroundMap]
  rw [genericTransformIdeal, Ideal.map_map, hcomp] at hpreimage
  have hpreimageProduct :
      tau.symm b * tau.symm G ∈
        Ideal.map
          (MvPolynomial.map
            (groundToParameterFraction (P := P) (U := U))) I := by
    simpa using hpreimage
  have hfractionProduct :
      parameterToCoefficient (P := P) (U := U) (X := Fin n)
          (phi * Gamma) ∈
        Ideal.map
          (MvPolynomial.map
            (groundToParameterFraction (P := P) (U := U))) I := by
    rw [map_mul]
    rw [← hbPresentation, ← hGPresentation]
    rw [show
      (MvPolynomial.C c * tau.symm b) *
          (MvPolynomial.C c * tau.symm G) =
        (MvPolynomial.C c * MvPolynomial.C c) *
          (tau.symm b * tau.symm G) by ring]
    exact
      (Ideal.map
        (MvPolynomial.map
          (groundToParameterFraction (P := P) (U := U))) I).mul_mem_left
        (MvPolynomial.C c * MvPolynomial.C c) hpreimageProduct
  have hreverse :=
    mem_genericTransformIdeal_comap_ground_of_fractionProduct
      M I tau phi Gamma
      (fun {_c} hc0 ↦
        (C_mem_nonzeroLateVariableSubmonoid_iff
          (S := FractionRing (MvPolynomial U P))
          (n := n) cutoff _c).2 hc0)
      hphiM hfractionProduct hc hGammaPresentation
  simpa [M, stageGroundIdeal] using hreverse

/-- Satz VI's transformed-ground-ideal equality, stated without choosing an
enumeration of the finite parameter type. -/
theorem stageGroundIdeal_genericTransform_eq
    (cutoff : ℕ)
    (I : Ideal (MvPolynomial (Fin n) P))
    (tau : MvPolynomial (Fin n) (FractionRing (MvPolynomial U P))
      ≃ₐ[FractionRing (MvPolynomial U P)]
      MvPolynomial (Fin n) (FractionRing (MvPolynomial U P))) :
    stageGroundIdeal (S := FractionRing (MvPolynomial U P)) cutoff
        (genericTransformIdeal (P := P) (U := U) tau I) =
      genericTransformIdeal (P := P) (U := U) tau
        (Ideal.comap (genericTransformHom (P := P) (U := U) tau)
          (stageGroundIdeal (S := FractionRing (MvPolynomial U P)) cutoff
            (genericTransformIdeal (P := P) (U := U) tau I))) := by
  apply le_antisymm
  · intro G hG
    exact mem_genericTransformIdeal_comap_stageGround_of_mem_stageGround
      cutoff I tau hG
  · change Ideal.map
        (genericTransformHom (P := P) (U := U) tau)
        (Ideal.comap (genericTransformHom (P := P) (U := U) tau)
          (stageGroundIdeal (S := FractionRing (MvPolynomial U P)) cutoff
            (genericTransformIdeal (P := P) (U := U) tau I))) ≤ _
    exact Ideal.map_comap_le

end GenericStageReverseInclusion

section SourceSpecialization

open CoordinateShear.IndependentParameters

variable {P : Type*} [Field P]
variable {n : ℕ}

/-- Source-specialized Satz VI: the stage ground ideal of Noether's generic
independent lower-unitriangular transform is again the extension of its
contraction to the original polynomial ring. -/
theorem stageGroundIdeal_independentLowerUnitriangular_eq
    (cutoff : ℕ) (I : Ideal (MvPolynomial (Fin n) P)) :
    stageGroundIdeal
        (S := FractionRing (MvPolynomial (LowerParameter n) P)) cutoff
        (genericTransformIdeal (P := P) (U := LowerParameter n)
          (independentLowerUnitriangularEquiv (P := P) (n := n)) I) =
      genericTransformIdeal (P := P) (U := LowerParameter n)
        (independentLowerUnitriangularEquiv (P := P) (n := n))
        (Ideal.comap
          (genericTransformHom (P := P) (U := LowerParameter n)
            (independentLowerUnitriangularEquiv (P := P) (n := n)))
          (stageGroundIdeal
            (S := FractionRing (MvPolynomial (LowerParameter n) P)) cutoff
            (genericTransformIdeal (P := P) (U := LowerParameter n)
              (independentLowerUnitriangularEquiv (P := P) (n := n)) I))) := by
  exact stageGroundIdeal_genericTransform_eq
    (U := LowerParameter n) cutoff I
    (independentLowerUnitriangularEquiv (P := P) (n := n))

end SourceSpecialization

#print axioms exists_common_parameterPresentation
#print axioms parameterTransformHom_mem_nonzeroLateVariableSubmonoid_of_eq
#print axioms mem_genericTransformIdeal_comap_stageGround_of_mem_stageGround
#print axioms stageGroundIdeal_genericTransform_eq
#print axioms stageGroundIdeal_independentLowerUnitriangular_eq

end

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

