import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.FirstGroundModuleTorsion
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Hentzelt--Noether equation (24): retain the second variable and localize the later ones

Module for P22, controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
lines 13162--13173.

After the first variable has been separated, line 13164 adjoins the variables
`x₃, ...` to the coefficient field while retaining `x₂` as a polynomial
variable.  For

* `B = P[x₃, ...]`,
* `A = B[x₂]`,
* `K = Frac(B)`, and
* `R = K[x₂]`,

the ring map used below is `A → R`, not `A → Frac(A)`: the second variable is
therefore never inverted.  The finite `ξ`-space is represented before and
after localization by `A[x₁]_<k` and `R[x₁]_<k`.

The general part of this file proves that nonzero-scalar saturation commutes
with localization.  Its reverse inclusion is not a denominator-clearing
assumption: saturation is characterized by torsion-freeness of the ambient
quotient, and Mathlib proves that localization preserves torsion-freeness.
The source-specific result transports line 13162 through the two exact changes
of coefficients and supplies the full-rank premise for equation (24)'s Smith
form over the PID `K[x₂]`.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open MvPolynomial

namespace RegularIdealDecomposition

noncomputable section

section DegreeLTTransport

variable {R S : Type*} [CommRing R] [CommRing S]

set_option backward.defeqAttrib.useBackward true in
attribute [local instance]
  RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
/-- Apply a coefficient-ring equivalence to a bounded polynomial module.
The monomial basis makes the construction independent of degree lemmas for
`Polynomial.map`. -/
noncomputable def degreeLTMapEquiv (e : R ≃+* S) (k : ℕ) :
    Polynomial.degreeLT R k ≃ₛₗ[(e : R →+* S)]
      Polynomial.degreeLT S k :=
  ((Polynomial.degreeLT.basis R k).repr).trans
    ((Finsupp.mapRange.linearEquiv (α := Fin k) e.toSemilinearEquiv).trans
      (Polynomial.degreeLT.basis S k).repr.symm)

end DegreeLTTransport

section SaturationTransport

variable {R S E F : Type*}
variable [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
variable [CommSemiring S] [NoZeroDivisors S] [Nontrivial S]
variable [AddCommMonoid E] [Module R E] [AddCommMonoid F] [Module S F]

set_option backward.defeqAttrib.useBackward true in
attribute [local instance]
  RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
/-- Nonzero-scalar saturation is natural under simultaneous equivalences of
the coefficient ring and the module. -/
theorem map_nonzeroScalarSaturation_equiv
    (eR : R ≃+* S)
    (e : E ≃ₛₗ[(eR : R →+* S)] F)
    (M : Submodule R E) :
    (nonzeroScalarSaturation M).map e.toLinearMap =
      nonzeroScalarSaturation (M.map e.toLinearMap) := by
  apply le_antisymm
  · rintro y ⟨x, ⟨b, hb, hbx⟩, rfl⟩
    refine ⟨eR b, ?_, ?_⟩
    · intro hbmap
      apply hb
      apply eR.injective
      simpa using hbmap
    · exact ⟨b • x, hbx, e.map_smulₛₗ b x⟩
  · rintro y ⟨c, hc, hcy⟩
    let x : E := e.symm y
    let b : R := eR.symm c
    have hb : b ≠ 0 := by
      intro hb0
      apply hc
      apply eR.symm.injective
      simpa [b] using hb0
    obtain ⟨m, hm, hmmap⟩ := hcy
    have hbx : b • x ∈ M := by
      have hbm : b • x = m := by
        apply e.injective
        calc
          e (b • x) = eR b • e x := e.map_smulₛₗ b x
          _ = c • y := by simp [b, x]
          _ = e m := hmmap.symm
      simpa [hbm] using hm
    exact ⟨x, ⟨b, hb, hbx⟩, e.apply_symm_apply y⟩

end SaturationTransport

section GroundQuotient

variable {R E : Type*} [CommRing R] [IsDomain R]
variable [AddCommGroup E] [Module R E]

/-- Definition I's nonzero-scalar cancellation condition is exactly
torsion-freeness of the quotient by the proposed ground module. -/
theorem isGroundModule_iff_quotient_isTorsionFree
    (G : Submodule R E) :
    IsGroundModule G ↔ Module.IsTorsionFree R (E ⧸ G) := by
  constructor
  · intro hG
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro b q hbq
    by_cases hb : b = 0
    · exact Or.inl hb
    · right
      obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective G q
      rw [← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero] at hbq
      rw [Submodule.Quotient.mk_eq_zero]
      exact hG b g hb hbq
  · intro hQ b g hb hbg
    letI : Module.IsTorsionFree R (E ⧸ G) := hQ
    have hzero :
        b • (Submodule.Quotient.mk g : E ⧸ G) = 0 := by
      rw [← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero]
      exact hbg
    have hmk : (Submodule.Quotient.mk g : E ⧸ G) = 0 :=
      (smul_eq_zero.mp hzero).resolve_left hb
    rw [Submodule.Quotient.mk_eq_zero] at hmk
    exact hmk

end GroundQuotient

section DegreeLTLocalization

variable {A L : Type*} [CommRing A] [CommRing L] [Algebra A L]

/-- Coefficientwise localization of a bounded polynomial module.  The
`Finsupp` middle term is internal; the public source and target remain the
degree-bounded polynomial spaces. -/
noncomputable def degreeLTLocalizationMap (k : ℕ) :
    Polynomial.degreeLT A k →ₗ[A] Polynomial.degreeLT L k :=
  ((Polynomial.degreeLT.basis L k).repr.symm.restrictScalars A).toLinearMap.comp
    ((Finsupp.mapRange.linearMap (α := Fin k) (Algebra.linearMap A L)).comp
      (Polynomial.degreeLT.basis A k).repr.toLinearMap)

variable (D : Submonoid A) [IsLocalization D L]

instance degreeLTLocalizationMap_isLocalizedModule (k : ℕ) :
    IsLocalizedModule D (degreeLTLocalizationMap (A := A) (L := L) k) := by
  unfold degreeLTLocalizationMap
  infer_instance

end DegreeLTLocalization

section LocalizationOfSaturation

variable {A L E F : Type*}
variable [CommRing A] [IsDomain A] [CommRing L] [IsDomain L]
variable [Algebra A L]
variable [AddCommGroup E] [Module A E]
variable [AddCommGroup F] [Module L F] [Module A F] [IsScalarTower A L F]
variable (D : Submonoid A) [IsLocalization D L]
variable (f : E →ₗ[A] F) [IsLocalizedModule D f]

/-- A saturation inclusion remains a saturation inclusion after localization.
This is the rank-relevant half of the exact theorem below. -/
theorem localized_le_nonzeroScalarSaturation_localized
    (hD : D ≤ nonZeroDivisors A) {G M : Submodule A E}
    (hG : G ≤ nonzeroScalarSaturation M) :
    G.localized' L D f ≤
      nonzeroScalarSaturation (M.localized' L D f) := by
  rw [Submodule.localized'_eq_span]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨a, ha, hag⟩ := hG hg
  refine ⟨algebraMap A L a, ?_, ?_⟩
  · intro hamap
    apply ha
    apply IsLocalization.injective L hD
    simpa using hamap
  · rw [algebraMap_smul L, ← f.map_smul]
    exact ⟨a • g, hag, 1, by simp⟩

/-- Exact base change of formula (4): if `G` is the nonzero-scalar
saturation of `M`, then their localizations satisfy the same equality over
the localized coefficient ring. -/
theorem localized_eq_nonzeroScalarSaturation_localized
    (hD : D ≤ nonZeroDivisors A) {G M : Submodule A E}
    (hGM : G = nonzeroScalarSaturation M) :
    G.localized' L D f =
      nonzeroScalarSaturation (M.localized' L D f) := by
  have hforward :
      G.localized' L D f ≤
        nonzeroScalarSaturation (M.localized' L D f) :=
    localized_le_nonzeroScalarSaturation_localized D f hD hGM.le
  have hMG : M ≤ G := by
    rw [hGM]
    exact le_nonzeroScalarSaturation M
  have hMGlocalized :
      M.localized' L D f ≤ G.localized' L D f :=
    by
      rintro x ⟨m, hm, s, hs⟩
      exact ⟨m, hMG hm, s, hs⟩
  have hGround : IsGroundModule G := by
    rw [hGM]
    exact nonzeroScalarSaturation_isGroundModule M
  letI : Module.IsTorsionFree A (E ⧸ G) :=
    (isGroundModule_iff_quotient_isTorsionFree G).mp hGround
  letI : Module.IsTorsionFree L (F ⧸ G.localized' L D f) :=
    IsLocalizedModule.isTorsionFree
      (G.toLocalizedQuotient' L D f) D
  have hGroundLocalized : IsGroundModule (G.localized' L D f) :=
    (isGroundModule_iff_quotient_isTorsionFree
      (G.localized' L D f)).mpr inferInstance
  exact le_antisymm hforward
    (nonzeroScalarSaturation_le_of_le_of_isGroundModule
      hMGlocalized hGroundLocalized)

end LocalizationOfSaturation

section StageOneLateVariableLocalization

variable {P : Type*} [Field P]
variable {n : ℕ}

attribute [local instance] Polynomial.algebra

/-- The source's genuinely later-variable coefficient ring `B = P[x₃,...]`.
The indexing starts after `x₂`; no retained variable occurs in this ring. -/
abbrev lateVariableCoefficientRing (P : Type*) [Field P] (n : ℕ) :=
  MvPolynomial (Fin n) P

/-- The coefficient field obtained by adjoining only the genuinely later
variables. -/
abbrev lateVariableFractionField (P : Type*) [Field P] (n : ℕ) :=
  FractionRing (lateVariableCoefficientRing P n)

/-- The PID `K[x₂]` used for equation (24).  The univariate polynomial
variable is the retained `x₂`, so it is deliberately not inverted. -/
abbrev secondVariablePID (P : Type*) [Field P] (n : ℕ) :=
  Polynomial (lateVariableFractionField P n)

/-- Coordinate form of `A[x₁]_<k`, where `A = P[x₃,...][x₂]`.
Using the finite coefficient vector gives the canonical additive-group
structure needed by quotient localization, without changing the bounded
polynomial represented. -/
abbrev secondVariableBoundedAmbient
    (P : Type*) [Field P] (n k : ℕ) :=
  Fin k → Polynomial (lateVariableCoefficientRing P n)

/-- Coordinate form of `K[x₂][x₁]_<k` after localizing the genuinely later
variables. -/
abbrev localizedSecondVariableBoundedAmbient
    (P : Type*) [Field P] (n k : ℕ) :=
  Fin k → secondVariablePID P n

/-- Expose the source's second variable as univariate while retaining the
later variables in its coefficient ring. -/
noncomputable def secondVariableCoefficientEquiv :
    MvPolynomial (Fin (n + 1)) P ≃+*
      Polynomial (MvPolynomial (Fin n) P) :=
  MvPolynomial.finSuccEquiv P n

set_option backward.defeqAttrib.useBackward true in
attribute [local instance]
  RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
/-- Coefficientwise form of `secondVariableCoefficientEquiv` on the finite
`ξ`-space. -/
noncomputable def secondVariableBoundedEquiv (k : ℕ) :
    Polynomial.degreeLT (MvPolynomial (Fin (n + 1)) P) k ≃ₛₗ[
      (secondVariableCoefficientEquiv (P := P) (n := n) :
        MvPolynomial (Fin (n + 1)) P →+*
          Polynomial (MvPolynomial (Fin n) P))]
      Polynomial.degreeLT (Polynomial (MvPolynomial (Fin n) P)) k :=
  degreeLTMapEquiv (secondVariableCoefficientEquiv (P := P) (n := n)) k

set_option backward.defeqAttrib.useBackward true in
attribute [local instance]
  RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
/-- The exact coefficient-ring equivalence followed by the canonical first
`k` coefficient coordinates. -/
noncomputable def secondVariableBoundedCoordinateEquiv (k : ℕ) :
    Polynomial.degreeLT (MvPolynomial (Fin (n + 1)) P) k ≃ₛₗ[
      (secondVariableCoefficientEquiv (P := P) (n := n) :
        MvPolynomial (Fin (n + 1)) P →+*
          Polynomial (MvPolynomial (Fin n) P))]
      secondVariableBoundedAmbient P n k :=
  (secondVariableBoundedEquiv (P := P) (n := n) k).trans
    (Polynomial.degreeLTEquiv
      (Polynomial (MvPolynomial (Fin n) P)) k)

set_option backward.defeqAttrib.useBackward true in
attribute [local instance]
  RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
/-- The transported bounded stage-one ground module over `P[x₃,...][x₂]`. -/
noncomputable def secondVariableGroundModule
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    Submodule (Polynomial (MvPolynomial (Fin n) P))
      (secondVariableBoundedAmbient P n k) :=
  (boundedPartInDegreeLT (stageOneGroundIdeal I) k).map
    (secondVariableBoundedCoordinateEquiv
      (P := P) (n := n) k).toLinearMap

set_option backward.defeqAttrib.useBackward true in
attribute [local instance]
  RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
/-- The transported bounded original module over `P[x₃,...][x₂]`. -/
noncomputable def secondVariableOriginalModule
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    Submodule (Polynomial (MvPolynomial (Fin n) P))
      (secondVariableBoundedAmbient P n k) :=
  (boundedPartInDegreeLT (finSuccIdeal (n := n + 1) I) k).map
    (secondVariableBoundedCoordinateEquiv
      (P := P) (n := n) k).toLinearMap

set_option backward.defeqAttrib.useBackward true in
attribute [local instance]
  RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
/-- Line 13162 after making `x₂` explicit: the transported ground module is
still exactly formula-(4) saturation of the transported original module. -/
theorem secondVariableGroundModule_eq_saturation
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    secondVariableGroundModule I k =
      nonzeroScalarSaturation (secondVariableOriginalModule I k) := by
  rw [secondVariableGroundModule, secondVariableOriginalModule,
    boundedPartInDegreeLT_stageOneGroundIdeal_eq_saturation]
  exact map_nonzeroScalarSaturation_equiv
    (R := MvPolynomial (Fin (n + 1)) P)
    (S := Polynomial (MvPolynomial (Fin n) P))
    (E := Polynomial.degreeLT (MvPolynomial (Fin (n + 1)) P) k)
    (F := secondVariableBoundedAmbient P n k)
    (secondVariableCoefficientEquiv (P := P) (n := n))
    (secondVariableBoundedCoordinateEquiv (P := P) (n := n) k)
    (boundedPartInDegreeLT (finSuccIdeal (n := n + 1) I) k)

/-- Nonzero polynomials in the genuinely later variables, embedded as
constants in the retained `x₂`-polynomial ring. -/
def lateVariableDenominators :
    Submonoid (Polynomial (MvPolynomial (Fin n) P)) :=
  (nonZeroDivisors (MvPolynomial (Fin n) P)).map
    (Polynomial.C : MvPolynomial (Fin n) P →+*
      Polynomial (MvPolynomial (Fin n) P)).toMonoidHom

/-- The chosen later-variable denominators are non-zero-divisors in
`P[x₃,...][x₂]`. -/
theorem lateVariableDenominators_le_nonZeroDivisors :
    lateVariableDenominators (P := P) (n := n) ≤
      nonZeroDivisors (Polynomial (MvPolynomial (Fin n) P)) := by
  rintro _ ⟨b, hb, rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  simpa using (nonZeroDivisors.coe_ne_zero ⟨b, hb⟩)

local instance lateVariablePolynomialIsLocalization :
    IsLocalization (lateVariableDenominators (P := P) (n := n))
      (Polynomial (FractionRing (MvPolynomial (Fin n) P))) :=
  Polynomial.isLocalization
    (nonZeroDivisors (MvPolynomial (Fin n) P))
    (FractionRing (MvPolynomial (Fin n) P))

/-- Localize the later-variable coefficients of the bounded `ξ`-space while
leaving `x₂` as the polynomial coefficient variable.  This is the bounded
`degreeLT` localization map conjugated by the exact coefficient-coordinate
equivalences on both sides. -/
noncomputable def secondVariableBoundedLocalizationMap (k : ℕ) :
    secondVariableBoundedAmbient P n k →ₗ[
      Polynomial (MvPolynomial (Fin n) P)]
      localizedSecondVariableBoundedAmbient P n k :=
  let sourceCoordinates :=
    (Polynomial.degreeLTEquiv
      (Polynomial (MvPolynomial (Fin n) P)) k).symm
  let targetCoordinates :=
    (Polynomial.degreeLTEquiv
      (Polynomial (FractionRing (MvPolynomial (Fin n) P))) k).restrictScalars
        (Polynomial (MvPolynomial (Fin n) P))
  targetCoordinates.toLinearMap.comp
    ((degreeLTLocalizationMap
      (A := Polynomial (MvPolynomial (Fin n) P))
      (L := Polynomial (FractionRing (MvPolynomial (Fin n) P))) k).comp
      sourceCoordinates.toLinearMap)

local instance secondVariableBoundedLocalizationMap_isLocalizedModule
    (k : ℕ) :
    IsLocalizedModule (lateVariableDenominators (P := P) (n := n))
      (secondVariableBoundedLocalizationMap (P := P) (n := n) k) :=
by
  let sourceCoordinates :=
    (Polynomial.degreeLTEquiv
      (Polynomial (MvPolynomial (Fin n) P)) k).symm
  let targetCoordinates :=
    (Polynomial.degreeLTEquiv
      (Polynomial (FractionRing (MvPolynomial (Fin n) P))) k).restrictScalars
        (Polynomial (MvPolynomial (Fin n) P))
  let localizationMap :=
    degreeLTLocalizationMap
      (A := Polynomial (MvPolynomial (Fin n) P))
      (L := Polynomial (FractionRing (MvPolynomial (Fin n) P))) k
  letI : IsLocalizedModule
      (lateVariableDenominators (P := P) (n := n))
      (localizationMap.comp sourceCoordinates.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right
      (lateVariableDenominators (P := P) (n := n))
      localizationMap sourceCoordinates
  exact IsLocalizedModule.of_linearEquiv
    (lateVariableDenominators (P := P) (n := n))
    (localizationMap.comp sourceCoordinates.toLinearMap)
    targetCoordinates

/-- The actual bounded ground module after adjoining the later variables to
the coefficient field, with `x₂` retained. -/
noncomputable def localizedSecondVariableGroundModule
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    Submodule (Polynomial (FractionRing (MvPolynomial (Fin n) P)))
      (localizedSecondVariableBoundedAmbient P n k) :=
  (secondVariableGroundModule I k).localized'
    (Polynomial (FractionRing (MvPolynomial (Fin n) P)))
    (lateVariableDenominators (P := P) (n := n))
    (secondVariableBoundedLocalizationMap (P := P) (n := n) k)

/-- The actual bounded original module after adjoining the later variables to
the coefficient field, with `x₂` retained. -/
noncomputable def localizedSecondVariableOriginalModule
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    Submodule (Polynomial (FractionRing (MvPolynomial (Fin n) P)))
      (localizedSecondVariableBoundedAmbient P n k) :=
  (secondVariableOriginalModule I k).localized'
    (Polynomial (FractionRing (MvPolynomial (Fin n) P)))
    (lateVariableDenominators (P := P) (n := n))
    (secondVariableBoundedLocalizationMap (P := P) (n := n) k)

set_option backward.defeqAttrib.useBackward true in
/-- Lines 13162--13164 after the exact base change used in equation (24):
the localized ground module remains exactly the nonzero-scalar saturation of
the localized original module over `Frac(P[x₃,...])[x₂]`. -/
theorem localizedSecondVariableGroundModule_eq_saturation
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    localizedSecondVariableGroundModule I k =
      nonzeroScalarSaturation
        (localizedSecondVariableOriginalModule I k) := by
  exact localized_eq_nonzeroScalarSaturation_localized
    (A := Polynomial (MvPolynomial (Fin n) P))
    (L := Polynomial (FractionRing (MvPolynomial (Fin n) P)))
    (E := secondVariableBoundedAmbient P n k)
    (F := localizedSecondVariableBoundedAmbient P n k)
    (G := secondVariableGroundModule I k)
    (M := secondVariableOriginalModule I k)
    (lateVariableDenominators (P := P) (n := n))
    (secondVariableBoundedLocalizationMap (P := P) (n := n) k)
    (lateVariableDenominators_le_nonZeroDivisors (P := P) (n := n))
    (secondVariableGroundModule_eq_saturation I k)

set_option backward.defeqAttrib.useBackward true in
/-- The localized denominator has the same finite rank as the localized
ground module.  Since the retained coefficient ring is the PID
`Frac(P[x₃,...])[x₂]`, this is precisely the full-rank input for equation
(24)'s Smith basis. -/
theorem finrank_localizedSecondVariable_relativeDenominator_eq
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    Module.finrank (Polynomial (FractionRing (MvPolynomial (Fin n) P)))
        (CommonTailQuotient.relativeDenominator
          (R := Polynomial (FractionRing (MvPolynomial (Fin n) P)))
          (E := localizedSecondVariableBoundedAmbient P n k)
          (localizedSecondVariableGroundModule I k)
          (localizedSecondVariableOriginalModule I k)) =
      Module.finrank (Polynomial (FractionRing (MvPolynomial (Fin n) P)))
        (localizedSecondVariableGroundModule I k) :=
  relativeDenominator_finrank_eq_of_le_nonzeroScalarSaturation
    (R := Polynomial (FractionRing (MvPolynomial (Fin n) P)))
    (E := localizedSecondVariableBoundedAmbient P n k)
    (G := localizedSecondVariableGroundModule I k)
    (M := localizedSecondVariableOriginalModule I k)
    (localizedSecondVariableGroundModule_eq_saturation I k).le

#print axioms degreeLTMapEquiv
#print axioms map_nonzeroScalarSaturation_equiv
#print axioms isGroundModule_iff_quotient_isTorsionFree
#print axioms degreeLTLocalizationMap
#print axioms degreeLTLocalizationMap_isLocalizedModule
#print axioms localized_le_nonzeroScalarSaturation_localized
#print axioms localized_eq_nonzeroScalarSaturation_localized
#print axioms lateVariableCoefficientRing
#print axioms lateVariableFractionField
#print axioms secondVariablePID
#print axioms secondVariableBoundedAmbient
#print axioms localizedSecondVariableBoundedAmbient
#print axioms secondVariableCoefficientEquiv
#print axioms secondVariableBoundedEquiv
#print axioms secondVariableBoundedCoordinateEquiv
#print axioms secondVariableGroundModule
#print axioms secondVariableOriginalModule
#print axioms secondVariableGroundModule_eq_saturation
#print axioms lateVariableDenominators
#print axioms lateVariableDenominators_le_nonZeroDivisors
#print axioms secondVariableBoundedLocalizationMap
#print axioms localizedSecondVariableGroundModule
#print axioms localizedSecondVariableOriginalModule
#print axioms localizedSecondVariableGroundModule_eq_saturation
#print axioms finrank_localizedSecondVariable_relativeDenominator_eq

end StageOneLateVariableLocalization

end

end RegularIdealDecomposition

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
