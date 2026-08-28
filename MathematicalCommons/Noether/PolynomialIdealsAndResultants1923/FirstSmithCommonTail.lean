import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.FirstSmithPairedQuotient
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Hentzelt--Noether equations (23)--(24): restore the common zeta tail

Module for P22, controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
lines 13155--13173.

`FirstSmithPairedQuotient` constructs the finite localized pair
`G₁*` and `M₁*` and its selected Smith vectors `eta_i`, `e_i * eta_i`.
This file models the source's independent `zeta` tail by freely adjoining it
to the actual finite localized pair.  For an arbitrary tail index type `tau`,
the ambient module is the direct product of the actual localized ground module
with the finitely supported free module `tau ->₀ R`.
The finite pair is embedded in the first summand and the tail in the second.
Consequently

* the full ground and original modules are their finite parts joined with
  the same tail;
* the finite ground part is disjoint from the tail;
* adjoining that tail does not change the relative quotient; and
* the extended diagonal coefficients are the selected finite `e_i` and `1`
  on every tail coordinate.

The specialization `tau = Nat` models the source's countable sequence
`zeta₀, zeta₁, ...`.  All vectors in `tau ->₀ R` have finite support;
no infinite determinant or infinite product is formed.  This module also does
not assert divisibility ordering, normalization, or uniqueness of the selected
Smith coefficients: Mathlib v4.31's Smith API does not provide those claims.
The coefficient `1` on each tail coordinate is part of this shared-identity-
tail model.  A separate construction and localization of the historical
unbounded `zeta` module, and an identification of it with this free tail, have
not yet been supplied.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open Module MvPolynomial

namespace RegularIdealDecomposition

noncomputable section

namespace ProductHeadQuotient

variable {R E F : Type*}
variable [Ring R] [AddCommGroup E] [Module R E]
variable [AddCommGroup F] [Module R F]

/-- The first projection identifies the copy `E x {0}` inside `E x F`
with `E`.  Keeping this transport generic prevents source-specific localized
module definitions from being unfolded throughout the quotient proof. -/
noncomputable def headEquiv :
    ((⊤ : Submodule R E).prod (⊥ : Submodule R F)) ≃ₗ[R] E where
  toFun x := x.1.1
  invFun x := ⟨(x, 0), by simp⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hx0 : x.1.2 = 0 := by simpa using x.property.2
      exact hx0.symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Adjoining a zero second coordinate to both numerator and denominator
does not change the quotient.  Naming the ambient submodules in the endpoint
keeps source-specific localization towers opaque during instantiation. -/
noncomputable def relativeQuotientEquiv (G M : Submodule R E) :
    CommonTailQuotient.relativeQuotient
        ((⊤ : Submodule R G).prod (⊥ : Submodule R F))
        ((CommonTailQuotient.relativeDenominator G M).prod
          (⊥ : Submodule R F)) ≃ₗ[R]
      CommonTailQuotient.relativeQuotient G M := by
  apply Submodule.Quotient.equiv
    (CommonTailQuotient.relativeDenominator
      ((⊤ : Submodule R G).prod (⊥ : Submodule R F))
      ((CommonTailQuotient.relativeDenominator G M).prod
        (⊥ : Submodule R F)))
    (CommonTailQuotient.relativeDenominator G M)
    (headEquiv (R := R) (E := G) (F := F))
  ext y
  simp only [Submodule.mem_map_equiv]
  change ((((headEquiv (R := R) (E := G) (F := F)).symm y :
      ((⊤ : Submodule R G).prod (⊥ : Submodule R F))) : G × F) ∈
        (CommonTailQuotient.relativeDenominator G M).prod
          (⊥ : Submodule R F)) ↔
      y ∈ CommonTailQuotient.relativeDenominator G M
  simp [headEquiv]

/-- Cancelling the identity tail and forgetting its zero coordinate are
composed generically, before any source-specific polynomial tower is
instantiated. -/
noncomputable def commonTailRelativeQuotientEquiv (G M : Submodule R E) :
    CommonTailQuotient.relativeQuotient
        (((⊤ : Submodule R G).prod (⊥ : Submodule R F)) ⊔
          ((⊥ : Submodule R G).prod (⊤ : Submodule R F)))
        (((CommonTailQuotient.relativeDenominator G M).prod
            (⊥ : Submodule R F)) ⊔
          ((⊥ : Submodule R G).prod (⊤ : Submodule R F))) ≃ₗ[R]
      CommonTailQuotient.relativeQuotient G M :=
  (CommonTailQuotient.commonTailQuotientEquiv
      (R := R) (E := G × F)
      ((⊤ : Submodule R G).prod (⊥ : Submodule R F))
      ((CommonTailQuotient.relativeDenominator G M).prod
        (⊥ : Submodule R F))
      ((⊥ : Submodule R G).prod (⊤ : Submodule R F))
      (Submodule.prod_mono le_top le_rfl)
      (by
        rw [disjoint_iff_inf_le, Submodule.prod_inf_prod]
        simp)).trans
    (relativeQuotientEquiv (R := R) (E := E) (F := F) G M)

/-- Every class after adjoining the identity tail is represented by an
element of the finite first factor. -/
theorem exists_commonTail_representative
    (G M : Submodule R E)
    (q : CommonTailQuotient.relativeQuotient
      (((⊤ : Submodule R G).prod (⊥ : Submodule R F)) ⊔
        ((⊥ : Submodule R G).prod (⊤ : Submodule R F)))
      (((CommonTailQuotient.relativeDenominator G M).prod
          (⊥ : Submodule R F)) ⊔
        ((⊥ : Submodule R G).prod (⊤ : Submodule R F)))) :
    ∃ g : G,
      commonTailRelativeQuotientEquiv (R := R) (E := E) (F := F) G M q =
        Submodule.Quotient.mk g := by
  obtain ⟨g, hg⟩ := Submodule.Quotient.mk_surjective _
    (commonTailRelativeQuotientEquiv (R := R) (E := E) (F := F) G M q)
  exact ⟨g, hg.symm⟩

end ProductHeadQuotient

variable {P : Type*} [Field P]
variable {n : ℕ}

/-- The actual finite localized numerator carrier `G₁*`. -/
abbrev localizedSecondVariableGroundCarrier
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :=
  localizedSecondVariableGroundModule I k

/-- The actual relative-denominator carrier `M₁*`, as a submodule of
`G₁*`. -/
abbrev localizedSecondVariableDenominatorCarrier
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :=
  CommonTailQuotient.relativeDenominator
    (R := secondVariablePID P n)
    (E := localizedSecondVariableBoundedAmbient P n k)
    (localizedSecondVariableGroundModule I k)
    (localizedSecondVariableOriginalModule I k)

/-- The enlarged coordinate ambient `G₁* x (tau ->₀ R)`. -/
abbrev localizedSecondVariableCommonTailAmbient
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :=
  localizedSecondVariableGroundCarrier I k ×
    (tau →₀ secondVariablePID P n)

/-- The basis vectors of the independent `zeta` tail. -/
noncomputable def localizedSecondVariableTailBasis (tau : Type*) :
    Basis tau (secondVariablePID P n)
      (tau →₀ secondVariablePID P n) :=
  Finsupp.basisSingleOne

/-- The finite numerator `G₁*`, embedded in the enlarged ambient. -/
def localizedSecondVariableFiniteGroundPart
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :
    Submodule (secondVariablePID P n)
      (localizedSecondVariableCommonTailAmbient I k tau) :=
  (⊤ : Submodule (secondVariablePID P n)
      (localizedSecondVariableGroundCarrier I k)).prod ⊥

/-- The finite denominator `M₁*`, embedded in the enlarged ambient. -/
def localizedSecondVariableFiniteOriginalPart
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :
    Submodule (secondVariablePID P n)
      (localizedSecondVariableCommonTailAmbient I k tau) :=
  (localizedSecondVariableDenominatorCarrier I k).prod ⊥

/-- The common independent tail `C₁`, embedded in the second summand. -/
def localizedSecondVariableCommonTail
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :
    Submodule (secondVariablePID P n)
      (localizedSecondVariableCommonTailAmbient I k tau) :=
  (⊥ : Submodule (secondVariablePID P n)
      (localizedSecondVariableGroundCarrier I k)).prod ⊤

/-- Source equation (23), numerator side: `G₁ = (G₁*, C₁)`. -/
def localizedSecondVariableFullGroundModule
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :
    Submodule (secondVariablePID P n)
      (localizedSecondVariableCommonTailAmbient I k tau) :=
  localizedSecondVariableFiniteGroundPart I k tau ⊔
    localizedSecondVariableCommonTail I k tau

/-- Source equation (23), denominator side: `M₁ = (M₁*, C₁)`. -/
def localizedSecondVariableFullOriginalModule
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :
    Submodule (secondVariablePID P n)
      (localizedSecondVariableCommonTailAmbient I k tau) :=
  localizedSecondVariableFiniteOriginalPart I k tau ⊔
    localizedSecondVariableCommonTail I k tau

/-- The embedded finite denominator lies in the embedded finite numerator. -/
theorem localizedSecondVariableFiniteOriginalPart_le_ground
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :
    localizedSecondVariableFiniteOriginalPart I k tau ≤
      localizedSecondVariableFiniteGroundPart I k tau :=
  Submodule.prod_mono le_top le_rfl

/-- The finite `eta` coordinates and the independent `zeta` coordinates have
zero intersection. -/
theorem localizedSecondVariableFiniteGroundPart_disjoint_tail
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :
    Disjoint (localizedSecondVariableFiniteGroundPart I k tau)
      (localizedSecondVariableCommonTail I k tau) := by
  rw [disjoint_iff_inf_le, localizedSecondVariableFiniteGroundPart,
    localizedSecondVariableCommonTail, Submodule.prod_inf_prod]
  simp

/-- The restored full numerator is the whole enlarged coordinate ambient. -/
@[simp]
theorem localizedSecondVariableFullGroundModule_eq_top
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :
    localizedSecondVariableFullGroundModule I k tau = ⊤ := by
  simp [localizedSecondVariableFullGroundModule,
    localizedSecondVariableFiniteGroundPart,
    localizedSecondVariableCommonTail, Submodule.prod_sup_prod]

/-- The restored full denominator is `M₁* x (tau ->₀ R)`. -/
@[simp]
theorem localizedSecondVariableFullOriginalModule_eq_prod_top
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :
    localizedSecondVariableFullOriginalModule I k tau =
      (localizedSecondVariableDenominatorCarrier I k).prod ⊤ := by
  simp [localizedSecondVariableFullOriginalModule,
    localizedSecondVariableFiniteOriginalPart,
    localizedSecondVariableCommonTail, Submodule.prod_sup_prod]

/-- The finite Smith numerator basis extended by the standard tail basis. -/
noncomputable def localizedSecondVariableExtendedEtaBasis
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :
    Basis (localizedSecondVariableSmithIndex I k ⊕ tau)
      (secondVariablePID P n)
      (localizedSecondVariableCommonTailAmbient I k tau) :=
  (localizedSecondVariableEtaBasis I k).prod
    (localizedSecondVariableTailBasis (P := P) (n := n) tau)

/-- The finite Smith denominator basis extended by the same standard tail
basis.  Its module is canonically `M₁* x (tau ->₀ R)`, identified above
with the full denominator. -/
noncomputable def localizedSecondVariableExtendedDenominatorBasis
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :
    Basis (localizedSecondVariableSmithIndex I k ⊕ tau)
      (secondVariablePID P n)
      (localizedSecondVariableDenominatorCarrier I k ×
        (tau →₀ secondVariablePID P n)) :=
  (localizedSecondVariableDenominatorBasis I k).prod
    (localizedSecondVariableTailBasis (P := P) (n := n) tau)

/-- Include the extended denominator carrier in the enlarged numerator
ambient. -/
def localizedSecondVariableExtendedDenominatorInclusion
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :
    (localizedSecondVariableDenominatorCarrier I k ×
        (tau →₀ secondVariablePID P n)) →ₗ[secondVariablePID P n]
      localizedSecondVariableCommonTailAmbient I k tau :=
  LinearMap.prodMap
    (localizedSecondVariableDenominatorCarrier I k).subtype LinearMap.id

/-- The source's diagonal coefficients after the common tail is restored:
the selected finite `e_i`, followed by units on every tail coordinate. -/
def localizedSecondVariableExtendedSmithCoefficients
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :
    localizedSecondVariableSmithIndex I k ⊕ tau →
      secondVariablePID P n
  | Sum.inl i => localizedSecondVariableSmithCoefficients I k i
  | Sum.inr _ => 1

@[simp]
theorem localizedSecondVariableExtendedSmithCoefficients_inl
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*)
    (i : localizedSecondVariableSmithIndex I k) :
    localizedSecondVariableExtendedSmithCoefficients I k tau (Sum.inl i) =
      localizedSecondVariableSmithCoefficients I k i := rfl

@[simp]
theorem localizedSecondVariableExtendedSmithCoefficients_inr
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*)
    (j : tau) :
    localizedSecondVariableExtendedSmithCoefficients I k tau (Sum.inr j) =
      1 := rfl

/-- Every extended coefficient is nonzero: this is the finite Smith
nonvanishing theorem on the left summand and `one_ne_zero` on the tail. -/
theorem localizedSecondVariableExtendedSmithCoefficients_ne_zero
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*)
    (j : localizedSecondVariableSmithIndex I k ⊕ tau) :
    localizedSecondVariableExtendedSmithCoefficients I k tau j ≠ 0 := by
  cases j with
  | inl i =>
      exact localizedSecondVariableSmithCoefficients_ne_zero I k i
  | inr _ =>
      exact one_ne_zero

/-- Equation (24) after restoring the tail: finite denominator vectors are
`e_i * eta_i`, while every common-tail vector is `1 * zeta_j`. -/
@[simp]
theorem localizedSecondVariableExtendedDenominatorBasis_eq_smul_eta
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*)
    (j : localizedSecondVariableSmithIndex I k ⊕ tau) :
    localizedSecondVariableExtendedDenominatorInclusion I k tau
        (localizedSecondVariableExtendedDenominatorBasis I k tau j) =
      localizedSecondVariableExtendedSmithCoefficients I k tau j •
        localizedSecondVariableExtendedEtaBasis I k tau j := by
  cases j with
  | inl i =>
      apply Prod.ext
      · simp [localizedSecondVariableExtendedDenominatorInclusion,
          localizedSecondVariableExtendedDenominatorBasis,
          localizedSecondVariableExtendedEtaBasis,
          localizedSecondVariableDenominatorBasis_eq_smul_eta]
      · simp [localizedSecondVariableExtendedDenominatorInclusion,
          localizedSecondVariableExtendedDenominatorBasis,
          localizedSecondVariableExtendedEtaBasis]
  | inr j =>
      simp [localizedSecondVariableExtendedDenominatorInclusion,
        localizedSecondVariableExtendedDenominatorBasis,
        localizedSecondVariableExtendedEtaBasis,
        localizedSecondVariableTailBasis]

/-- Every vector of the extended denominator basis lies in the restored full
original module. -/
theorem localizedSecondVariableExtendedDenominatorBasis_mem_fullOriginal
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*)
    (j : localizedSecondVariableSmithIndex I k ⊕ tau) :
    localizedSecondVariableExtendedDenominatorInclusion I k tau
        (localizedSecondVariableExtendedDenominatorBasis I k tau j) ∈
      localizedSecondVariableFullOriginalModule I k tau := by
  rw [localizedSecondVariableFullOriginalModule_eq_prod_top]
  cases j with
  | inl i =>
      simpa [localizedSecondVariableExtendedDenominatorInclusion,
        localizedSecondVariableExtendedDenominatorBasis,
        localizedSecondVariableTailBasis] using
        localizedSecondVariable_smul_eta_mem_original I k i
  | inr j =>
      simp [localizedSecondVariableExtendedDenominatorInclusion,
        localizedSecondVariableExtendedDenominatorBasis,
        localizedSecondVariableTailBasis]

/-- Forget the zero tail coordinate in the embedded finite numerator. -/
noncomputable def localizedSecondVariableFiniteGroundEquiv
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :
    localizedSecondVariableFiniteGroundPart I k tau ≃ₗ[
      secondVariablePID P n] localizedSecondVariableGroundCarrier I k :=
  ProductHeadQuotient.headEquiv
    (R := secondVariablePID P n)
    (E := localizedSecondVariableGroundCarrier I k)
    (F := tau →₀ secondVariablePID P n)

/-- The embedded finite quotient is canonically the actual localized
`G₁* / M₁*` quotient from `FirstSmithPairedQuotient`. -/
noncomputable def localizedSecondVariableFiniteQuotientEquiv
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :
    CommonTailQuotient.relativeQuotient
        (R := secondVariablePID P n)
        (E := localizedSecondVariableCommonTailAmbient I k tau)
        (localizedSecondVariableFiniteGroundPart I k tau)
        (localizedSecondVariableFiniteOriginalPart I k tau) ≃ₗ[
      secondVariablePID P n]
      CommonTailQuotient.relativeQuotient
        (R := secondVariablePID P n)
        (E := localizedSecondVariableBoundedAmbient P n k)
        (localizedSecondVariableGroundModule I k)
        (localizedSecondVariableOriginalModule I k) :=
  ProductHeadQuotient.relativeQuotientEquiv
    (R := secondVariablePID P n)
    (E := localizedSecondVariableBoundedAmbient P n k)
    (F := tau →₀ secondVariablePID P n)
    (localizedSecondVariableGroundModule I k)
    (localizedSecondVariableOriginalModule I k)

/-- Equations (23)--(24), source-instantiated: cancel the restored common tail
and recover the actual finite localized relative quotient. -/
noncomputable def localizedSecondVariableCommonTailQuotientEquiv
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :
    CommonTailQuotient.relativeQuotient
        (R := secondVariablePID P n)
        (E := localizedSecondVariableCommonTailAmbient I k tau)
        (localizedSecondVariableFullGroundModule I k tau)
        (localizedSecondVariableFullOriginalModule I k tau) ≃ₗ[
      secondVariablePID P n]
      CommonTailQuotient.relativeQuotient
        (R := secondVariablePID P n)
        (E := localizedSecondVariableBoundedAmbient P n k)
        (localizedSecondVariableGroundModule I k)
        (localizedSecondVariableOriginalModule I k) :=
  ProductHeadQuotient.commonTailRelativeQuotientEquiv
    (R := secondVariablePID P n)
    (E := localizedSecondVariableBoundedAmbient P n k)
    (F := tau →₀ secondVariablePID P n)
    (localizedSecondVariableGroundModule I k)
    (localizedSecondVariableOriginalModule I k)

/-- Cancel the restored common tail and then apply the actual finite Smith
decomposition.  Thus the full source-shaped quotient has exactly the same
finite cyclic factors as `G₁* / M₁*`; no factor is attached to a tail
coordinate because its diagonal coefficient is the unit `1`. -/
noncomputable def localizedSecondVariableCommonTailQuotientEquivSmithCyclic
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :
    CommonTailQuotient.relativeQuotient
        (R := secondVariablePID P n)
        (E := localizedSecondVariableCommonTailAmbient I k tau)
        (localizedSecondVariableFullGroundModule I k tau)
        (localizedSecondVariableFullOriginalModule I k tau) ≃ₗ[
      secondVariablePID P n]
      (∀ i : localizedSecondVariableSmithIndex I k,
        secondVariablePID P n ⧸
          Ideal.span
            ({localizedSecondVariableSmithCoefficients I k i} :
              Set (secondVariablePID P n))) :=
  (localizedSecondVariableCommonTailQuotientEquiv I k tau).trans
    (localizedSecondVariableRelativeQuotientEquivSmithCyclic I k)

/-- Every class in the restored full quotient has a representative in the
actual finite localized ground module. -/
noncomputable def exists_localizedSecondVariableCommonTail_representative
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :=
  ProductHeadQuotient.exists_commonTail_representative
    (R := secondVariablePID P n)
    (E := localizedSecondVariableBoundedAmbient P n k)
    (F := tau →₀ secondVariablePID P n)
    (localizedSecondVariableGroundModule I k)
    (localizedSecondVariableOriginalModule I k)

/-- Countable source specialization for `zeta₀, zeta₁, ...`. -/
abbrev localizedSecondVariableNatTailAmbient
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :=
  localizedSecondVariableCommonTailAmbient I k ℕ

/-- The extended numerator basis for the countable `zeta` tail. -/
noncomputable def localizedSecondVariableNatTailEtaBasis
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    Basis (localizedSecondVariableSmithIndex I k ⊕ ℕ)
      (secondVariablePID P n)
      (localizedSecondVariableNatTailAmbient I k) :=
  localizedSecondVariableExtendedEtaBasis I k ℕ

/-- The extended denominator basis for the countable `zeta` tail. -/
noncomputable def localizedSecondVariableNatTailDenominatorBasis
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    Basis (localizedSecondVariableSmithIndex I k ⊕ ℕ)
      (secondVariablePID P n)
      (localizedSecondVariableDenominatorCarrier I k ×
        (ℕ →₀ secondVariablePID P n)) :=
  localizedSecondVariableExtendedDenominatorBasis I k ℕ

/-- Every countable tail coordinate has diagonal coefficient `1`. -/
@[simp]
theorem localizedSecondVariableNatTailCoefficient_eq_one
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k j : ℕ) :
    localizedSecondVariableExtendedSmithCoefficients I k ℕ (Sum.inr j) =
      1 := rfl

/-- Countable-tail form of the source-instantiated quotient cancellation. -/
noncomputable def localizedSecondVariableNatTailQuotientEquiv
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    CommonTailQuotient.relativeQuotient
        (R := secondVariablePID P n)
        (E := localizedSecondVariableCommonTailAmbient I k ℕ)
        (localizedSecondVariableFullGroundModule I k ℕ)
        (localizedSecondVariableFullOriginalModule I k ℕ) ≃ₗ[
      secondVariablePID P n]
      CommonTailQuotient.relativeQuotient
        (R := secondVariablePID P n)
        (E := localizedSecondVariableBoundedAmbient P n k)
        (localizedSecondVariableGroundModule I k)
        (localizedSecondVariableOriginalModule I k) :=
  localizedSecondVariableCommonTailQuotientEquiv I k ℕ

/-- Countable-tail form of the full quotient's finite Smith cyclic
decomposition. -/
noncomputable def localizedSecondVariableNatTailQuotientEquivSmithCyclic
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    CommonTailQuotient.relativeQuotient
        (R := secondVariablePID P n)
        (E := localizedSecondVariableCommonTailAmbient I k ℕ)
        (localizedSecondVariableFullGroundModule I k ℕ)
        (localizedSecondVariableFullOriginalModule I k ℕ) ≃ₗ[
      secondVariablePID P n]
      (∀ i : localizedSecondVariableSmithIndex I k,
        secondVariablePID P n ⧸
          Ideal.span
            ({localizedSecondVariableSmithCoefficients I k i} :
              Set (secondVariablePID P n))) :=
  localizedSecondVariableCommonTailQuotientEquivSmithCyclic I k ℕ

#print axioms ProductHeadQuotient.headEquiv
#print axioms ProductHeadQuotient.relativeQuotientEquiv
#print axioms ProductHeadQuotient.commonTailRelativeQuotientEquiv
#print axioms ProductHeadQuotient.exists_commonTail_representative
#print axioms localizedSecondVariableGroundCarrier
#print axioms localizedSecondVariableDenominatorCarrier
#print axioms localizedSecondVariableCommonTailAmbient
#print axioms localizedSecondVariableTailBasis
#print axioms localizedSecondVariableFiniteGroundPart
#print axioms localizedSecondVariableFiniteOriginalPart
#print axioms localizedSecondVariableCommonTail
#print axioms localizedSecondVariableFullGroundModule
#print axioms localizedSecondVariableFullOriginalModule
#print axioms localizedSecondVariableFiniteOriginalPart_le_ground
#print axioms localizedSecondVariableFiniteGroundPart_disjoint_tail
#print axioms localizedSecondVariableFullGroundModule_eq_top
#print axioms localizedSecondVariableFullOriginalModule_eq_prod_top
#print axioms localizedSecondVariableExtendedEtaBasis
#print axioms localizedSecondVariableExtendedDenominatorBasis
#print axioms localizedSecondVariableExtendedDenominatorInclusion
#print axioms localizedSecondVariableExtendedSmithCoefficients
#print axioms localizedSecondVariableExtendedSmithCoefficients_inl
#print axioms localizedSecondVariableExtendedSmithCoefficients_inr
#print axioms localizedSecondVariableExtendedSmithCoefficients_ne_zero
#print axioms localizedSecondVariableExtendedDenominatorBasis_eq_smul_eta
#print axioms localizedSecondVariableExtendedDenominatorBasis_mem_fullOriginal
#print axioms localizedSecondVariableFiniteGroundEquiv
#print axioms localizedSecondVariableFiniteQuotientEquiv
#print axioms localizedSecondVariableCommonTailQuotientEquiv
#print axioms localizedSecondVariableCommonTailQuotientEquivSmithCyclic
#print axioms exists_localizedSecondVariableCommonTail_representative
#print axioms localizedSecondVariableNatTailAmbient
#print axioms localizedSecondVariableNatTailEtaBasis
#print axioms localizedSecondVariableNatTailDenominatorBasis
#print axioms localizedSecondVariableNatTailCoefficient_eq_one
#print axioms localizedSecondVariableNatTailQuotientEquiv
#print axioms localizedSecondVariableNatTailQuotientEquivSmithCyclic

end

end RegularIdealDecomposition

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
