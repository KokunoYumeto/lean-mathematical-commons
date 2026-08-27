import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Hentzelt--Noether equation (23): cancelling a common independent tail

Module for P22, controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
lines 13155--13173.  The source writes
`G₁ = (G₁*, C₁)` and `M₁ = (M₁*, C₁)` and passes from `G₁ / M₁` to
`G₁* / M₁*`.  Here the comma is modeled by the supremum of submodules and
the common `C₁`-tail is assumed disjoint from the bounded numerator.

The historical divisibility notation is oriented explicitly in modern terms:
the denominator `M` is a submodule of the numerator `G`.  The result is an
instance of Noether's second isomorphism theorem for modules, already present
in Mathlib as `LinearMap.quotientInfEquivSupQuotient`; the new content here is
the source-facing common-tail specialization and its representative formula.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

namespace CommonTailQuotient

noncomputable section

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- The denominator induced on a numerator submodule.  This spelling makes
the historical quotient `G / M` type-correct even though both are submodules
of a larger ambient module. -/
abbrev relativeDenominator (G M : Submodule R E) : Submodule R G :=
  M.comap G.subtype

/-- A source-facing abbreviation for the quotient of one ambient submodule
by another.  The accompanying theorems always carry the required inclusion
`M ≤ G` explicitly. -/
abbrev relativeQuotient (G M : Submodule R E) :=
  G ⧸ relativeDenominator G M

/-- Equal ambient numerator submodules give equivalent relative quotients.
This small transport isolates the dependent subtype equality that arises when
the second isomorphism theorem simplifies `G ⊔ (M ⊔ T)` to `G ⊔ T`. -/
noncomputable def relativeQuotientEquivOfEq
    (G G' M : Submodule R E) (h : G = G') :
    relativeQuotient G M ≃ₗ[R] relativeQuotient G' M := by
  subst G'
  exact LinearEquiv.refl R _

/-- If `M ≤ G` and `G` is disjoint from a tail `T`, then the part of
`M ⊔ T` lying in `G` is exactly `M`. -/
theorem inf_sup_eq_left_of_le_of_disjoint
    (G M T : Submodule R E) (hMG : M ≤ G) (hGT : Disjoint G T) :
    G ⊓ (M ⊔ T) = M := by
  apply le_antisymm
  · intro x hx
    rcases Submodule.mem_sup.mp hx.2 with ⟨m, hm, t, ht, rfl⟩
    have htG : t ∈ G := by
      simpa only [add_sub_cancel_left] using G.sub_mem hx.1 (hMG hm)
    have ht_zero : t = 0 := (Submodule.disjoint_def.mp hGT) t htG ht
    simpa [ht_zero] using hm
  · intro x hx
    exact ⟨hMG hx, (le_sup_left : M ≤ M ⊔ T) hx⟩

/-- Adjoining the same independent tail to numerator and denominator does
not change their relative quotient.  This is the abstract linear form of the
passage following equation (23). -/
noncomputable def commonTailQuotientEquiv
    (G M T : Submodule R E) (hMG : M ≤ G) (hGT : Disjoint G T) :
    relativeQuotient (G ⊔ T) (M ⊔ T) ≃ₗ[R] relativeQuotient G M := by
  have hden :
      Submodule.comap G.subtype G ⊓
          Submodule.comap G.subtype (M ⊔ T) =
        Submodule.comap G.subtype M := by
    rw [← Submodule.comap_inf,
      inf_sup_eq_left_of_le_of_disjoint G M T hMG hGT]
  have hsup : G ⊔ (M ⊔ T) = G ⊔ T := by
    calc
      G ⊔ (M ⊔ T) = (G ⊔ M) ⊔ T := (sup_assoc G M T).symm
      _ = G ⊔ T := by rw [sup_eq_left.mpr hMG]
  exact
    (relativeQuotientEquivOfEq (G ⊔ T) (G ⊔ (M ⊔ T))
        (M ⊔ T) hsup.symm).trans
      ((LinearMap.quotientInfEquivSupQuotient G (M ⊔ T)).symm.trans
        (Submodule.quotEquivOfEq _ _ hden))

/-- Every class after adjoining the common tail is represented by a class
from `G`.  Together with `commonTailQuotientEquiv`, this is the formal
representative-system consequence stated after equation (23). -/
theorem exists_commonTail_representative
    (G M T : Submodule R E) (hMG : M ≤ G) (hGT : Disjoint G T)
    (q : relativeQuotient (G ⊔ T) (M ⊔ T)) :
    ∃ g : G,
      q = (commonTailQuotientEquiv G M T hMG hGT).symm
        (Submodule.Quotient.mk g) := by
  let e := commonTailQuotientEquiv G M T hMG hGT
  obtain ⟨g, hg⟩ := Submodule.Quotient.mk_surjective _ (e q)
  refine ⟨g, ?_⟩
  change q = e.symm (Submodule.Quotient.mk g)
  apply e.injective
  simpa only [e.apply_symm_apply] using hg.symm

#print axioms relativeDenominator
#print axioms relativeQuotient
#print axioms relativeQuotientEquivOfEq
#print axioms inf_sup_eq_left_of_le_of_disjoint
#print axioms commonTailQuotientEquiv
#print axioms exists_commonTail_representative

end

end CommonTailQuotient

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
