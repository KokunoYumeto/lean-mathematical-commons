import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.FirstGroundModule
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Hentzelt--Noether line 13162: torsion and full-rank consequences

Module for P22, controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
Definition I and Satz I at lines 12752--12795 and the application at lines
13162--13173.

`FirstGroundModule` proves the source's exact assertion
`G₁* = saturation(M₁*)`.  This file records its next two basis-independent
consequences.  The relative quotient `G₁* / M₁*` is torsion over the ring in
the remaining variables, and therefore the relative denominator has the same
finite rank as `G₁*`.  This supplies the full-rank premise used by the later
Smith-form packaging, before the separate localization step that changes the
coefficient ring to a principal ideal domain.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open MvPolynomial

namespace RegularIdealDecomposition

noncomputable section

section AbstractGroundQuotient

variable {R E : Type*} [CommRing R] [IsDomain R]
variable [AddCommGroup E] [Module R E]

/-- A module modulo any submodule whose saturation is the whole module is a
torsion module. -/
theorem relativeQuotient_isTorsion_of_le_nonzeroScalarSaturation
    {G M : Submodule R E} (hG : G ≤ nonzeroScalarSaturation M) :
    Module.IsTorsion R (CommonTailQuotient.relativeQuotient G M) := by
  intro q
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective
    (CommonTailQuotient.relativeDenominator G M) q
  obtain ⟨b, hb, hbg⟩ :=
    (mem_nonzeroScalarSaturation_iff M (g : E)).mp (hG g.property)
  refine ⟨⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩, ?_⟩
  rw [← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero]
  change b • (g : E) ∈ M
  exact hbg

/-- Conversely, torsion of the relative quotient says exactly that every
numerator element has a nonzero multiple in the denominator. -/
theorem le_nonzeroScalarSaturation_of_relativeQuotient_isTorsion
    {G M : Submodule R E}
    (h : Module.IsTorsion R
      (CommonTailQuotient.relativeQuotient G M)) :
    G ≤ nonzeroScalarSaturation M := by
  intro x hx
  let g : G := ⟨x, hx⟩
  obtain ⟨b, hb⟩ := h (x :=
    (Submodule.Quotient.mk g :
      CommonTailQuotient.relativeQuotient G M))
  refine ⟨(b : R), mem_nonZeroDivisors_iff_ne_zero.mp b.property, ?_⟩
  have hb' :
      (Submodule.Quotient.mk (b • g) :
        CommonTailQuotient.relativeQuotient G M) = 0 := by
    rw [Submodule.Quotient.mk_smul]
    exact hb
  have hden :=
    (Submodule.Quotient.mk_eq_zero
      (p := CommonTailQuotient.relativeDenominator G M)
      (x := b • g)).mp hb'
  change (b : R) • (g : E) ∈ M at hden
  simpa [g] using hden

/-- Torsion of `G / M` is equivalent to formula-(4) saturation of every
element of `G`. -/
theorem relativeQuotient_isTorsion_iff_le_nonzeroScalarSaturation
    {G M : Submodule R E} :
    Module.IsTorsion R (CommonTailQuotient.relativeQuotient G M) ↔
      G ≤ nonzeroScalarSaturation M :=
  ⟨le_nonzeroScalarSaturation_of_relativeQuotient_isTorsion,
    relativeQuotient_isTorsion_of_le_nonzeroScalarSaturation⟩

/-- Cardinal rank zero over a domain is equivalent to torsion.  This is the
nonzero-scalar witness form specialized to Mathlib's `R⁰` definition. -/
theorem rank_eq_zero_iff_isTorsion_nonzeroScalar :
    Module.rank R E = 0 ↔ Module.IsTorsion R E := by
  rw [Module.IsTorsion, rank_eq_zero_iff]
  simp [mem_nonZeroDivisors_iff_ne_zero]

/-- Saturation forces the relative denominator to have the same cardinal rank
as the numerator; no finite-generation hypothesis is needed. -/
theorem relativeDenominator_rank_eq_of_le_nonzeroScalarSaturation
    {G M : Submodule R E} (hG : G ≤ nonzeroScalarSaturation M) :
    Module.rank R (CommonTailQuotient.relativeDenominator G M) =
      Module.rank R G := by
  have hquotient :
      Module.rank R (CommonTailQuotient.relativeQuotient G M) = 0 :=
    (rank_eq_zero_iff_isTorsion_nonzeroScalar (R := R)).2
      (relativeQuotient_isTorsion_of_le_nonzeroScalarSaturation hG)
  have hdimension :=
    (CommonTailQuotient.relativeDenominator G M).rank_quotient_add_rank
  rw [hquotient, zero_add] at hdimension
  exact hdimension

/-- Taking cardinal `toNat` gives exactly the `finrank` equality required by
Mathlib's Smith-normal-form API. -/
theorem relativeDenominator_finrank_eq_of_le_nonzeroScalarSaturation
    {G M : Submodule R E} (hG : G ≤ nonzeroScalarSaturation M) :
    Module.finrank R (CommonTailQuotient.relativeDenominator G M) =
      Module.finrank R G :=
  congrArg Cardinal.toNat
    (relativeDenominator_rank_eq_of_le_nonzeroScalarSaturation hG)

/-- Satz I's "same rank" conclusion: passing to formula-(4) saturation does
not change cardinal module rank. -/
theorem nonzeroScalarSaturation_rank_eq (M : Submodule R E) :
    Module.rank R (nonzeroScalarSaturation M) = Module.rank R M := by
  have hden :=
    relativeDenominator_rank_eq_of_le_nonzeroScalarSaturation
      (G := nonzeroScalarSaturation M) (M := M) le_rfl
  have he :=
    (Submodule.comapSubtypeEquivOfLe
      (le_nonzeroScalarSaturation M)).rank_eq
  exact hden.symm.trans he

end AbstractGroundQuotient

variable {P : Type*} [Field P]
variable {n : ℕ}

/-- Every degree-bounded transported ideal module is finite over the
late-variable coefficient ring. -/
theorem boundedPartInDegreeLT_moduleFinite
    (I : Ideal (Polynomial (MvPolynomial (Fin n) P))) (k : ℕ) :
    Module.Finite (MvPolynomial (Fin n) P)
      (boundedPartInDegreeLT I k) := by
  letI : IsNoetherian (MvPolynomial (Fin n) P)
      (Polynomial.degreeLT (MvPolynomial (Fin n) P) k) :=
    isNoetherian_of_linearEquiv
      (Polynomial.degreeLTEquiv (MvPolynomial (Fin n) P) k).symm
  exact Module.Finite.of_injective
    (boundedPartInDegreeLT I k).subtype
    (boundedPartInDegreeLT I k).subtype_injective

/-- Line 13162 makes the bounded relative quotient `G₁* / M₁*` torsion
over the unlocalized remaining-variable polynomial ring. -/
theorem stageOneGround_boundedRelativeQuotient_isTorsion
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    Module.IsTorsion (MvPolynomial (Fin (n + 1)) P)
      (CommonTailQuotient.relativeQuotient
        (R := MvPolynomial (Fin (n + 1)) P)
        (E := Polynomial.degreeLT (MvPolynomial (Fin (n + 1)) P) k)
        (boundedPartInDegreeLT (stageOneGroundIdeal I) k)
        (boundedPartInDegreeLT (finSuccIdeal (n := n + 1) I) k)) :=
  relativeQuotient_isTorsion_of_le_nonzeroScalarSaturation
    (boundedPartInDegreeLT_stageOneGroundIdeal_eq_saturation I k).le

set_option maxHeartbeats 400000

/-- The source's ground-module characterization supplies the full-rank premise
needed for the later Smith diagonalization after localization. -/
theorem finrank_stageOneGround_relativeDenominator_eq
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    Module.finrank (MvPolynomial (Fin (n + 1)) P)
        (CommonTailQuotient.relativeDenominator
          (R := MvPolynomial (Fin (n + 1)) P)
          (E := Polynomial.degreeLT (MvPolynomial (Fin (n + 1)) P) k)
          (boundedPartInDegreeLT (stageOneGroundIdeal I) k)
          (boundedPartInDegreeLT (finSuccIdeal (n := n + 1) I) k)) =
      Module.finrank (MvPolynomial (Fin (n + 1)) P)
        (boundedPartInDegreeLT (stageOneGroundIdeal I) k) :=
  relativeDenominator_finrank_eq_of_le_nonzeroScalarSaturation
    (R := MvPolynomial (Fin (n + 1)) P)
    (E := Polynomial.degreeLT (MvPolynomial (Fin (n + 1)) P) k)
    (G := boundedPartInDegreeLT (stageOneGroundIdeal I) k)
    (M := boundedPartInDegreeLT (finSuccIdeal (n := n + 1) I) k)
    (boundedPartInDegreeLT_stageOneGroundIdeal_eq_saturation I k).le

set_option maxHeartbeats 200000

#print axioms relativeQuotient_isTorsion_of_le_nonzeroScalarSaturation
#print axioms le_nonzeroScalarSaturation_of_relativeQuotient_isTorsion
#print axioms relativeQuotient_isTorsion_iff_le_nonzeroScalarSaturation
#print axioms rank_eq_zero_iff_isTorsion_nonzeroScalar
#print axioms relativeDenominator_rank_eq_of_le_nonzeroScalarSaturation
#print axioms relativeDenominator_finrank_eq_of_le_nonzeroScalarSaturation
#print axioms nonzeroScalarSaturation_rank_eq
#print axioms boundedPartInDegreeLT_moduleFinite
#print axioms stageOneGround_boundedRelativeQuotient_isTorsion
#print axioms finrank_stageOneGround_relativeDenominator_eq

end

end RegularIdealDecomposition

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
