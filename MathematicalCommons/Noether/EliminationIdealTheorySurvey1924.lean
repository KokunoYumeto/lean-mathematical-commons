import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Generic zeros in Noether's 1924 elimination-theory survey

This is the source-shaped generic-zero construction at line 14187 of the
controlled witness `NOETH-DE-AUTH-v052-20260815`. It proves the vanishing
kernel and field-generation claims. It deliberately does not assert the
printed strict transcendence-degree bound; instead it proves the valid
non-strict upper bound, allowing equality for the zero prime ideal.
-/

noncomputable section

namespace MathematicalCommons.Noether.EliminationIdealTheorySurvey1924

open scoped IntermediateField.algebraAdjoinAdjoin

variable {P σ : Type*} [Field P]

/-- The coordinate ring of a prime ideal. -/
abbrev CoordinateRing (I : Ideal (MvPolynomial σ P)) := (MvPolynomial σ P) ⧸ I

/-- The fraction field of the coordinate ring. -/
abbrev GenericZeroField (I : Ideal (MvPolynomial σ P)) := FractionRing (CoordinateRing I)

/-- The generic zero: the coordinate classes embedded in the fraction field
of the coordinate ring. -/
def genericZero (I : Ideal (MvPolynomial σ P)) [I.IsPrime] (i : σ) : GenericZeroField I :=
  algebraMap (CoordinateRing I) (GenericZeroField I)
    (Ideal.Quotient.mk I (MvPolynomial.X i))

/-- Evaluation at the generic zero is the quotient map followed by the
fraction-field embedding. -/
theorem aeval_genericZero_eq_algebraMap_mk
    (I : Ideal (MvPolynomial σ P)) [I.IsPrime] (f : MvPolynomial σ P) :
    MvPolynomial.aeval (genericZero I) f =
      algebraMap (CoordinateRing I) (GenericZeroField I) (Ideal.Quotient.mk I f) := by
  let q : MvPolynomial σ P →ₐ[P] CoordinateRing I := Ideal.Quotient.mkₐ P I
  let j : CoordinateRing I →ₐ[P] GenericZeroField I :=
    IsScalarTower.toAlgHom P (CoordinateRing I) (GenericZeroField I)
  have h_eval : MvPolynomial.aeval (genericZero I) = j.comp q := by
    ext i
    simp [genericZero, q, j]
  simp only [h_eval, AlgHom.comp_apply, q, j, IsScalarTower.toAlgHom_apply,
    Ideal.Quotient.mkₐ_eq_mk]

/-- The fraction field of a prime coordinate ring is generated, as a field
over the coefficient field, by its generic coordinate classes. This is the
formal content of Noether's `R = P(α₁, ..., αₙ)` at line 14187. -/
theorem intermediateField_adjoin_range_genericZero_eq_top
    (I : Ideal (MvPolynomial σ P)) [I.IsPrime] :
    IntermediateField.adjoin P (Set.range (genericZero I)) = ⊤ := by
  let F : IntermediateField P (GenericZeroField I) :=
    IntermediateField.adjoin P (Set.range (genericZero I))
  have hcoord (i : σ) : genericZero I i ∈ F :=
    IntermediateField.subset_adjoin P _ (Set.mem_range_self i)
  have heval (f : MvPolynomial σ P) : MvPolynomial.aeval (genericZero I) f ∈ F := by
    rw [MvPolynomial.aeval_def]
    apply MvPolynomial.eval₂_mem
    · intro n hn
      exact F.algebraMap_mem _
    · exact fun i ↦ hcoord i
  have hquotient (x : CoordinateRing I) :
      algebraMap (CoordinateRing I) (GenericZeroField I) x ∈ F := by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← aeval_genericZero_eq_algebraMap_mk]
    exact heval f
  change F = ⊤
  apply top_unique
  intro z hz
  obtain ⟨x, y, hy, hxy⟩ :=
    IsFractionRing.div_surjective (CoordinateRing I) z
  rw [← hxy]
  exact F.div_mem (hquotient x) (hquotient y)

private theorem isAlgebraic_algebraAdjoin_of_intermediateField_adjoin_eq_top
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (S : Set E) (hS : IntermediateField.adjoin F S = ⊤) :
    Algebra.IsAlgebraic (Algebra.adjoin F S) E := by
  refine ⟨fun x ↦ ?_⟩
  let y : IntermediateField.adjoin F S := ⟨x, by simpa [hS]⟩
  have hy : IsAlgebraic (Algebra.adjoin F S) y :=
    Algebra.IsAlgebraic.isAlgebraic y
  have hz := hy.algHom
    (IsScalarTower.toAlgHom (Algebra.adjoin F S) (IntermediateField.adjoin F S) E)
  simpa [y, IsScalarTower.toAlgHom_apply] using hz

/-- The transcendence degree of the generic-zero field is bounded by the
cardinality of the actual family of generic coordinates. -/
theorem trdeg_genericZeroField_le_cardinalMk_range
    (I : Ideal (MvPolynomial σ P)) [I.IsPrime] :
    Algebra.trdeg P (GenericZeroField I) ≤ Cardinal.mk (Set.range (genericZero I)) := by
  let S : Set (GenericZeroField I) := Set.range (genericZero I)
  letI : Algebra.IsAlgebraic (Algebra.adjoin P S) (GenericZeroField I) :=
    isAlgebraic_algebraAdjoin_of_intermediateField_adjoin_eq_top S
      (intermediateField_adjoin_range_genericZero_eq_top I)
  exact Algebra.IsAlgebraic.trdeg_le_cardinalMk P S

/-- For `n` coordinates, the generic-zero field has transcendence degree at
most `n`. Equality is allowed, as it must be for the zero prime ideal. -/
theorem trdeg_genericZeroField_fin_le {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) P)) [I.IsPrime] :
    Algebra.trdeg P (GenericZeroField I) ≤ (n : Cardinal) := by
  have htr := trdeg_genericZeroField_le_cardinalMk_range I
  have h := (Cardinal.lift_le.mpr htr).trans
    (Cardinal.mk_range_le_lift (f := genericZero I))
  simpa using h

/-- If the prime ideal is nonzero, the finite-coordinate bound is strict.
This proves the printed strict inequality under the explicit hypothesis missing
from the statement at line 14187. -/
theorem trdeg_genericZeroField_fin_lt_of_ne_bot {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) P)) [I.IsPrime] (hI : I ≠ ⊥) :
    Algebra.trdeg P (GenericZeroField I) < (n : Cardinal) := by
  by_contra hlt
  have hnle : (n : Cardinal) ≤ Algebra.trdeg P (GenericZeroField I) :=
    not_lt.mp hlt
  let S : Set (GenericZeroField I) := Set.range (genericZero I)
  letI : Algebra.IsAlgebraic (Algebra.adjoin P S) (GenericZeroField I) :=
    isAlgebraic_algebraAdjoin_of_intermediateField_adjoin_eq_top S
      (intermediateField_adjoin_range_genericZero_eq_top I)
  have hbasis : IsTranscendenceBasis P (genericZero I) :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite
      P (genericZero I) (by simpa using hnle)
  obtain ⟨f, hfI, hfbot⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI)
  have hfne : f ≠ 0 := by simpa using hfbot
  have heval : MvPolynomial.aeval (genericZero I) f = 0 := by
    rw [aeval_genericZero_eq_algebraMap_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr hfI, map_zero]
  have hinj : Function.Injective (MvPolynomial.aeval (genericZero I)) :=
    algebraicIndependent_iff_injective_aeval.mp hbasis.1
  exact hfne (hinj (by simpa using heval))

/-- A polynomial vanishes at the generic zero of a prime ideal exactly when it
belongs to that ideal. -/
theorem aeval_genericZero_eq_zero_iff_mem (I : Ideal (MvPolynomial σ P)) [I.IsPrime]
    (f : MvPolynomial σ P) :
    MvPolynomial.aeval (genericZero I) f = 0 ↔ f ∈ I := by
  let q : MvPolynomial σ P →ₐ[P] CoordinateRing I := Ideal.Quotient.mkₐ P I
  let j : CoordinateRing I →ₐ[P] GenericZeroField I :=
    IsScalarTower.toAlgHom P (CoordinateRing I) (GenericZeroField I)
  have h_eval : MvPolynomial.aeval (genericZero I) = j.comp q := by
    ext i
    simp [genericZero, q, j]
  constructor
  · intro hf
    have hmap : algebraMap (CoordinateRing I) (GenericZeroField I)
        (Ideal.Quotient.mk I f) = 0 := by
      simpa only [h_eval, AlgHom.comp_apply, q, j, IsScalarTower.toAlgHom_apply,
        Ideal.Quotient.mkₐ_eq_mk] using hf
    have hquot : Ideal.Quotient.mk I f = 0 :=
      IsFractionRing.injective (CoordinateRing I) (GenericZeroField I) (by simpa using hmap)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hquot
  · intro hf
    have hquot : Ideal.Quotient.mk I f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hf
    have hmap : algebraMap (CoordinateRing I) (GenericZeroField I)
        (Ideal.Quotient.mk I f) = 0 := by
      rw [hquot, map_zero]
    simpa only [h_eval, AlgHom.comp_apply, q, j, IsScalarTower.toAlgHom_apply,
      Ideal.Quotient.mkₐ_eq_mk] using hmap

/-- The finite-coordinate form matching Noether's variables `x₁, …, xₙ`. -/
theorem aeval_genericZero_fin_eq_zero_iff_mem {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) P)) [I.IsPrime] (f : MvPolynomial (Fin n) P) :
    MvPolynomial.aeval (genericZero I) f = 0 ↔ f ∈ I :=
  aeval_genericZero_eq_zero_iff_mem I f

#print axioms aeval_genericZero_eq_zero_iff_mem
#print axioms aeval_genericZero_fin_eq_zero_iff_mem
#print axioms aeval_genericZero_eq_algebraMap_mk
#print axioms intermediateField_adjoin_range_genericZero_eq_top
#print axioms trdeg_genericZeroField_le_cardinalMk_range
#print axioms trdeg_genericZeroField_fin_le
#print axioms trdeg_genericZeroField_fin_lt_of_ne_bot

end MathematicalCommons.Noether.EliminationIdealTheorySurvey1924
