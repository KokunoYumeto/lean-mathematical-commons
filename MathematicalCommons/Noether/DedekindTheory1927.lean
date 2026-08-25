import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Noether 1927: the Axiom-II bridge

Noether's Axiom II says that the descending chain condition holds modulo every
nonzero ideal. This file proves the equivalence between that quotient-Artinian
condition and Mathlib's modern `Ring.DimensionLEOne` presentation, under the
paper's Axiom I (`IsNoetherianRing`).
-/

namespace MathematicalCommons.Noether.DedekindTheory1927

variable {R : Type*} [CommRing R]

/-- If every quotient by a nonzero ideal is Artinian, then every nonzero prime
ideal is maximal. No Noetherian or domain hypothesis is needed in this
direction. -/
theorem dimensionLEOne_of_artinian_nonzero_quotients
    (h : ∀ I : Ideal R, I ≠ ⊥ → IsArtinianRing (R ⧸ I)) :
    Ring.DimensionLEOne R where
  maximalOfPrime := by
    intro p hp hprime
    letI : p.IsPrime := hprime
    letI : IsArtinianRing (R ⧸ p) := h p hp
    exact Ideal.Quotient.maximal_of_isField p
      (IsArtinianRing.isField_of_isDomain (R ⧸ p))

/-- In a commutative Noetherian ring of dimension at most one, every quotient
by a nonzero ideal is Artinian. -/
theorem isArtinianRing_quotient_of_dimensionLEOne
    [IsNoetherianRing R] [Ring.DimensionLEOne R]
    (I : Ideal R) (hI : I ≠ ⊥) : IsArtinianRing (R ⧸ I) := by
  letI : IsNoetherianRing (R ⧸ I) :=
    isNoetherianRing_of_surjective R (R ⧸ I) (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  haveI : Ring.KrullDimLE 0 (R ⧸ I) :=
    (Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal).2
      fun J hJ ↦ hJ.1.1.isMaximal <| by
        intro hJbot
        apply hI
        apply le_bot_iff.mp
        simpa [hJbot] using hJ.1.2
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

/-- Noether's Axiom II, in quotient form, is equivalent to the modern
dimension-at-most-one condition once Axiom I is assumed. -/
theorem artinian_nonzero_quotients_iff_dimensionLEOne
    [IsNoetherianRing R] :
    (∀ I : Ideal R, I ≠ ⊥ → IsArtinianRing (R ⧸ I)) ↔
      Ring.DimensionLEOne R := by
  constructor
  · exact dimensionLEOne_of_artinian_nonzero_quotients
  · intro h
    letI : Ring.DimensionLEOne R := h
    exact isArtinianRing_quotient_of_dimensionLEOne

#print axioms dimensionLEOne_of_artinian_nonzero_quotients
#print axioms isArtinianRing_quotient_of_dimensionLEOne
#print axioms artinian_nonzero_quotients_iff_dimensionLEOne

end MathematicalCommons.Noether.DedekindTheory1927
