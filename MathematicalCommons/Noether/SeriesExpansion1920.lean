import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.Ideal.Maps

/-!
# Noether 1920: the relation-ideal congruence

This file isolates the exact kernel-congruence content of formula [3] at
controlled source lines 9941–9947 of Emmy Noether's 1920 paper
*Zur Reihenentwicklung in der Formentheorie*.

The declarations do not construct Fischer's normal form, prove uniqueness of
a representative, identify a determinant or Plücker kernel, or prove a series
expansion.
-/

namespace MathematicalCommons.Noether.SeriesExpansion1920

variable {R σ τ : Type*} [CommRing R]

/-- The ideal of all polynomial relations among the substituted polynomials
`f i`. This is Noether's relation “module” `M` in modern terminology. -/
noncomputable def relationIdeal (f : σ → MvPolynomial τ R) :
    Ideal (MvPolynomial σ R) :=
  RingHom.ker (MvPolynomial.bind₁ f).toRingHom

/-- Two polynomials agree after the substitution `X i ↦ f i` exactly when
their difference belongs to the relation ideal.

This is only the congruence content of Noether's formula [3], not the
existence or uniqueness of her distinguished normal form `Φ`. -/
theorem sub_mem_relationIdeal_iff
    (f : σ → MvPolynomial τ R) (F Phi : MvPolynomial σ R) :
    F - Phi ∈ relationIdeal f ↔
      MvPolynomial.bind₁ f F = MvPolynomial.bind₁ f Phi := by
  change F - Phi ∈ RingHom.ker (MvPolynomial.bind₁ f).toRingHom ↔
    (MvPolynomial.bind₁ f).toRingHom F =
      (MvPolynomial.bind₁ f).toRingHom Phi
  exact RingHom.sub_mem_ker_iff (MvPolynomial.bind₁ f).toRingHom

#print axioms sub_mem_relationIdeal_iff

end MathematicalCommons.Noether.SeriesExpansion1920
