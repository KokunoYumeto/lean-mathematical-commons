import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Noether's algebraic and differential invariants (1923)

Controlled source: Emmy Noether, *Algebraische und Differentialinvarianten*,
witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`.

The coefficient-retraction lemmas isolate the algebraic replacement step in
Satz 3 at lines 13592--13600. They assume the required projection and do not
construct Hilbert/Fischer's Ω-process or a Reynolds operator.

The final two theorems formalize the uniform-exponent core of Satz 5.
The exponent is chosen from `a` before the universally quantified ideal `b`.
Historical ideal divisibility is represented by reverse inclusion, so
“`b ^ r` is divisible by `a`” becomes `b ^ r ≤ a`.
-/

namespace MathematicalCommons.Noether.AlgebraicDifferentialInvariants1923

open Ideal
open scoped BigOperators

noncomputable section

section CoefficientRetraction

variable {R ι : Type*} [AddCommMonoid R] [Mul R]

/-- An additive map passes through a finite coefficient identity when it
commutes with right multiplication by each displayed generator. -/
theorem map_sum_mul_of_map_mul
    (ρ : R →+ R) (s : Finset ι) (coefficient generator : ι → R)
    (hρ_mul : ∀ i ∈ s,
      ρ (coefficient i * generator i) = ρ (coefficient i) * generator i) :
    ρ (∑ i ∈ s, coefficient i * generator i) =
      ∑ i ∈ s, ρ (coefficient i) * generator i := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact hρ_mul i hi

/-- Replacing every coefficient by its projection preserves a finite
expression for an invariant target, provided the projection fixes that target
and is compatible with multiplication by invariant generators. -/
theorem replace_coefficients_by_retraction
    (Invariant : R → Prop) (ρ : R →+ R) (s : Finset ι)
    (target : R) (coefficient generator : ι → R)
    (hfix : ∀ x, Invariant x → ρ x = x)
    (hρ_mul : ∀ a j, Invariant j → ρ (a * j) = ρ a * j)
    (htarget : Invariant target)
    (hgenerator : ∀ i ∈ s, Invariant (generator i))
    (hidentity : target = ∑ i ∈ s, coefficient i * generator i) :
    target = ∑ i ∈ s, ρ (coefficient i) * generator i := by
  calc
    target = ρ target := (hfix target htarget).symm
    _ = ρ (∑ i ∈ s, coefficient i * generator i) := congrArg ρ hidentity
    _ = ∑ i ∈ s, ρ (coefficient i) * generator i :=
      map_sum_mul_of_map_mul ρ s coefficient generator fun i hi ↦
        hρ_mul (coefficient i) (generator i) (hgenerator i hi)

/-- Existence form of `replace_coefficients_by_retraction`: if the range of
the projection consists of invariant elements, any finite coefficient
identity for an invariant target using invariant generators has invariant
coefficients. -/
theorem exists_invariant_coefficients_of_retraction
    (Invariant : R → Prop) (ρ : R →+ R) (s : Finset ι)
    (target : R) (coefficient generator : ι → R)
    (hfix : ∀ x, Invariant x → ρ x = x)
    (hrange : ∀ x, Invariant (ρ x))
    (hρ_mul : ∀ a j, Invariant j → ρ (a * j) = ρ a * j)
    (htarget : Invariant target)
    (hgenerator : ∀ i ∈ s, Invariant (generator i))
    (hidentity : target = ∑ i ∈ s, coefficient i * generator i) :
    ∃ invariantCoefficient : ι → R,
      (∀ i ∈ s, Invariant (invariantCoefficient i)) ∧
      target = ∑ i ∈ s, invariantCoefficient i * generator i := by
  refine ⟨fun i ↦ ρ (coefficient i), ?_, ?_⟩
  · intro i _
    exact hrange (coefficient i)
  · exact replace_coefficients_by_retraction Invariant ρ s target coefficient generator
      hfix hρ_mul htarget hgenerator hidentity

end CoefficientRetraction

/--
Algebraic core of Satz 5. In a Noetherian commutative semiring, a fixed ideal
`a` admits one positive exponent that sends every ideal below `a.radical` into
`a`. The exponent is uniform in `b`.
-/
theorem exists_uniformExponent_of_le_radical
    {R : Type*} [CommSemiring R] [IsNoetherianRing R] (a : Ideal R) :
    ∃ r : ℕ, 0 < r ∧ ∀ b : Ideal R, b ≤ a.radical → b ^ r ≤ a := by
  obtain ⟨r, hr⟩ :=
    a.exists_radical_pow_le_of_fg a.radical.fg_of_isNoetherianRing
  refine ⟨r + 1, Nat.zero_lt_succ r, fun b hba ↦ ?_⟩
  exact (Ideal.pow_right_mono hba (r + 1)).trans <|
    (Ideal.pow_le_pow_right (I := a.radical) r.le_succ).trans hr

variable {k K σ : Type*}
variable [Field k] [Field K] [Algebra k K] [IsAlgClosed K] [Finite σ]

/--
Noether's Satz 5: for a fixed polynomial ideal `a`, there is a single exponent
`r` such that every polynomial ideal `b` vanishing at every common zero of `a`
satisfies `b ^ r ≤ a`.

The common zeros are taken in an algebraically closed extension `K` of the
coefficient field `k`. This is the modern hypothesis under which the
vanishing condition is equivalent to `b ≤ a.radical`.
-/
theorem exists_uniformExponent_of_vanishingOn_zeroLocus
    (a : Ideal (MvPolynomial σ k)) :
    ∃ r : ℕ, 0 < r ∧ ∀ b : Ideal (MvPolynomial σ k),
      (∀ f ∈ b, ∀ x ∈ MvPolynomial.zeroLocus K a, MvPolynomial.aeval x f = 0) →
        b ^ r ≤ a := by
  obtain ⟨r, hrpos, hr⟩ := exists_uniformExponent_of_le_radical a
  refine ⟨r, hrpos, fun b hb ↦ hr b ?_⟩
  have hba : b ≤ a.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) a]
    intro f hf x hx
    exact hb f hf x hx
  exact hba

#print axioms map_sum_mul_of_map_mul
#print axioms replace_coefficients_by_retraction
#print axioms exists_invariant_coefficients_of_retraction
#print axioms exists_uniformExponent_of_le_radical
#print axioms exists_uniformExponent_of_vanishingOn_zeroLocus

end

end MathematicalCommons.Noether.AlgebraicDifferentialInvariants1923
