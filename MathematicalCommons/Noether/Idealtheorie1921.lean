/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.IsPrimary
import Mathlib.RingTheory.Lasker

/-!
# Emmy Noether, *Idealtheorie in Ringbereichen* (1921)

Source: E. Noether, *Mathematische Annalen* 83 (1921), 24–66,
<https://doi.org/10.1007/BF01464225>.

This module separates three kinds of declarations:

* source-shaped aliases of results already present in Mathlib;
* source-shaped combinations that are not direct Mathlib declarations;
* future mathematical gaps, which must not be represented with `sorry` here.

The controlled German witness and exact snapshot identity are recorded in
`sources/noether/CANON_REFERENCE.json`. Formal success does not certify the
transcription.
-/

namespace MathematicalCommons.Noether.Idealtheorie1921

/-- The finite-basis/ascending-chain equivalence assembled from Noether's §1
finite-basis hypothesis, Satz I, and the converse immediately after its proof.
Mathlib states the modern equivalence as `isNoetherianRing_iff_ideal_fg`. -/
theorem finiteBasis_iff_noetherian (R : Type*) [Semiring R] :
    IsNoetherianRing R ↔ ∀ I : Ideal R, I.FG :=
  isNoetherianRing_iff_ideal_fg R

/-- **Noether 1921, §2, Satz II.** Every ideal in a Noetherian ring is a finite
infimum of infimum-irreducible ideals. This is Mathlib's order-theoretic
`exists_infIrred_decomposition` specialized to ideals. -/
theorem finiteIrreducibleDecomposition
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    ∃ s : Finset (Ideal R), s.inf id = I ∧ ∀ ⦃J⦄, J ∈ s → InfIrred J :=
  exists_infIrred_decomposition I

/-- Noether's Definition III of a primary ideal, already present in Mathlib as
`Ideal.isPrimary_iff`. -/
theorem primary_iff_factor_or_power
    {R : Type*} [CommSemiring R] {Q : Ideal R} :
    Q.IsPrimary ↔ Q ≠ ⊤ ∧
      ∀ {a b : R}, a * b ∈ Q → a ∈ Q ∨ b ∈ Q.radical :=
  Ideal.isPrimary_iff

/-- **Noether 1921, §4, Definition IIIa**, in ideal-product form.

The uniform positive exponent for the whole ideal `B` uses Noetherian finite
generation. This is a source-shaped consequence of Mathlib's elementwise
definition plus `Ideal.exists_pow_le_of_le_radical_of_fg`. -/
theorem primary_iff_ideal_product_or_power
    {R : Type*} [CommRing R] [IsNoetherianRing R] {Q : Ideal R} :
    Q.IsPrimary ↔ Q ≠ ⊤ ∧
      ∀ {A B : Ideal R}, A * B ≤ Q → A ≤ Q ∨
        ∃ n : ℕ, 0 < n ∧ B ^ n ≤ Q := by
  constructor
  · intro hQ
    refine ⟨hQ.ne_top, ?_⟩
    intro A B hAB
    by_cases hAQ : A ≤ Q
    · exact Or.inl hAQ
    · right
      have hB : B ≤ Q.radical := by
        obtain ⟨a, haA, haQ⟩ := SetLike.not_le_iff_exists.mp hAQ
        intro b hbB
        have habQ : a * b ∈ Q := hAB (Ideal.mul_mem_mul haA hbB)
        exact (Ideal.isPrimary_iff.mp hQ).2 habQ |>.resolve_left haQ
      obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hB B.fg_of_isNoetherianRing
      have hnpos : 0 < n := by
        apply Nat.pos_of_ne_zero
        intro hnzero
        have htop : (⊤ : Ideal R) ≤ Q := by simpa [hnzero] using hn
        exact hQ.ne_top (eq_top_iff.mpr htop)
      exact ⟨n, hnpos, hn⟩
  · rintro ⟨hQtop, hQ⟩
    rw [Ideal.isPrimary_iff]
    refine ⟨hQtop, ?_⟩
    intro x y hxy
    by_cases hx : x ∈ Q
    · exact Or.inl hx
    · right
      have hmul : Ideal.span {x} * Ideal.span {y} ≤ Q := by
        rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_le]
        simpa using hxy
      have hxspan : ¬Ideal.span {x} ≤ Q := by
        simpa [Ideal.span_singleton_le_iff_mem] using hx
      obtain ⟨n, -, hn⟩ := (hQ hmul).resolve_left hxspan
      refine ⟨n, ?_⟩
      apply hn
      rw [Ideal.span_singleton_pow]
      exact Ideal.subset_span (Set.mem_singleton _)

/-- **Noether 1921, §4, Satz VI.** An infimum-irreducible ideal in a
commutative Noetherian ring is primary. Mathlib proves this at the more general
submodule level as `InfIrred.isPrimary`. -/
theorem irreducible_isPrimary
    {R : Type*} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
    (hI : InfIrred I) : I.IsPrimary :=
  hI.isPrimary

/-- **Noether 1921, §5, Zusatz after Satz VIII.** Every prime ideal is
infimum-irreducible. -/
theorem prime_isIrreducible
    {R : Type*} [CommRing R] {P : Ideal R} (hP : P.IsPrime) : InfIrred P := by
  apply InfPrime.infIrred
  refine ⟨not_isMax_iff_ne_top.mpr hP.ne_top, ?_⟩
  intro I J hIJ
  exact hP.inf_le.mp hIJ

/-- The modern Lasker–Noether decomposition statement: every ideal in a
commutative Noetherian ring is a finite intersection of primary ideals.
Mathlib already supplies the stronger module-level theorem
`Submodule.isLasker`. -/
theorem primaryDecomposition
    (R : Type*) [CommRing R] [IsNoetherianRing R] : IsLasker R R :=
  Submodule.isLasker R R

/-- **Noether 1921, §5, Satz VIII (first direction).** A nonempty finite
intersection of primary ideals with the same associated prime is primary. The
associated prime is represented by the common radical. -/
theorem primaryFiniteInf_sameAssociatedPrime
    {R : Type*} [CommRing R] {ι : Type*} {s : Finset ι}
    {f : ι → Ideal R} {i : ι} (hi : i ∈ s)
    (hprimary : ∀ ⦃j⦄, j ∈ s → (f j).IsPrimary)
    (hradical : ∀ ⦃j⦄, j ∈ s → (f j).radical = (f i).radical) :
    (s.inf f).IsPrimary :=
  Ideal.isPrimary_finsetInf hi hprimary hradical

/-- **Noether 1921, §4, Satz V.**

For a primary ideal `Q` in a commutative Noetherian ring, there is a unique
prime ideal `P` such that `Q ≤ P` and some power of `P` is contained in `Q`.
The unique `P` is `Q.radical`.

Mathlib contains the two main ingredients separately:
`Ideal.isPrime_radical` and `Ideal.exists_radical_pow_le_of_fg`. This theorem
packages the existence and uniqueness in Noether's source order and fixes the
historical divisibility convention as modern ideal inclusions.
-/
theorem existsUnique_associatedPrime
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (Q : Ideal R) (hQ : Q.IsPrimary) :
    ∃! P : Ideal R, P.IsPrime ∧ Q ≤ P ∧ ∃ n : ℕ, 0 < n ∧ P ^ n ≤ Q := by
  have hPrime : Q.radical.IsPrime := Ideal.isPrime_radical hQ
  have hFG : Q.radical.FG :=
    (isNoetherianRing_iff_ideal_fg R).mp (by infer_instance) Q.radical
  obtain ⟨n, hn⟩ := Q.exists_radical_pow_le_of_fg hFG
  have hnpos : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hnzero
    have htop : (⊤ : Ideal R) ≤ Q := by simpa [hnzero] using hn
    exact (Ideal.isPrimary_iff.mp hQ).1 (eq_top_iff.mpr htop)
  refine ⟨Q.radical, ⟨hPrime, Ideal.le_radical, ⟨n, hnpos, hn⟩⟩, ?_⟩
  intro P hP
  rcases hP with ⟨hPPrime, hQP, n, -, hPow⟩
  apply le_antisymm
  · letI : Q.radical.IsPrime := hPrime
    exact Ideal.IsPrime.le_of_pow_le (hPow.trans Ideal.le_radical)
  · exact hPPrime.radical_le_iff.mpr hQP

/-- The omitted "greatest common divisor" clause of Noether's Satz V, stated
as the modern inclusion universal property of `Q.radical`: every ideal whose
positive power is contained in `Q` is contained in the associated prime. -/
theorem associatedPrime_isGreatest_powerContained
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (Q : Ideal R) (hQ : Q.IsPrimary) :
    Q.radical.IsPrime ∧ Q ≤ Q.radical ∧
      (∃ n : ℕ, 0 < n ∧ Q.radical ^ n ≤ Q) ∧
      ∀ B : Ideal R, (∃ n : ℕ, 0 < n ∧ B ^ n ≤ Q) → B ≤ Q.radical := by
  have hPrime : Q.radical.IsPrime := Ideal.isPrime_radical hQ
  have hFG : Q.radical.FG := Q.radical.fg_of_isNoetherianRing
  obtain ⟨n, hn⟩ := Q.exists_radical_pow_le_of_fg hFG
  have hnpos : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hnzero
    have htop : (⊤ : Ideal R) ≤ Q := by simpa [hnzero] using hn
    exact hQ.ne_top (eq_top_iff.mpr htop)
  refine ⟨hPrime, Ideal.le_radical, ⟨n, hnpos, hn⟩, ?_⟩
  intro B hB
  rcases hB with ⟨m, -, hm⟩
  letI : Q.radical.IsPrime := hPrime
  exact Ideal.IsPrime.le_of_pow_le (hm.trans Ideal.le_radical)

/-- The exponent clause of Noether's Satz V: the associated prime has a least
positive power contained in the primary ideal. -/
theorem exists_least_associatedPrimeExponent
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (Q : Ideal R) (hQ : Q.IsPrimary) :
    ∃ ρ : ℕ, 0 < ρ ∧ Q.radical ^ ρ ≤ Q ∧
      ∀ n : ℕ, 0 < n → Q.radical ^ n ≤ Q → ρ ≤ n := by
  classical
  obtain ⟨n, hnpos, hn⟩ :=
    associatedPrime_isGreatest_powerContained Q hQ |>.2.2.1
  let hExists : ∃ k : ℕ, 0 < k ∧ Q.radical ^ k ≤ Q := ⟨n, hnpos, hn⟩
  let ρ := Nat.find hExists
  refine ⟨ρ, (Nat.find_spec hExists).1, (Nat.find_spec hExists).2, ?_⟩
  intro k hkpos hk
  exact Nat.find_min' hExists ⟨hkpos, hk⟩

#print axioms finiteBasis_iff_noetherian
#print axioms primary_iff_factor_or_power
#print axioms primary_iff_ideal_product_or_power
#print axioms finiteIrreducibleDecomposition
#print axioms irreducible_isPrimary
#print axioms prime_isIrreducible
#print axioms primaryDecomposition
#print axioms primaryFiniteInf_sameAssociatedPrime
#print axioms existsUnique_associatedPrime
#print axioms associatedPrime_isGreatest_powerContained
#print axioms exists_least_associatedPrimeExponent

end MathematicalCommons.Noether.Idealtheorie1921
