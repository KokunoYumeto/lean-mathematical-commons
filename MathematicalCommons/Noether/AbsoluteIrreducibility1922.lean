/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic

/-!
# Emmy Noether, *Ein algebraisches Kriterium für absolute Irreduzibilität* (1922)

Controlled source: `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
lines 12398–12608.

At lines 12594–12598 Noether forms a nonzero ideal from specialized
coefficients of the reducibility form and observes that only finitely many
prime ideals divide it. This module isolates that factorization step. It does
not construct the reducibility form, characterize absolute irreducibility, or
prove the Ostrowski specialization theorem stated at lines 12411–12413.

Both declarations are short source-linked packages around Mathlib's existing
finite-divisor theorem for unique factorization monoids. They are not claimed
as new factorization mathematics.
-/

namespace MathematicalCommons.Noether.AbsoluteIrreducibility1922

/-- A nonzero element of a unique factorization monoid with finitely many units
has only finitely many prime divisors. -/
theorem finite_prime_divisors
    {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M] [Fintype Mˣ]
    (a : M) (ha : a ≠ 0) :
    {p : M | Prime p ∧ p ∣ a}.Finite := by
  have hdiv : {x : M | x ∣ a}.Finite :=
    Set.finite_def.mpr ⟨UniqueFactorizationMonoid.fintypeSubtypeDvd a ha⟩
  exact hdiv.subset fun _ hp ↦ hp.2

/-- In a Dedekind domain, only finitely many prime ideals divide a given
nonzero ideal. This is the ideal-theoretic form of the finiteness observation
used at controlled line 12598. -/
theorem finite_primeIdeal_divisors
    {A : Type*} [CommRing A] [IsDedekindDomain A]
    (I : Ideal A) (hI : I ≠ ⊥) :
    {P : Ideal A | P.IsPrime ∧ P ∣ I}.Finite := by
  have hdiv : {J : Ideal A | J ∣ I}.Finite :=
    Set.finite_def.mpr
      ⟨UniqueFactorizationMonoid.fintypeSubtypeDvd I
        (by simpa only [Ideal.zero_eq_bot] using hI)⟩
  exact hdiv.subset fun _ hP ↦ hP.2

#print axioms finite_prime_divisors
#print axioms finite_primeIdeal_divisors

end MathematicalCommons.Noether.AbsoluteIrreducibility1922

