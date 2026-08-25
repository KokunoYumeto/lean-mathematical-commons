/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Trace.Quotient

/-!
# Noether 1927: quotient reduction of a discriminant

Controlled source: Emmy Noether, *Der Diskriminantensatz für die Ordnungen
eines algebraischen Zahl- oder Funktionenkörpers*, witness `NOETH-DE-ED-0014`,
SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
line 16041.

This file formalizes the local finite-free matrix constituent: reducing a
basis modulo the maximal ideal reduces its trace matrix and hence its
discriminant. No claim is made here about Noether's full arbitrary-order
criterion, primary components, or reverse étale descent.
-/

open IsLocalRing Module

namespace MathematicalCommons.Noether.DiscriminantTheorem1927

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [Module.Free R S] [Module.Finite R S]

local notation "p" => maximalIdeal R

attribute [local instance] Ideal.Quotient.field

/-- The discriminant of the quotient basis is the residue class of the
original discriminant. This is Noether's quotient-discriminant reduction at
controlled source line 16041, in Mathlib's local maximal-ideal setting. -/
theorem discr_basisQuotient [Fintype ι] [DecidableEq ι] (b : Basis ι R S) :
    Algebra.discr (R ⧸ p) (basisQuotient b) =
      Ideal.Quotient.mk p (Algebra.discr R b) := by
  classical
  rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
  congr 1
  ext i j
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    basisQuotient_apply, ← map_mul, Algebra.trace_quotient_mk,
    RingHom.mapMatrix_apply, Matrix.map_apply]

#print axioms discr_basisQuotient

end MathematicalCommons.Noether.DiscriminantTheorem1927
