/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.RingTheory.Invariant.Basic

/-!
# Emmy Noether, *Der Endlichkeitssatz der Invarianten endlicher Gruppen* (1916)

Controlled source:
`interlanguage/03_projects/noether/07_german_canon_control/candidates/ED0014/noether.tex`,
lines 5843–5933.

Source mapping:

* Lines 5858–5868: a finite group acts by invertible linear transformations,
  and an invariant is fixed by every transformation.
* Lines 5871–5888: the “Galoissche Resolvente” is the product over the
  transformed linear forms, and its coefficients are invariants.
* Lines 5890–5933: the power-sum reformulation and degree bound belong to the
  later finite-generation argument and are not claimed by this module.

Convention note: Noether writes each resolvent factor as `z +` a transformed
linear form. The standard orbit-polynomial convention below is
`X - C (g • x)`; instantiating `x` with the negative of Noether's linear form
identifies the two products. The multivariate coefficient extraction and the
finite-generation conclusion remain outside this specialized module.

Mathlib v4.31.0 already contains this orbit product and all results below as
`MulSemiringAction.charpoly`, `eval_charpoly`, `smul_charpoly`, and
`smul_coeff_charpoly`. Consequently this file is source-linked packaging,
not a claim of new mathematics. Formal success does not certify the German
transcription.
-/

namespace MathematicalCommons.Noether.FiniteGroupInvariants1916

open Polynomial

section OrbitPolynomial

variable (G R : Type*) [Group G] [Fintype G] [CommRing R]
  [MulSemiringAction G R]

/-- Noether's resolvent specialized to the orbit of one ring element.

This is an explicit source-facing name for Mathlib's exact existing
construction `MulSemiringAction.charpoly`. -/
noncomputable abbrev orbitPolynomial (x : R) : R[X] :=
  MulSemiringAction.charpoly G x

/-- The source-facing orbit polynomial is the product of its linear orbit
factors. -/
theorem orbitPolynomial_eq (x : R) :
    orbitPolynomial G R x = ∏ g : G, (X - C (g • x)) :=
  MulSemiringAction.charpoly_eq G x

/-- The orbit polynomial is monic. -/
theorem orbitPolynomial_monic (x : R) :
    (orbitPolynomial G R x).Monic :=
  MulSemiringAction.monic_charpoly G x

/-- The original element occurs in its orbit (at the identity), so it is a
root of the orbit polynomial. -/
theorem orbitPolynomial_isRoot (x : R) :
    (orbitPolynomial G R x).IsRoot x := by
  exact MulSemiringAction.eval_charpoly G x

/-- The orbit polynomial is invariant under the induced action on
polynomials. -/
theorem orbitPolynomial_fixed (x : R) (g : G) :
    g • orbitPolynomial G R x = orbitPolynomial G R x :=
  MulSemiringAction.smul_charpoly x g

/-- Every coefficient of the orbit polynomial is invariant. This is the
formal content of the coefficient-invariance assertion for the specialized
resolvent. -/
theorem orbitPolynomial_coeff_fixed (x : R) (n : ℕ) (g : G) :
    g • (orbitPolynomial G R x).coeff n =
      (orbitPolynomial G R x).coeff n :=
  MulSemiringAction.smul_coeff_charpoly x n g

/-- A compact audit bundle recording the properties of Noether's specialized
resolvent used by downstream source coverage. -/
theorem orbitPolynomial_audit_bundle (x : R) :
    (orbitPolynomial G R x).Monic ∧
      (orbitPolynomial G R x).IsRoot x ∧
      (∀ g : G, g • orbitPolynomial G R x = orbitPolynomial G R x) ∧
      (∀ (n : ℕ) (g : G),
        g • (orbitPolynomial G R x).coeff n =
          (orbitPolynomial G R x).coeff n) := by
  exact ⟨orbitPolynomial_monic G R x,
    orbitPolynomial_isRoot G R x,
    orbitPolynomial_fixed G R x,
    orbitPolynomial_coeff_fixed G R x⟩

#print axioms orbitPolynomial_eq
#print axioms orbitPolynomial_monic
#print axioms orbitPolynomial_isRoot
#print axioms orbitPolynomial_fixed
#print axioms orbitPolynomial_coeff_fixed
#print axioms orbitPolynomial_audit_bundle

end OrbitPolynomial

end MathematicalCommons.Noether.FiniteGroupInvariants1916
