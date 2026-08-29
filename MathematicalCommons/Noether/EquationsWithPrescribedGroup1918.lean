/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Emmy Noether, *Gleichungen mit vorgeschriebener Gruppe* (1918)

Controlled source:
`interlanguage/03_projects/noether/07_german_canon_control/candidates/ED0020/noether.tex`,
SHA-256
`77D5BF32D9C6606EAB7DE4579097808EA1EEFD09949A81ED579DFFDB3A87F8C2`,
lines 7882--8084.

Source mapping:

* Lines 7901 and 7938--7942 characterize the desired minimal basis of the
  invariant field as an algebraically independent family of `n` rational
  functions.
* Lines 7942--8017 derive Noether's sufficient condition for a rational
  parameterization of equations with prescribed group, including the explicit
  singular-value qualification.
* Lines 8024--8067 reduce the remaining rationality problem to `n - 2`
  variables.
* Lines 8069--8079 apply Lüroth and Castelnuovo to the degree-three and
  degree-four cases.

Mathlib v4.31.0 already proves the fundamental theorem of symmetric
polynomials as `MvPolynomial.esymmAlgEquiv`.  The first theorem below records
the algebraic independence consequence for the elementary-symmetric family;
the second gives the exact existing invariant-ring equivalence a source-facing
name; and the third transports it to fraction rings.

Internet provenance note: a focused GitHub audit found a 138-line Lean file in
`rjwalters/lean-genius` PR 28732 (no repository license was observed during
the bounded audit), commit
`494c45c4a1000ba00e15ae515d87916628c9d3a2`, path
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ11.lean`, 6,932 bytes, SHA-256
`3ACBE0B58F153BB753355C2F55FE04C61E51684FEEBF8B4F3E5F6C64D6EAA3B4`.
It supplied a mathematical/API lead, but no external source bytes are copied
here: these proofs are written directly against the cited Mathlib API.

The fraction-ring equivalence below is **not** an identification of the
fraction ring of `symmetricSubalgebra` with the fixed subfield of the rational
function field.  That fixed-field bridge, Noether's general minimal-basis
criterion and parameterization theorem, the singular-locus analysis, the
`n - 2` reduction, and the degree-three/four conclusions remain open.  Lean
success here does not certify the German transcription.
-/

namespace MathematicalCommons.Noether.EquationsWithPrescribedGroup1918

open MvPolynomial

section SymmetricPolynomials

variable {σ : Type*} [Fintype σ]
variable (R : Type*) [CommRing R] {n : ℕ}

/-- The first `n` elementary symmetric polynomials are algebraically
independent whenever the ambient variable type has at least `n` elements. -/
theorem elementarySymmetric_algebraicIndependent
    (hn : n ≤ Fintype.card σ) :
    AlgebraicIndependent R (fun i : Fin n => esymm σ R (i + 1)) := by
  rw [algebraicIndependent_iff_injective_aeval]
  intro p q hpq
  apply esymmAlgHom_injective R hn
  apply Subtype.ext
  simpa only [esymmAlgHom_apply] using hpq

/-- Source-facing name for Mathlib's fundamental theorem of symmetric
polynomials: the symmetric invariant ring is a polynomial algebra on the
elementary symmetric generators. -/
noncomputable abbrev symmetricInvariantRingAlgEquiv
    (hcard : Fintype.card σ = n) :
    MvPolynomial (Fin n) R ≃ₐ[R] symmetricSubalgebra σ R :=
  esymmAlgEquiv σ R hcard

end SymmetricPolynomials

section FractionFields

variable (K : Type*) [Field K]

/-- The fraction ring of the symmetric invariant ring is a rational function
field, obtained by extending the fundamental symmetric-polynomial equivalence
to fraction rings.

This does not assert that this fraction ring is the fixed subfield of the
ambient rational function field. -/
noncomputable def symmetricInvariantFractionRingAlgEquiv (n : ℕ) :
    FractionRing (MvPolynomial (Fin n) K) ≃ₐ[K]
      FractionRing (symmetricSubalgebra (Fin n) K) := by
  letI : IsScalarTower K (MvPolynomial (Fin n) K)
      (FractionRing (MvPolynomial (Fin n) K)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower K (symmetricSubalgebra (Fin n) K)
      (FractionRing (symmetricSubalgebra (Fin n) K)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact IsFractionRing.algEquivOfAlgEquiv
    (symmetricInvariantRingAlgEquiv K (Fintype.card_fin n))

end FractionFields

#print axioms elementarySymmetric_algebraicIndependent
#print axioms symmetricInvariantRingAlgEquiv
#print axioms symmetricInvariantFractionRingAlgEquiv

end MathematicalCommons.Noether.EquationsWithPrescribedGroup1918
