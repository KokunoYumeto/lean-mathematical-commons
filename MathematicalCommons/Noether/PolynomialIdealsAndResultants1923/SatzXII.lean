/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Pi

/-!
# Hentzelt--Noether 1923: Satz XII and its Nullstellensatz corollary

Controlled source: Kurt Hentzelt, freely edited and conceptually recast by
Emmy Noether, *Zur Theorie der Polynomideale und Resultanten*, witness
`NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
the corollary immediately after Satz XII at line 13445.

The source first constructs finitely many compatible partial zeros, then
concludes that every polynomial ideal without a zero is the unit ideal.  This
module formalizes the finite-coordinate substrate: if the ideal contains a
nonzero univariate polynomial in every coordinate, its common zero locus
embeds in the finite product of the corresponding root sets.  Algebraic
closedness is not needed for that finiteness direction.  The final theorem is
the exact modern Nullstellensatz corollary over an algebraically closed
extension.  The stronger successive compatibility construction remains open.
-/

open Polynomial

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.SatzXII

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable {n : ℕ}

/-- Regard a univariate polynomial as a multivariate polynomial in the single
coordinate `i`. -/
noncomputable def coordinatePolynomial (i : Fin n) :
    k[X] →ₐ[k] MvPolynomial (Fin n) k :=
  Polynomial.aeval (MvPolynomial.X i)

/-- Evaluating a coordinate polynomial at a point is ordinary univariate
evaluation at the corresponding coordinate. -/
@[simp]
theorem aeval_coordinatePolynomial
    (x : Fin n → K) (i : Fin n) (p : k[X]) :
    MvPolynomial.aeval x (coordinatePolynomial i p) =
      Polynomial.aeval (x i) p := by
  rw [coordinatePolynomial, ← Polynomial.aeval_algHom_apply]
  simp

/-- Every common zero lies in the coordinatewise product of the root sets of
the displayed univariate polynomials. -/
theorem zeroLocus_subset_coordinateRootBox
    (I : Ideal (MvPolynomial (Fin n) k))
    (p : Fin n → k[X])
    (hp : ∀ i, p i ≠ 0)
    (hmem : ∀ i, coordinatePolynomial i (p i) ∈ I) :
    MvPolynomial.zeroLocus K I ⊆
      {x : Fin n → K | ∀ i, x i ∈ (p i).rootSet K} := by
  intro x hx i
  rw [Polynomial.mem_rootSet_of_ne (hp i)]
  rw [← aeval_coordinatePolynomial x i (p i)]
  exact (MvPolynomial.mem_zeroLocus_iff.mp hx) _ (hmem i)

/-- The coordinate root box is finite because it is a finite product of
finite univariate root sets. -/
theorem coordinateRootBox_finite (p : Fin n → k[X]) :
    Set.Finite {x : Fin n → K | ∀ i, x i ∈ (p i).rootSet K} :=
  Set.Finite.pi' fun i ↦ Polynomial.rootSet_finite (p i) K

/-- The identity-on-coordinates injection from the common zero locus into the
product of coordinate root sets. -/
noncomputable def zeroLocusEmbeddingCoordinateRootBox
    (I : Ideal (MvPolynomial (Fin n) k))
    (p : Fin n → k[X])
    (hp : ∀ i, p i ≠ 0)
    (hmem : ∀ i, coordinatePolynomial i (p i) ∈ I) :
    (MvPolynomial.zeroLocus K I) ↪
      (∀ i : Fin n, (p i).rootSet K) where
  toFun x i :=
    ⟨x.1 i, zeroLocus_subset_coordinateRootBox I p hp hmem x.2 i⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hxy i)

/-- Fixed-family form of the finite-zero theorem. -/
theorem zeroLocus_finite_of_coordinatePolynomials
    (I : Ideal (MvPolynomial (Fin n) k))
    (p : Fin n → k[X])
    (hp : ∀ i, p i ≠ 0)
    (hmem : ∀ i, coordinatePolynomial i (p i) ∈ I) :
    (MvPolynomial.zeroLocus K I).Finite :=
  (coordinateRootBox_finite p).subset
    (zeroLocus_subset_coordinateRootBox I p hp hmem)

/-- Existential form: the ideal contains some nonzero univariate polynomial
in every coordinate. -/
theorem zeroLocus_finite_of_exists_coordinatePolynomial
    (I : Ideal (MvPolynomial (Fin n) k))
    (hcoord : ∀ i : Fin n,
      ∃ p : k[X], p ≠ 0 ∧ coordinatePolynomial i p ∈ I) :
    (MvPolynomial.zeroLocus K I).Finite := by
  classical
  let p : Fin n → k[X] := fun i ↦ (hcoord i).choose
  have hp : ∀ i, p i ≠ 0 := fun i ↦ (hcoord i).choose_spec.1
  have hmem : ∀ i, coordinatePolynomial i (p i) ∈ I :=
    fun i ↦ (hcoord i).choose_spec.2
  exact zeroLocus_finite_of_coordinatePolynomials I p hp hmem

/-- A finite-variable polynomial ideal has no common zero over an
algebraically closed extension field exactly when it is the unit ideal. -/
theorem zeroLocus_eq_empty_iff_eq_top {σ : Type*} [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) :
    MvPolynomial.zeroLocus K I = ∅ ↔ I = ⊤ := by
  constructor
  · intro hzero
    rw [← Ideal.radical_eq_top,
      ← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) I,
      hzero, MvPolynomial.vanishingIdeal_empty]
  · rintro rfl
    exact MvPolynomial.zeroLocus_top

#print axioms coordinatePolynomial
#print axioms aeval_coordinatePolynomial
#print axioms zeroLocus_subset_coordinateRootBox
#print axioms coordinateRootBox_finite
#print axioms zeroLocusEmbeddingCoordinateRootBox
#print axioms zeroLocus_finite_of_coordinatePolynomials
#print axioms zeroLocus_finite_of_exists_coordinatePolynomial
#print axioms zeroLocus_eq_empty_iff_eq_top

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.SatzXII
