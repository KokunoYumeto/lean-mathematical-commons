/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.CharZero.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Finite nonvanishing specializations for Hentzelt--Noether regularity arguments

Controlled source: Kurt Hentzelt, freely edited and conceptually recast by
Emmy Noether, *Zur Theorie der Polynomideale und Resultanten*, witness
`NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
in particular the characteristic-zero specialization discussion at line
13319.

This module isolates a reusable fact needed by that discussion: over an
infinite domain, any supplied finite list of nonzero parameter polynomials has
one specialization at which every member stays nonzero.  It does **not** show
that a gcd, resultant, leading coefficient, or regularity determinant is
nonzero, and it does not manufacture the finite list required by the source.
Those algebraic obligations must be proved separately before applying these
lemmas.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open MvPolynomial

namespace RegularitySpecialization

noncomputable section

/-- A source-shaped regularity predicate.  A polynomial of total degree `r`
is regular with respect to `x_i` when its pure term `x_i^r` has nonzero
coefficient.  This is the definition at P22 line 13039. -/
def IsRegularInDegree {R σ : Type*} [CommSemiring R]
    (i : σ) (r : ℕ) (F : MvPolynomial σ R) : Prop :=
  F.totalDegree = r ∧ MvPolynomial.coeff (Finsupp.single i r) F ≠ 0

private theorem eq_zero_of_forall_eval_eq_zero_fin
    {R : Type*} [CommRing R] [IsDomain R] [Infinite R] :
    ∀ {n : ℕ} {p : MvPolynomial (Fin n) R},
      (∀ x : Fin n → R, MvPolynomial.eval x p = 0) → p = 0 := by
  intro n
  induction n with
  | zero =>
      intro p h
      ext d
      simpa only [Subsingleton.elim d 0, MvPolynomial.eval_zero,
        MvPolynomial.coeff_zero, MvPolynomial.constantCoeff_eq] using h 0
  | succ n ih =>
      intro p h
      apply (MvPolynomial.finSuccEquiv R n).injective
      rw [map_zero]
      apply Polynomial.ext
      intro i
      rw [Polynomial.coeff_zero]
      apply ih
      intro s
      let q : Polynomial R :=
        Polynomial.map (MvPolynomial.eval s)
          (MvPolynomial.finSuccEquiv R n p)
      have hq : q = 0 := by
        apply Polynomial.eq_zero_of_infinite_isRoot
        have hroots : {y : R | Polynomial.IsRoot q y} = Set.univ := by
          apply Set.eq_univ_of_forall
          intro y
          change Polynomial.eval y
            (Polynomial.map (MvPolynomial.eval s)
              (MvPolynomial.finSuccEquiv R n p)) = 0
          rw [← MvPolynomial.eval_eq_eval_mv_eval']
          exact h _
        rw [hroots]
        exact Set.infinite_univ
      have hc := congrArg (fun z : Polynomial R ↦ z.coeff i) hq
      simpa [q] using hc

private theorem eq_zero_of_forall_eval_eq_zero
    {R U : Type*} [CommRing R] [IsDomain R] [Infinite R]
    {p : MvPolynomial U R} (h : ∀ a : U → R, MvPolynomial.eval a p = 0) :
    p = 0 := by
  obtain ⟨n, f, hf, q, rfl⟩ := MvPolynomial.exists_fin_rename p
  suffices q = 0 by simp [this]
  apply eq_zero_of_forall_eval_eq_zero_fin
  intro x
  simpa only [MvPolynomial.eval, MvPolynomial.eval₂Hom_rename,
    Function.extend_comp hf] using h (Function.extend f x 0)

/-- A nonzero multivariate polynomial over an infinite domain is nonzero at
some evaluation.  This is the contrapositive existence form of
multivariate polynomial function extensionality. -/
theorem exists_evaluation_ne_zero
    {R U : Type*} [CommRing R] [IsDomain R] [Infinite R]
    (p : MvPolynomial U R) (hp : p ≠ 0) :
    ∃ a : U → R, MvPolynomial.eval a p ≠ 0 := by
  by_contra h_exists
  apply hp
  apply eq_zero_of_forall_eval_eq_zero
  intro a
  by_contra ha
  exact h_exists ⟨a, ha⟩

/-- A finite set of nonzero parameter polynomials has a simultaneous
nonvanishing evaluation.  The proof applies `exists_evaluation_ne_zero` to
their product. -/
theorem exists_evaluation_preserving_finset
    {R U : Type*} [CommRing R] [IsDomain R] [Infinite R]
    (s : Finset (MvPolynomial U R))
    (hs : ∀ p ∈ s, p ≠ 0) :
    ∃ a : U → R, ∀ p ∈ s, MvPolynomial.eval a p ≠ 0 := by
  classical
  have hprod : (∏ p ∈ s, p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hs
  obtain ⟨a, ha⟩ :=
    exists_evaluation_ne_zero (∏ p ∈ s, p) hprod
  rw [MvPolynomial.eval_prod] at ha
  exact ⟨a, Finset.prod_ne_zero_iff.mp ha⟩

/-- Fintype-indexed form of simultaneous nonvanishing specialization.  An
index may occur more than once in the family; no deduplication or chosen
enumeration appears in the statement. -/
theorem exists_evaluation_preserving_fintype
    {R U Ι : Type*} [CommRing R] [IsDomain R] [Infinite R] [Fintype Ι]
    (p : Ι → MvPolynomial U R) (hp : ∀ i, p i ≠ 0) :
    ∃ a : U → R, ∀ i, MvPolynomial.eval a (p i) ≠ 0 := by
  classical
  have hprod : (∏ i : Ι, p i) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun i _hi ↦ hp i)
  obtain ⟨a, ha⟩ :=
    exists_evaluation_ne_zero (∏ i : Ι, p i) hprod
  rw [MvPolynomial.eval_prod] at ha
  exact ⟨a, fun i ↦
    (Finset.prod_ne_zero_iff.mp ha) i (Finset.mem_univ i)⟩

/-- Characteristic-zero field wrapper matching the source's specialization
regime.  The local `Infinite` witness comes from injectivity of the natural
number cast. -/
theorem exists_evaluation_preserving_fintype_charZero
    {P U Ι : Type*} [Field P] [CharZero P] [Fintype Ι]
    (p : Ι → MvPolynomial U P) (hp : ∀ i, p i ≠ 0) :
    ∃ a : U → P, ∀ i, MvPolynomial.eval a (p i) ≠ 0 := by
  letI : Infinite P := Infinite.of_injective Nat.cast Nat.cast_injective
  exact exists_evaluation_preserving_fintype p hp

/-- Mapping coefficients preserves source-shaped regularity whenever the
single pure-power coefficient that witnesses regularity stays nonzero. -/
theorem isRegularInDegree_map_of_coefficient_ne_zero
    {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) {i : σ} {r : ℕ} {F : MvPolynomial σ R}
    (hF : IsRegularInDegree i r F)
    (hcoeff : f (MvPolynomial.coeff (Finsupp.single i r) F) ≠ 0) :
    IsRegularInDegree i r (MvPolynomial.map f F) := by
  constructor
  · apply le_antisymm
    · calc
        (MvPolynomial.map f F).totalDegree ≤ F.totalDegree :=
          by
            simp only [MvPolynomial.totalDegree]
            exact Finset.sup_mono (MvPolynomial.support_map_subset f F)
        _ = r := hF.1
    · have hmem : Finsupp.single i r ∈ (MvPolynomial.map f F).support := by
        rw [MvPolynomial.mem_support_iff]
        simpa only [MvPolynomial.coeff_map] using hcoeff
      simpa using MvPolynomial.le_totalDegree hmem
  · simpa only [MvPolynomial.coeff_map] using hcoeff

/-- A finite family of parameter-polynomial coefficient families can be
specialized once so that every supplied source-shaped regularity witness is
preserved.  The coordinate and degree may depend on the family index. -/
theorem exists_evaluation_preserving_regularity_fintype
    {P U σ Ι : Type*} [CommRing P] [IsDomain P] [Infinite P] [Fintype Ι]
    (coord : Ι → σ) (degree : Ι → ℕ)
    (F : Ι → MvPolynomial σ (MvPolynomial U P))
    (hF : ∀ j, IsRegularInDegree (coord j) (degree j) (F j)) :
    ∃ a : U → P, ∀ j,
      IsRegularInDegree (coord j) (degree j)
        (MvPolynomial.map (MvPolynomial.eval a) (F j)) := by
  let leadingParameter : Ι → MvPolynomial U P := fun j ↦
    MvPolynomial.coeff (Finsupp.single (coord j) (degree j)) (F j)
  have hleading : ∀ j, leadingParameter j ≠ 0 := fun j ↦ (hF j).2
  obtain ⟨a, ha⟩ :=
    exists_evaluation_preserving_fintype leadingParameter hleading
  refine ⟨a, fun j ↦ ?_⟩
  exact isRegularInDegree_map_of_coefficient_ne_zero
    (MvPolynomial.eval a) (hF j) (ha j)

/-- Characteristic-zero field form of simultaneous regularity preservation,
matching the specialization regime stated at P22 line 13319.  It preserves a
finite family whose regularity over the parameter-polynomial ring has already
been proved; it does not construct Hentzelt's later determinant family. -/
theorem exists_evaluation_preserving_regularity_fintype_charZero
    {P U σ Ι : Type*} [Field P] [CharZero P] [Fintype Ι]
    (coord : Ι → σ) (degree : Ι → ℕ)
    (F : Ι → MvPolynomial σ (MvPolynomial U P))
    (hF : ∀ j, IsRegularInDegree (coord j) (degree j) (F j)) :
    ∃ a : U → P, ∀ j,
      IsRegularInDegree (coord j) (degree j)
        (MvPolynomial.map (MvPolynomial.eval a) (F j)) := by
  letI : Infinite P := Infinite.of_injective Nat.cast Nat.cast_injective
  exact exists_evaluation_preserving_regularity_fintype coord degree F hF

#print axioms IsRegularInDegree
#print axioms exists_evaluation_ne_zero
#print axioms exists_evaluation_preserving_finset
#print axioms exists_evaluation_preserving_fintype
#print axioms exists_evaluation_preserving_fintype_charZero
#print axioms isRegularInDegree_map_of_coefficient_ne_zero
#print axioms exists_evaluation_preserving_regularity_fintype
#print axioms exists_evaluation_preserving_regularity_fintype_charZero

end

end RegularitySpecialization

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
