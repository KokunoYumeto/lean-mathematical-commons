/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.FirstGroundPairedQuotient
import Mathlib.RingTheory.Ideal.Colon

/-!
# Hentzelt--Noether Satz VIII: one-stage denominator descent

Module for P22, controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
lines 13344--13373, especially equation (33).

The printed proof starts with a stage element `G` and a nonzero late-variable
multiplier `b^(i+1)` for which `b^(i+1) E^(i) G` belongs to the original
ideal.  It then takes a finite ideal basis and multiplies its finitely many
denominators to obtain one denominator working for the whole stage ideal.

The generic lemmas below make that finite common-denominator step explicit.
The source-shaped declarations then use the already formalized literal stage
submonoid and ground ideal.  They treat `E` as a supplied integral polynomial;
they do not construct or normalize Hentzelt's historical `E^(i)`, identify a
selected Smith coefficient with it, identify a determinant product with
`R^(i)`, perform the later-stage iteration of lines 13374--13380, or prove
equation (34).
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open scoped BigOperators

namespace SatzVIIIOneStageDescent

section Generic

variable {R : Type*} [CommRing R]

/-- The product of a selected denominator for every member of a finite basis
is again an allowed denominator.  This is the multiplicative-set part of the
finite-basis argument after equation (33). -/
theorem selectedCommonMultiplier_mem
    (M : Submonoid R) (s : Finset R) (b : R → R)
    (hb : ∀ x ∈ s, b x ∈ M) :
    (∏ x ∈ s, b x) ∈ M := by
  exact M.prod_mem fun x hx ↦ hb x hx

/-- If each selected basis denominator kills `e * x` modulo `I`, their product
kills `e * g` for every `g` in the ideal spanned by that basis. -/
theorem selectedCommonMultiplier_mul_mem_span
    (I : Ideal R) (s : Finset R) (e : R) (b : R → R)
    (hb : ∀ x ∈ s, b x * (e * x) ∈ I) :
    ∀ g ∈ Ideal.span (↑s : Set R),
      (∏ x ∈ s, b x) * e * g ∈ I := by
  let c : R := ∏ x ∈ s, b x
  have hspan : Ideal.span (↑s : Set R) ≤ I.colon (Ideal.span ({c * e} : Set R)) := by
    refine Ideal.span_le.2 ?_
    intro x hx
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem b hx
    have hmem := I.mul_mem_left d (hb x hx)
    apply (Ideal.mem_colon_span_singleton
      (I := I) (x := c * e) (r := x)).2
    simpa [c, hd, mul_assoc, mul_comm, mul_left_comm] using hmem
  intro g hg
  have hg' := (Ideal.mem_colon_span_singleton
    (I := I) (x := c * e) (r := g)).1 (hspan hg)
  simpa [c, mul_assoc, mul_comm, mul_left_comm] using hg'

/-- Finite common-denominator packaging: pointwise denominator witnesses on a
finite ideal basis yield one multiplier in `M` that works on the entire ideal.
-/
theorem exists_commonMultiplier_mul_mem_span
    (M : Submonoid R) (I : Ideal R) (s : Finset R) (e : R)
    (h : ∀ x ∈ s, ∃ b : R, b ∈ M ∧ b * (e * x) ∈ I) :
    ∃ c : R, c ∈ M ∧
      ∀ g ∈ Ideal.span (↑s : Set R), c * e * g ∈ I := by
  classical
  let b : R → R := fun x ↦
    if hx : x ∈ s then Classical.choose (h x hx) else 1
  have hb (x : R) (hx : x ∈ s) :
      b x ∈ M ∧ b x * (e * x) ∈ I := by
    simpa [b, hx] using Classical.choose_spec (h x hx)
  refine ⟨∏ x ∈ s, b x, selectedCommonMultiplier_mem M s b ?_, ?_⟩
  · intro x hx
    exact (hb x hx).1
  · exact selectedCommonMultiplier_mul_mem_span I s e b fun x hx ↦ (hb x hx).2

/-- Elementwise denominator witnesses are exactly what is needed to place
`e * g` in the localization-contraction ground ideal. -/
theorem mul_mem_groundIdealAlong_of_exists_multiplier
    (M : Submonoid R) (I : Ideal R) (e g : R)
    (h : ∃ b : R, b ∈ M ∧ b * (e * g) ∈ I) :
    e * g ∈ groundIdealAlong M I := by
  rw [mem_groundIdealAlong_iff]
  exact h

end Generic

section P22

variable {P : Type*} [Field P]
variable {n : ℕ}

/-- Source-shaped equation-(33) hypothesis at zero-based stage `cutoff`.

The historical `E^(i)` is represented by the supplied polynomial `e`.  The
multiplier is typed by Definition V's literal nonzero late-variable submonoid.
-/
def HasEquation33Witness
    (I : Ideal (MvPolynomial (Fin n) P)) (cutoff : ℕ)
    (e : MvPolynomial (Fin n) P) : Prop :=
  ∀ g ∈ stageGroundIdeal (S := P) cutoff I,
    ∃ b : MvPolynomial (Fin n) P,
      b ∈ nonzeroLateVariableSubmonoid (S := P) (n := n) (cutoff + 1) ∧
      b * (e * g) ∈ I

/-- Equation (33) descends one stage: its supplied denominator witness says
exactly that `e * g` belongs to the next ground ideal. -/
theorem equation33_mem_succStageGroundIdeal
    (I : Ideal (MvPolynomial (Fin n) P)) (cutoff : ℕ)
    (e : MvPolynomial (Fin n) P)
    (h : HasEquation33Witness I cutoff e)
    {g : MvPolynomial (Fin n) P}
    (hg : g ∈ stageGroundIdeal (S := P) cutoff I) :
    e * g ∈ stageGroundIdeal (S := P) (cutoff + 1) I := by
  obtain ⟨b, hb, hbmem⟩ := h g hg
  rw [mem_stageGroundIdeal_iff]
  exact ⟨b, hb.1, hb.2, hbmem⟩

/-- Ideal-theoretic form of the one-stage conclusion printed after equation
(33): `(e) * g_cutoff ≤ g_(cutoff+1)` in modern inclusion order. -/
theorem equation33_span_mul_le_succStageGroundIdeal
    (I : Ideal (MvPolynomial (Fin n) P)) (cutoff : ℕ)
    (e : MvPolynomial (Fin n) P)
    (h : HasEquation33Witness I cutoff e) :
    Ideal.span ({e} : Set (MvPolynomial (Fin n) P)) *
        stageGroundIdeal (S := P) cutoff I ≤
      stageGroundIdeal (S := P) (cutoff + 1) I := by
  rw [Ideal.span_singleton_mul_le_iff]
  intro g hg
  exact equation33_mem_succStageGroundIdeal I cutoff e h hg

/-- The finite-basis uniformization following equation (33): one nonzero
late-variable polynomial works for every element of the current ground ideal.
-/
theorem exists_equation33_commonMultiplier
    (I : Ideal (MvPolynomial (Fin n) P)) (cutoff : ℕ)
    (e : MvPolynomial (Fin n) P)
    (s : Finset (MvPolynomial (Fin n) P))
    (hs : Ideal.span (↑s : Set (MvPolynomial (Fin n) P)) =
      stageGroundIdeal (S := P) cutoff I)
    (h : HasEquation33Witness I cutoff e) :
    ∃ c : MvPolynomial (Fin n) P,
      c ∈ nonzeroLateVariableSubmonoid (S := P) (n := n) (cutoff + 1) ∧
      ∀ g ∈ stageGroundIdeal (S := P) cutoff I,
        c * e * g ∈ I := by
  have hbasis : ∀ x ∈ s,
      ∃ b : MvPolynomial (Fin n) P,
        b ∈ nonzeroLateVariableSubmonoid (S := P) (n := n) (cutoff + 1) ∧
        b * (e * x) ∈ I := by
    intro x hx
    apply h x
    rw [← hs]
    exact Ideal.subset_span hx
  obtain ⟨c, hc, hcall⟩ := exists_commonMultiplier_mul_mem_span
    (nonzeroLateVariableSubmonoid (S := P) (n := n) (cutoff + 1)) I s e hbasis
  refine ⟨c, hc, ?_⟩
  intro g hg
  apply hcall g
  rwa [hs]

/-- Polynomial rings over the source field are Noetherian, so the finite
basis used in the paragraph after equation (33) need not be supplied by the
caller.  One common late-variable denominator exists for the whole stage
ground ideal. -/
theorem exists_equation33_commonMultiplier_noetherian
    (I : Ideal (MvPolynomial (Fin n) P)) (cutoff : ℕ)
    (e : MvPolynomial (Fin n) P)
    (h : HasEquation33Witness I cutoff e) :
    ∃ c : MvPolynomial (Fin n) P,
      c ∈ nonzeroLateVariableSubmonoid (S := P) (n := n) (cutoff + 1) ∧
      ∀ g ∈ stageGroundIdeal (S := P) cutoff I,
        c * e * g ∈ I := by
  classical
  obtain ⟨m, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (stageGroundIdeal (S := P) cutoff I))
  let s : Finset (MvPolynomial (Fin n) P) := Finset.univ.image f
  have hsRange : (↑s : Set (MvPolynomial (Fin n) P)) = Set.range f := by
    ext x
    simp [s]
  have hs : Ideal.span (↑s : Set (MvPolynomial (Fin n) P)) =
      stageGroundIdeal (S := P) cutoff I := by
    rw [hsRange]
    exact hf
  exact exists_equation33_commonMultiplier I cutoff e s hs h

/-- At the first stage, the nonzero-ideal hypothesis makes `g₀ = ⊤`; equation
(33) therefore gives the printed first-stage conclusion `e ∈ g₁`. -/
theorem equation33_firstStage_mem
    (I : Ideal (MvPolynomial (Fin n) P)) (hI : I ≠ ⊥)
    (e : MvPolynomial (Fin n) P)
    (h : HasEquation33Witness I 0 e) :
    e ∈ stageGroundIdeal (S := P) 1 I := by
  have hOne : (1 : MvPolynomial (Fin n) P) ∈
      stageGroundIdeal (S := P) 0 I := by
    rw [(RegularIdealDecomposition.stageGroundIdeal_zero_eq_top_iff I).2 hI]
    simp
  simpa using equation33_mem_succStageGroundIdeal I 0 e h hOne

end P22

#print axioms selectedCommonMultiplier_mem
#print axioms selectedCommonMultiplier_mul_mem_span
#print axioms exists_commonMultiplier_mul_mem_span
#print axioms mul_mem_groundIdealAlong_of_exists_multiplier
#print axioms HasEquation33Witness
#print axioms equation33_mem_succStageGroundIdeal
#print axioms equation33_span_mul_le_succStageGroundIdeal
#print axioms exists_equation33_commonMultiplier
#print axioms exists_equation33_commonMultiplier_noetherian
#print axioms equation33_firstStage_mem

end SatzVIIIOneStageDescent

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
