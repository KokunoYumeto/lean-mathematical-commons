/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Ideal.Span

/-!
# A finite-minor determinantal-ideal scaffold

This file records only the elementary finite-matrix object needed for a later
formalization of the determinantal language in the Noether/Hentzelt corpus.
For a matrix `A`, a `k`-minor is represented by the determinant of a `k × k`
submatrix, and the corresponding ideal is the ideal spanned by all such
values.  Row and column selections are functions `Fin k → _`; this keeps the
definition total (selections with repeated indices simply give zero when the
determinant alternation applies).

The definitions here are deliberately source-neutral.  They do not define a
Fitting ideal, identify a module norm, assert a Cauchy--Binet theorem, or make
any claim about Noether's historical `R^(2)` or about canonical choices.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

namespace DeterminantalIdealScaffold

noncomputable section

variable {R m n : Type*}
variable [CommRing R]

/-- The determinant of the `k × k` submatrix selected by row map `r` and
column map `c`.

Using maps rather than embeddings is intentional: the definition is total for
all selections, and repeated rows or columns are handled by determinant
alternation rather than by a side condition in the definition.
-/
def kMinor (A : Matrix m n R) (k : ℕ) (r : Fin k → m) (c : Fin k → n) : R :=
  (A.submatrix r c).det

/-- The ideal spanned by all finite `k`-minors of `A`.

This is a scaffold definition only; no presentation- or Fitting-ideal
interpretation is bundled with it.
-/
def determinantalIdeal (A : Matrix m n R) (k : ℕ) : Ideal R :=
  Ideal.span (Set.range fun rc : (Fin k → m) × (Fin k → n) =>
    kMinor A k rc.1 rc.2)

@[simp]
theorem kMinor_apply (A : Matrix m n R) (k : ℕ) (r : Fin k → m) (c : Fin k → n) :
    kMinor A k r c = (A.submatrix r c).det :=
  rfl

/-- Every selected minor is a generator of the determinantal ideal. -/
theorem kMinor_mem_determinantalIdeal
    (A : Matrix m n R) (k : ℕ) (r : Fin k → m) (c : Fin k → n) :
    kMinor A k r c ∈ determinantalIdeal A k := by
  simpa only [determinantalIdeal] using
    (Ideal.mem_span_range_self
      (f := fun rc : (Fin k → m) × (Fin k → n) => kMinor A k rc.1 rc.2)
      (x := (r, c)))

/-- A repeated row makes a selected minor vanish. -/
theorem kMinor_eq_zero_of_row_eq
    (A : Matrix m n R) (k : ℕ) (r : Fin k → m) (c : Fin k → n)
    {i j : Fin k} (hij : i ≠ j) (hrows : r i = r j) :
    kMinor A k r c = 0 := by
  unfold kMinor
  apply Matrix.det_zero_of_row_eq hij
  funext l
  simp [hrows]

/-- A repeated column makes a selected minor vanish. -/
theorem kMinor_eq_zero_of_column_eq
    (A : Matrix m n R) (k : ℕ) (r : Fin k → m) (c : Fin k → n)
    {i j : Fin k} (hij : i ≠ j) (hcols : c i = c j) :
    kMinor A k r c = 0 := by
  unfold kMinor
  apply Matrix.det_zero_of_column_eq hij
  intro l
  simp [hcols]

/-- If every selected `k`-minor vanishes, the determinantal ideal is bottom. -/
theorem determinantalIdeal_eq_bot_of_forall_kMinor_eq_zero
    (A : Matrix m n R) (k : ℕ)
    (hzero : ∀ (r : Fin k → m) (c : Fin k → n), kMinor A k r c = 0) :
    determinantalIdeal A k = ⊥ := by
  rw [determinantalIdeal, Ideal.span_eq_bot]
  rintro x ⟨rc, rfl⟩
  exact hzero rc.1 rc.2

/-- For positive `k`, every minor of the zero matrix vanishes. -/
theorem kMinor_zero_of_pos
    (k : ℕ) (hk : 0 < k) (r : Fin k → m) (c : Fin k → n) :
    kMinor (0 : Matrix m n R) k r c = 0 := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  unfold kMinor
  change (0 : Matrix (Fin k) (Fin k) R).det = 0
  exact Matrix.det_zero (inferInstance : Nonempty (Fin k))

/-- The zero matrix has bottom determinantal ideal in every positive degree. -/
theorem determinantalIdeal_zero_of_pos
    (k : ℕ) (hk : 0 < k) :
    determinantalIdeal (0 : Matrix m n R) k = ⊥ := by
  apply determinantalIdeal_eq_bot_of_forall_kMinor_eq_zero
  intro r c
  exact kMinor_zero_of_pos k hk r c

/-- In degree zero the unique empty minor is `1`, so the ideal is top. -/
theorem determinantalIdeal_zeroDegree (A : Matrix m n R) :
    determinantalIdeal A 0 = ⊤ := by
  apply (Ideal.eq_top_iff_one _).2
  let r : Fin 0 → m := fun i => Fin.elim0 i
  let c : Fin 0 → n := fun i => Fin.elim0 i
  have hminor : kMinor A 0 r c = 1 := by
    unfold kMinor
    exact Matrix.det_fin_zero
  rw [← hminor]
  exact kMinor_mem_determinantalIdeal A 0 r c

end

end DeterminantalIdealScaffold

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

#print axioms MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.DeterminantalIdealScaffold.kMinor
#print axioms MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.DeterminantalIdealScaffold.determinantalIdeal
#print axioms MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.DeterminantalIdealScaffold.kMinor_apply
#print axioms MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.DeterminantalIdealScaffold.kMinor_mem_determinantalIdeal
#print axioms MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.DeterminantalIdealScaffold.kMinor_eq_zero_of_row_eq
#print axioms MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.DeterminantalIdealScaffold.kMinor_eq_zero_of_column_eq
#print axioms MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.DeterminantalIdealScaffold.determinantalIdeal_eq_bot_of_forall_kMinor_eq_zero
#print axioms MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.DeterminantalIdealScaffold.kMinor_zero_of_pos
#print axioms MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.DeterminantalIdealScaffold.determinantalIdeal_zero_of_pos
#print axioms MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.DeterminantalIdealScaffold.determinantalIdeal_zeroDegree
