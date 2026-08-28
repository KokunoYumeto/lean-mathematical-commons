import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.FirstSmithCommonTail
import Mathlib.RingTheory.Ideal.Colon

/-!
# Hentzelt--Noether equation (24): scalar quotients of the first Smith pair

Module for P22, controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
lines 13164--13179.

The slash in the displayed formulas after equation (24) is historical
module-ideal quotient notation.  In this file it is interpreted explicitly as
Mathlib's `Submodule.colon`: `A.colon (B : Set E)` is the ideal of scalars `r`
such that `r • B <= A`.

For a finite diagonal presentation

`N = (e_i • eta_i)_i <= G = (eta_i)_i`,

put `D(s) = N sup span {eta_i | i in s}`.  The generic core below proves

* membership in `N` is coordinatewise divisibility by the `e_i`;
* `D(s).colon D(insert i s) = (e_i)` when `i` is not already in `s`; and
* `D(s).colon G` is the infimum of the principal ideals `(e_j)` over the
  coordinates not in `s`.

Consequently the source's unconditional formula
`M_1 / (M_1, eta_i) = (e_i)` is valid in the restored common-tail model.  By
contrast, replacing `(M_1, eta_i)` by all of `G_1` gives a single `(e_i)` only
when that coefficient is explicitly assumed divisible by every remaining
coefficient.  The theorem type records this hypothesis; Mathlib v4.31's Smith
API does not prove it for the selected coefficients.

No divisibility ordering, normalized or canonical invariant factors,
resultant identification, determinant norm, primitive normalization, or
choice-independence statement is made here.  The arbitrary tail is a freely
adjoined common identity tail, as in `FirstSmithCommonTail`; identifying it
with the historical unbounded zeta module remains separate work.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open Module MvPolynomial

namespace SmithScalarQuotients

noncomputable section

variable {ι R E F : Type*}
variable [CommSemiring R]
variable [AddCommGroup E] [Module R E]

/-- The span of the displayed basis vectors whose indices lie in `s`. -/
def basisFinsetSpan (b : Basis ι R E) (s : Finset ι) : Submodule R E :=
  Submodule.span R ((fun i => b i) '' (s : Set ι))

/-- The finite Smith filtration `D(s) = N + (eta_i | i in s)`. -/
def filtration (N : Submodule R E) (b : Basis ι R E) (s : Finset ι) :
    Submodule R E :=
  N ⊔ basisFinsetSpan b s

/-- A vector belongs to the span of a finite subset of a basis exactly when
all coordinates outside that subset vanish. -/
theorem mem_basisFinsetSpan_iff [Fintype ι]
    (b : Basis ι R E) (s : Finset ι) (x : E) :
    x ∈ basisFinsetSpan b s ↔
      ∀ i, i ∉ s → b.repr x i = 0 := by
  constructor
  · intro hx i hi
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨j, hj, rfl⟩
        have hji : j ≠ i := fun hji => hi (hji ▸ hj)
        simp [Basis.repr_self, hji]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  · intro hx
    rw [← b.sum_repr x]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : i ∈ s
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨i, hi, rfl⟩)
    · rw [hx i hi, zero_smul]
      exact Submodule.zero_mem _

/-- Diagonal-basis membership: if the displayed basis of `N` maps to
`e_i • eta_i` in the ambient basis, then membership in `N` is equivalent to
coordinatewise divisibility by `e_i`. -/
theorem mem_iff_dvd_of_diagonal_bases
    [Fintype ι]
    (N : Submodule R E) (b : Basis ι R E) (bN : Basis ι R N)
    (e : ι → R) (hdiag : ∀ i, (bN i : E) = e i • b i) (x : E) :
    x ∈ N ↔ ∀ i, e i ∣ b.repr x i := by
  simp_rw [bN.mem_submodule_iff', hdiag]
  have hrepr : ∀ (c : ι → R) (i),
      b.repr (∑ j : ι, c j • e j • b j) i = e i * c i := by
    intro c i
    simp only [← mul_smul, b.repr_sum_self, mul_comm]
  constructor
  · rintro ⟨c, rfl⟩ i
    exact ⟨c i, hrepr c i⟩
  · rintro h
    choose c hc using h
    exact ⟨c, b.ext_elem fun i => Eq.trans (hc i) (hrepr c i).symm⟩

/-- Coordinate criterion for the Smith filtration: the coordinates already
adjoined in `s` are unrestricted and every remaining coordinate is divisible
by its diagonal coefficient. -/
theorem mem_filtration_iff
    [Fintype ι]
    (N : Submodule R E) (b : Basis ι R E) (e : ι → R)
    (hN : ∀ x, x ∈ N ↔ ∀ i, e i ∣ b.repr x i)
    (s : Finset ι) (x : E) :
    x ∈ filtration N b s ↔
      ∀ i, i ∉ s → e i ∣ b.repr x i := by
  have hrepr : ∀ (c : ι → R) (i),
      b.repr (∑ j : ι, c j • e j • b j) i = e i * c i := by
    intro c i
    simp only [← mul_smul, b.repr_sum_self, mul_comm]
  constructor
  · intro hx i hi
    obtain ⟨y, hy, z, hz, rfl⟩ := (Submodule.mem_sup.mp hx)
    have hz0 : b.repr z i = 0 :=
      (mem_basisFinsetSpan_iff b s z).mp hz i hi
    simpa [hz0] using (hN y).mp hy i
  · intro hx
    classical
    let c : ι → R := fun i =>
      if hi : i ∈ s then 0 else (hx i hi).choose
    have hc (i : ι) (hi : i ∉ s) :
        b.repr x i = e i * c i := by
      rw [show c i = (hx i hi).choose by simp [c, hi]]
      exact (hx i hi).choose_spec
    let y : E := ∑ i : ι, c i • e i • b i
    have hyrepr (i : ι) : b.repr y i = e i * c i := by
      simpa [y] using hrepr c i
    have hy : y ∈ N := by
      apply (hN y).mpr
      intro i
      exact ⟨c i, hyrepr i⟩
    let z : E := ∑ i ∈ s, b.repr x i • b i
    have hz : z ∈ basisFinsetSpan b s := by
      dsimp [z]
      apply Submodule.sum_mem
      intro i hi
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨i, hi, rfl⟩)
    have hzrepr (i : ι) :
        b.repr z i = if i ∈ s then b.repr x i else 0 := by
      simp [z, Basis.repr_self, Finsupp.single_apply,
        Finset.sum_ite_eq']
    have hyz : y + z = x := by
      apply b.ext_elem
      intro i
      rw [map_add]
      change b.repr y i + b.repr z i = b.repr x i
      rw [hyrepr, hzrepr]
      by_cases hi : i ∈ s
      · simp [c, hi]
      · rw [hc i hi]
        simp [hi]
    apply Submodule.mem_sup.mpr
    exact ⟨y, hy, z, hz, hyz⟩

@[simp]
theorem filtration_empty (N : Submodule R E) (b : Basis ι R E) :
    filtration N b ∅ = N := by
  simp [filtration, basisFinsetSpan]

/-- Every selected basis vector belongs to the corresponding filtration
stage. -/
theorem basis_mem_filtration (N : Submodule R E) (b : Basis ι R E)
    (s : Finset ι) {i : ι} (hi : i ∈ s) :
    b i ∈ filtration N b s := by
  apply Submodule.mem_sup_right
  exact Submodule.subset_span ⟨i, hi, rfl⟩

/-- The one-step historical scalar quotient.  No ordering of the `e_i` is
needed: adjoining one new basis vector isolates its own principal ideal. -/
theorem filtration_colon_insert_eq_span
    [Fintype ι] [DecidableEq ι]
    (N : Submodule R E) (b : Basis ι R E) (e : ι → R)
    (hN : ∀ x, x ∈ N ↔ ∀ i, e i ∣ b.repr x i)
    (s : Finset ι) (i : ι) (hi : i ∉ s) :
    (filtration N b s).colon
        ((filtration N b (insert i s) : Submodule R E) : Set E) =
      Ideal.span ({e i} : Set R) := by
  classical
  ext r
  constructor
  · intro hr
    have hrbi := (Submodule.mem_colon.mp hr) (b i)
      (basis_mem_filtration N b (insert i s) (Finset.mem_insert_self i s))
    have hdvd := (mem_filtration_iff N b e hN s (r • b i)).mp hrbi i hi
    apply Ideal.mem_span_singleton.mpr
    simpa using hdvd
  · intro hr
    apply Submodule.mem_colon.mpr
    intro x hx
    apply (mem_filtration_iff N b e hN s (r • x)).mpr
    intro j hj
    have hrepr : b.repr (r • x) j = r * b.repr x j := by simp
    rw [hrepr]
    by_cases hji : j = i
    · subst j
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hr
      refine ⟨c * b.repr x i, ?_⟩
      rw [hc]
      ac_rfl
    · have hjinsert : j ∉ insert i s := by simp [hji, hj]
      have hxj := (mem_filtration_iff N b e hN (insert i s) x).mp hx j hjinsert
      obtain ⟨c, hc⟩ := hxj
      refine ⟨r * c, ?_⟩
      rw [hc]
      ac_rfl

/-- The scalar quotient by the whole basis module is the intersection of the
principal ideals attached to the coordinates not yet adjoined. -/
theorem filtration_colon_top_eq_iInf
    [Fintype ι]
    (N : Submodule R E) (b : Basis ι R E) (e : ι → R)
    (hN : ∀ x, x ∈ N ↔ ∀ i, e i ∣ b.repr x i)
    (s : Finset ι) :
    (filtration N b s).colon ((⊤ : Submodule R E) : Set E) =
      ⨅ j : {j : ι // j ∉ s}, Ideal.span ({e j.1} : Set R) := by
  ext r
  constructor
  · intro hr
    apply Ideal.mem_iInf.mpr
    intro j
    apply Ideal.mem_span_singleton.mpr
    have hrbj := (Submodule.mem_colon.mp hr) (b j.1) (Submodule.mem_top)
    have hdvd :=
      (mem_filtration_iff N b e hN s (r • b j.1)).mp hrbj j.1 j.2
    simpa using hdvd
  · intro hr
    apply Submodule.mem_colon.mpr
    intro x _
    apply (mem_filtration_iff N b e hN s (r • x)).mpr
    intro i hi
    have hri : e i ∣ r := Ideal.mem_span_singleton.mp
      (Ideal.mem_iInf.mp hr ⟨i, hi⟩)
    obtain ⟨c, hc⟩ := hri
    have hrepr : b.repr (r • x) i = r * b.repr x i := by simp
    rw [hrepr, hc]
    exact ⟨c * b.repr x i, by
      simp [mul_assoc, mul_comm, mul_left_comm]⟩

/-- `i` is a greatest remaining Smith divisor when it is not yet adjoined
and every other remaining coefficient divides `e_i`.  This is an explicit
hypothesis, not data supplied by Mathlib's selected Smith bases. -/
def IsGreatestRemainingDivisor (e : ι → R) (s : Finset ι) (i : ι) : Prop :=
  i ∉ s ∧ ∀ j, j ∉ s → e j ∣ e i

/-- If one remaining coefficient is divisible by every other remaining
coefficient, the infimum of their principal ideals is its principal ideal. -/
theorem iInf_remaining_eq_span_of_isGreatest
    (e : ι → R) (s : Finset ι) (i : ι)
    (h : IsGreatestRemainingDivisor e s i) :
    (⨅ j : {j : ι // j ∉ s}, Ideal.span ({e j.1} : Set R)) =
      Ideal.span ({e i} : Set R) := by
  apply le_antisymm
  · exact iInf_le _ (⟨i, h.1⟩ : {j : ι // j ∉ s})
  · apply le_iInf
    intro j
    exact Ideal.span_singleton_le_span_singleton.mpr (h.2 j.1 j.2)

/-- Conditional simplification of `D(s) / G` to one displayed principal
ideal.  The greatest-divisor hypothesis is deliberately visible. -/
theorem filtration_colon_top_eq_span_of_isGreatest
    [Fintype ι]
    (N : Submodule R E) (b : Basis ι R E) (e : ι → R)
    (hN : ∀ x, x ∈ N ↔ ∀ i, e i ∣ b.repr x i)
    (s : Finset ι) (i : ι)
    (h : IsGreatestRemainingDivisor e s i) :
    (filtration N b s).colon ((⊤ : Submodule R E) : Set E) =
      Ideal.span ({e i} : Set R) := by
  rw [filtration_colon_top_eq_iInf N b e hN s,
    iInf_remaining_eq_span_of_isGreatest e s i h]

variable [AddCommGroup F] [Module R F]

/-- Adjoining one head vector to a product with a full common tail is exactly
the product of the corresponding head enlargement with that same full tail. -/
theorem prod_top_sup_span_singleton_eq
    (A : Submodule R E) (x : E) :
    A.prod (⊤ : Submodule R F) ⊔
        Submodule.span R ({(x, 0)} : Set (E × F)) =
      (A ⊔ Submodule.span R ({x} : Set E)).prod
        (⊤ : Submodule R F) := by
  apply le_antisymm
  · apply sup_le
    · exact Submodule.prod_mono le_sup_left le_rfl
    · rw [Submodule.span_le]
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst y
      exact ⟨Submodule.mem_sup_right (Submodule.subset_span (by simp)),
        Submodule.mem_top⟩
  · intro y hy
    obtain ⟨a, ha, z, hz, haz⟩ := Submodule.mem_sup.mp hy.1
    have hzpair : (z, 0) ∈ Submodule.span R ({(x, 0)} : Set (E × F)) := by
      have hzimage := Submodule.apply_mem_span_image_of_mem_span
        (LinearMap.inl R E F) hz
      simpa [LinearMap.inl_apply] using hzimage
    have hapair : (a, y.2) ∈ A.prod (⊤ : Submodule R F) :=
      ⟨ha, Submodule.mem_top⟩
    have hsum : (a, y.2) + (z, 0) ∈
        A.prod (⊤ : Submodule R F) ⊔
          Submodule.span R ({(x, 0)} : Set (E × F)) :=
      Submodule.add_mem_sup hapair hzpair
    change (y.1, y.2) ∈ _
    rw [← haz]
    simpa using hsum

/-- A common full second factor cancels from a colon ideal. -/
theorem prod_top_colon_prod_top (A B : Submodule R E) :
    (A.prod (⊤ : Submodule R F)).colon
        (((B.prod (⊤ : Submodule R F)) : Submodule R (E × F)) : Set (E × F)) =
      A.colon (B : Set E) := by
  ext r
  constructor
  · intro hr
    apply Submodule.mem_colon.mpr
    intro x hx
    have hpair := (Submodule.mem_colon.mp hr) (x, 0) ⟨hx, Submodule.mem_top⟩
    exact hpair.1
  · intro hr
    apply Submodule.mem_colon.mpr
    intro x hx
    exact ⟨(Submodule.mem_colon.mp hr) x.1 hx.1, Submodule.mem_top⟩

/-- Product-tail form of cancelling the common full second factor when the
right-hand module is the whole ambient module. -/
theorem prod_top_colon_top (A : Submodule R E) :
    (A.prod (⊤ : Submodule R F)).colon
        ((⊤ : Submodule R (E × F)) : Set (E × F)) =
      A.colon ((⊤ : Submodule R E) : Set E) := by
  rw [show (⊤ : Submodule R (E × F)) =
      (⊤ : Submodule R E).prod (⊤ : Submodule R F) by
        ext y
        simp]
  exact prod_top_colon_prod_top (F := F) A ⊤

#print axioms basisFinsetSpan
#print axioms filtration
#print axioms mem_basisFinsetSpan_iff
#print axioms mem_iff_dvd_of_diagonal_bases
#print axioms mem_filtration_iff
#print axioms filtration_empty
#print axioms basis_mem_filtration
#print axioms filtration_colon_insert_eq_span
#print axioms filtration_colon_top_eq_iInf
#print axioms IsGreatestRemainingDivisor
#print axioms iInf_remaining_eq_span_of_isGreatest
#print axioms filtration_colon_top_eq_span_of_isGreatest
#print axioms prod_top_sup_span_singleton_eq
#print axioms prod_top_colon_prod_top
#print axioms prod_top_colon_top

end

end SmithScalarQuotients

namespace RegularIdealDecomposition

noncomputable section

variable {P : Type*} [Field P]
variable {n : ℕ}

/-- Membership in the actual localized relative denominator `M_1*` is
coordinatewise divisibility by the selected Smith coefficients. -/
theorem localizedSecondVariable_mem_denominatorCarrier_iff_dvd
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (x : localizedSecondVariableGroundCarrier I k) :
    x ∈ localizedSecondVariableDenominatorCarrier I k ↔
      ∀ i : localizedSecondVariableSmithIndex I k,
        localizedSecondVariableSmithCoefficients I k i ∣
          (localizedSecondVariableEtaBasis I k).repr x i := by
  exact SmithScalarQuotients.mem_iff_dvd_of_diagonal_bases
    (R := secondVariablePID P n)
    (E := localizedSecondVariableGroundCarrier I k)
    (ι := localizedSecondVariableSmithIndex I k)
    (localizedSecondVariableDenominatorCarrier I k)
    (localizedSecondVariableEtaBasis I k)
    (localizedSecondVariableDenominatorBasis I k)
    (localizedSecondVariableSmithCoefficients I k)
    (fun i => localizedSecondVariableDenominatorBasis_eq_smul_eta I k i)
    x

/-- The actual finite localized filtration
`D(s) = M_1* + (eta_i | i in s)`. -/
def localizedSecondVariableSmithFiltration
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (s : Finset (localizedSecondVariableSmithIndex I k)) :
    Submodule (secondVariablePID P n)
      (localizedSecondVariableGroundCarrier I k) :=
  SmithScalarQuotients.filtration
    (R := secondVariablePID P n)
    (E := localizedSecondVariableGroundCarrier I k)
    (ι := localizedSecondVariableSmithIndex I k)
    (localizedSecondVariableDenominatorCarrier I k)
    (localizedSecondVariableEtaBasis I k) s

/-- Coordinate criterion for the actual first localized filtration. -/
theorem localizedSecondVariable_mem_SmithFiltration_iff
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (s : Finset (localizedSecondVariableSmithIndex I k))
    (x : localizedSecondVariableGroundCarrier I k) :
    x ∈ localizedSecondVariableSmithFiltration I k s ↔
      ∀ i, i ∉ s →
          localizedSecondVariableSmithCoefficients I k i ∣
          (localizedSecondVariableEtaBasis I k).repr x i := by
  simpa only [localizedSecondVariableSmithFiltration] using
    (SmithScalarQuotients.mem_filtration_iff
      (R := secondVariablePID P n)
      (E := localizedSecondVariableGroundCarrier I k)
      (ι := localizedSecondVariableSmithIndex I k)
      (localizedSecondVariableDenominatorCarrier I k)
      (localizedSecondVariableEtaBasis I k)
      (localizedSecondVariableSmithCoefficients I k)
      (localizedSecondVariable_mem_denominatorCarrier_iff_dvd I k)
      s x)

@[simp]
theorem localizedSecondVariableSmithFiltration_empty
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    localizedSecondVariableSmithFiltration I k ∅ =
      localizedSecondVariableDenominatorCarrier I k := by
  simpa only [localizedSecondVariableSmithFiltration] using
    (SmithScalarQuotients.filtration_empty
      (R := secondVariablePID P n)
      (E := localizedSecondVariableGroundCarrier I k)
      (ι := localizedSecondVariableSmithIndex I k)
      (localizedSecondVariableDenominatorCarrier I k)
      (localizedSecondVariableEtaBasis I k))

/-- Finite source form of `D(s) / D(insert i s) = (e_i)`. -/
theorem localizedSecondVariableSmithFiltration_colon_insert_eq_span
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (s : Finset (localizedSecondVariableSmithIndex I k))
    (i : localizedSecondVariableSmithIndex I k) (hi : i ∉ s) :
    (localizedSecondVariableSmithFiltration I k s).colon
        ((localizedSecondVariableSmithFiltration I k (insert i s) :
          Submodule (secondVariablePID P n)
            (localizedSecondVariableGroundCarrier I k)) :
          Set (localizedSecondVariableGroundCarrier I k)) =
      Ideal.span ({localizedSecondVariableSmithCoefficients I k i} :
        Set (secondVariablePID P n)) := by
  simpa only [localizedSecondVariableSmithFiltration] using
    (SmithScalarQuotients.filtration_colon_insert_eq_span
      (R := secondVariablePID P n)
      (E := localizedSecondVariableGroundCarrier I k)
      (ι := localizedSecondVariableSmithIndex I k)
      (localizedSecondVariableDenominatorCarrier I k)
      (localizedSecondVariableEtaBasis I k)
      (localizedSecondVariableSmithCoefficients I k)
      (localizedSecondVariable_mem_denominatorCarrier_iff_dvd I k)
      s i hi)

/-- Finite source form of `D(s) / G_1*`: the exact answer is the infimum of
the principal ideals for coordinates not yet adjoined. -/
theorem localizedSecondVariableSmithFiltration_colon_ground_eq_iInf
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (s : Finset (localizedSecondVariableSmithIndex I k)) :
    (localizedSecondVariableSmithFiltration I k s).colon
        ((⊤ : Submodule (secondVariablePID P n)
          (localizedSecondVariableGroundCarrier I k)) :
          Set (localizedSecondVariableGroundCarrier I k)) =
      ⨅ j : {j : localizedSecondVariableSmithIndex I k // j ∉ s},
        Ideal.span ({localizedSecondVariableSmithCoefficients I k j.1} :
          Set (secondVariablePID P n)) := by
  simpa only [localizedSecondVariableSmithFiltration] using
    (SmithScalarQuotients.filtration_colon_top_eq_iInf
      (R := secondVariablePID P n)
      (E := localizedSecondVariableGroundCarrier I k)
      (ι := localizedSecondVariableSmithIndex I k)
      (localizedSecondVariableDenominatorCarrier I k)
      (localizedSecondVariableEtaBasis I k)
      (localizedSecondVariableSmithCoefficients I k)
      (localizedSecondVariable_mem_denominatorCarrier_iff_dvd I k)
      s)

/-- Source-specific spelling of the explicit greatest-remaining-divisor
hypothesis. -/
def localizedSecondVariableIsGreatestRemainingDivisor
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (s : Finset (localizedSecondVariableSmithIndex I k))
    (i : localizedSecondVariableSmithIndex I k) : Prop :=
  SmithScalarQuotients.IsGreatestRemainingDivisor
    (localizedSecondVariableSmithCoefficients I k) s i

/-- Finite conditional simplification to one distinguished `(e_i)`. -/
theorem localizedSecondVariableSmithFiltration_colon_ground_eq_span_of_greatest
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (s : Finset (localizedSecondVariableSmithIndex I k))
    (i : localizedSecondVariableSmithIndex I k)
    (h : localizedSecondVariableIsGreatestRemainingDivisor I k s i) :
    (localizedSecondVariableSmithFiltration I k s).colon
        ((⊤ : Submodule (secondVariablePID P n)
          (localizedSecondVariableGroundCarrier I k)) :
          Set (localizedSecondVariableGroundCarrier I k)) =
      Ideal.span ({localizedSecondVariableSmithCoefficients I k i} :
        Set (secondVariablePID P n)) := by
  simpa only [localizedSecondVariableSmithFiltration] using
    (SmithScalarQuotients.filtration_colon_top_eq_span_of_isGreatest
      (R := secondVariablePID P n)
      (E := localizedSecondVariableGroundCarrier I k)
      (ι := localizedSecondVariableSmithIndex I k)
      (localizedSecondVariableDenominatorCarrier I k)
      (localizedSecondVariableEtaBasis I k)
      (localizedSecondVariableSmithCoefficients I k)
      (localizedSecondVariable_mem_denominatorCarrier_iff_dvd I k)
      s i h)

/-- Restore an arbitrary common identity tail at every stage of the finite
Smith filtration. -/
def localizedSecondVariableFullSmithFiltration
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*)
    (s : Finset (localizedSecondVariableSmithIndex I k)) :
    Submodule (secondVariablePID P n)
      (localizedSecondVariableCommonTailAmbient I k tau) :=
  (localizedSecondVariableSmithFiltration I k s).prod
    (⊤ : Submodule (secondVariablePID P n)
      (tau →₀ secondVariablePID P n))

/-- The zero stage of the restored filtration is exactly the full original
module `M_1`. -/
@[simp]
theorem localizedSecondVariableFullSmithFiltration_empty
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*) :
    localizedSecondVariableFullSmithFiltration I k tau ∅ =
      localizedSecondVariableFullOriginalModule I k tau := by
  rw [localizedSecondVariableFullOriginalModule_eq_prod_top]
  simp [localizedSecondVariableFullSmithFiltration]

/-- The historical generated module `(M_1, eta_i)`, formed literally by
adjoining the displayed extended `eta_i` vector to the full original module. -/
def localizedSecondVariableFullOriginalAdjoinEta
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*)
    (i : localizedSecondVariableSmithIndex I k) :
    Submodule (secondVariablePID P n)
      (localizedSecondVariableCommonTailAmbient I k tau) :=
  localizedSecondVariableFullOriginalModule I k tau ⊔
    Submodule.span (secondVariablePID P n)
      ({localizedSecondVariableExtendedEtaBasis I k tau (Sum.inl i)} :
        Set (localizedSecondVariableCommonTailAmbient I k tau))

/-- In product coordinates, the literal module `(M_1, eta_i)` is the
singleton stage of the restored Smith filtration. -/
theorem localizedSecondVariableFullOriginalAdjoinEta_eq_filtration_singleton
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*)
    (i : localizedSecondVariableSmithIndex I k) :
    localizedSecondVariableFullOriginalAdjoinEta I k tau i =
      localizedSecondVariableFullSmithFiltration I k tau {i} := by
  unfold localizedSecondVariableFullOriginalAdjoinEta
  rw [localizedSecondVariableFullOriginalModule_eq_prod_top]
  have heta :
      localizedSecondVariableExtendedEtaBasis I k tau (Sum.inl i) =
        (localizedSecondVariableEtaBasis I k i, 0) := by
    simp [localizedSecondVariableExtendedEtaBasis]
  rw [heta]
  unfold localizedSecondVariableFullSmithFiltration
  unfold localizedSecondVariableSmithFiltration
  rw [SmithScalarQuotients.prod_top_sup_span_singleton_eq
    (R := secondVariablePID P n)
    (E := localizedSecondVariableGroundCarrier I k)
    (F := tau →₀ secondVariablePID P n)
    (localizedSecondVariableDenominatorCarrier I k)
    (localizedSecondVariableEtaBasis I k i)]
  congr 1
  simp [SmithScalarQuotients.filtration,
    SmithScalarQuotients.basisFinsetSpan]

/-- The exact full common-tail formula
`M_1 / (M_1, eta_i) = (e_i)`.  It is unconditional for every finite Smith
coordinate and every tail index type. -/
theorem localizedSecondVariableFullOriginal_colon_adjoinEta_eq_span
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*)
    (i : localizedSecondVariableSmithIndex I k) :
    (localizedSecondVariableFullOriginalModule I k tau).colon
        ((localizedSecondVariableFullOriginalAdjoinEta I k tau i :
          Submodule (secondVariablePID P n)
            (localizedSecondVariableCommonTailAmbient I k tau)) :
          Set (localizedSecondVariableCommonTailAmbient I k tau)) =
      Ideal.span ({localizedSecondVariableSmithCoefficients I k i} :
        Set (secondVariablePID P n)) := by
  rw [localizedSecondVariableFullOriginalModule_eq_prod_top,
    localizedSecondVariableFullOriginalAdjoinEta_eq_filtration_singleton]
  change
    ((localizedSecondVariableDenominatorCarrier I k).prod
      (⊤ : Submodule (secondVariablePID P n)
        (tau →₀ secondVariablePID P n))).colon
      (((localizedSecondVariableSmithFiltration I k {i}).prod
        (⊤ : Submodule (secondVariablePID P n)
          (tau →₀ secondVariablePID P n)) :
        Submodule (secondVariablePID P n)
          (localizedSecondVariableCommonTailAmbient I k tau)) :
        Set (localizedSecondVariableCommonTailAmbient I k tau)) = _
  rw [SmithScalarQuotients.prod_top_colon_prod_top
    (R := secondVariablePID P n)
    (E := localizedSecondVariableGroundCarrier I k)
    (F := tau →₀ secondVariablePID P n)
    (localizedSecondVariableDenominatorCarrier I k)
    (localizedSecondVariableSmithFiltration I k {i})]
  simpa using
    (localizedSecondVariableSmithFiltration_colon_insert_eq_span
      I k (∅ : Finset (localizedSecondVariableSmithIndex I k)) i (by simp))

/-- Exact arbitrary-tail form of `D(s) / G_1`: the tail cancels and leaves
the infimum of the remaining finite principal ideals. -/
theorem localizedSecondVariableFullSmithFiltration_colon_ground_eq_iInf
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*)
    (s : Finset (localizedSecondVariableSmithIndex I k)) :
    (localizedSecondVariableFullSmithFiltration I k tau s).colon
        ((localizedSecondVariableFullGroundModule I k tau :
          Submodule (secondVariablePID P n)
            (localizedSecondVariableCommonTailAmbient I k tau)) :
          Set (localizedSecondVariableCommonTailAmbient I k tau)) =
      ⨅ j : {j : localizedSecondVariableSmithIndex I k // j ∉ s},
        Ideal.span ({localizedSecondVariableSmithCoefficients I k j.1} :
          Set (secondVariablePID P n)) := by
  rw [localizedSecondVariableFullGroundModule_eq_top]
  change
    ((localizedSecondVariableSmithFiltration I k s).prod
      (⊤ : Submodule (secondVariablePID P n)
        (tau →₀ secondVariablePID P n))).colon
      ((⊤ : Submodule (secondVariablePID P n)
        (localizedSecondVariableCommonTailAmbient I k tau)) :
        Set (localizedSecondVariableCommonTailAmbient I k tau)) = _
  rw [SmithScalarQuotients.prod_top_colon_top
    (R := secondVariablePID P n)
    (E := localizedSecondVariableGroundCarrier I k)
    (F := tau →₀ secondVariablePID P n)
    (localizedSecondVariableSmithFiltration I k s)]
  exact localizedSecondVariableSmithFiltration_colon_ground_eq_iInf I k s

/-- Conditional arbitrary-tail simplification of the preceding infimum to a
distinguished `(e_i)`. -/
theorem localizedSecondVariableFullSmithFiltration_colon_ground_eq_span_of_greatest
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*)
    (s : Finset (localizedSecondVariableSmithIndex I k))
    (i : localizedSecondVariableSmithIndex I k)
    (h : localizedSecondVariableIsGreatestRemainingDivisor I k s i) :
    (localizedSecondVariableFullSmithFiltration I k tau s).colon
        ((localizedSecondVariableFullGroundModule I k tau :
          Submodule (secondVariablePID P n)
            (localizedSecondVariableCommonTailAmbient I k tau)) :
          Set (localizedSecondVariableCommonTailAmbient I k tau)) =
      Ideal.span ({localizedSecondVariableSmithCoefficients I k i} :
        Set (secondVariablePID P n)) := by
  rw [localizedSecondVariableFullSmithFiltration_colon_ground_eq_iInf I k tau s,
    SmithScalarQuotients.iInf_remaining_eq_span_of_isGreatest
      (localizedSecondVariableSmithCoefficients I k) s i h]

/-- The printed distinguished-coefficient chain, with the missing ordering
premise exposed: `M_1 / G_1 = (e_i) = M_1 / (M_1, eta_i)`. -/
theorem localizedSecondVariableFull_distinguished_scalar_quotient_chain
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) (tau : Type*)
    (i : localizedSecondVariableSmithIndex I k)
    (h : ∀ j : localizedSecondVariableSmithIndex I k,
      localizedSecondVariableSmithCoefficients I k j ∣
        localizedSecondVariableSmithCoefficients I k i) :
    (localizedSecondVariableFullOriginalModule I k tau).colon
        ((localizedSecondVariableFullGroundModule I k tau :
          Submodule (secondVariablePID P n)
            (localizedSecondVariableCommonTailAmbient I k tau)) :
          Set (localizedSecondVariableCommonTailAmbient I k tau)) =
          Ideal.span ({localizedSecondVariableSmithCoefficients I k i} :
            Set (secondVariablePID P n)) ∧
      (localizedSecondVariableFullOriginalModule I k tau).colon
        ((localizedSecondVariableFullOriginalAdjoinEta I k tau i :
          Submodule (secondVariablePID P n)
            (localizedSecondVariableCommonTailAmbient I k tau)) :
          Set (localizedSecondVariableCommonTailAmbient I k tau)) =
          Ideal.span ({localizedSecondVariableSmithCoefficients I k i} :
            Set (secondVariablePID P n)) := by
  constructor
  · rw [← localizedSecondVariableFullSmithFiltration_empty I k tau]
    apply localizedSecondVariableFullSmithFiltration_colon_ground_eq_span_of_greatest
    exact ⟨by simp, fun j _ => h j⟩
  · exact localizedSecondVariableFullOriginal_colon_adjoinEta_eq_span I k tau i

/-- Countable-tail specialization of the restored Smith filtration. -/
abbrev localizedSecondVariableNatTailSmithFiltration
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (s : Finset (localizedSecondVariableSmithIndex I k)) :=
  localizedSecondVariableFullSmithFiltration I k ℕ s

/-- Countable-tail specialization of `(M_1, eta_i)`. -/
abbrev localizedSecondVariableNatTailOriginalAdjoinEta
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (i : localizedSecondVariableSmithIndex I k) :=
  localizedSecondVariableFullOriginalAdjoinEta I k ℕ i

/-- Countable-zeta-tail form of the unconditional scalar quotient
`M_1 / (M_1, eta_i) = (e_i)`. -/
theorem localizedSecondVariableNatTailOriginal_colon_adjoinEta_eq_span
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (i : localizedSecondVariableSmithIndex I k) :
    (localizedSecondVariableFullOriginalModule I k ℕ).colon
        ((localizedSecondVariableNatTailOriginalAdjoinEta I k i :
          Submodule (secondVariablePID P n)
            (localizedSecondVariableNatTailAmbient I k)) :
          Set (localizedSecondVariableNatTailAmbient I k)) =
      Ideal.span ({localizedSecondVariableSmithCoefficients I k i} :
        Set (secondVariablePID P n)) :=
  localizedSecondVariableFullOriginal_colon_adjoinEta_eq_span I k ℕ i

/-- Countable-zeta-tail form of the conditional distinguished-coefficient
chain. -/
theorem localizedSecondVariableNatTail_distinguished_scalar_quotient_chain
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (i : localizedSecondVariableSmithIndex I k)
    (h : ∀ j : localizedSecondVariableSmithIndex I k,
      localizedSecondVariableSmithCoefficients I k j ∣
        localizedSecondVariableSmithCoefficients I k i) :
    (localizedSecondVariableFullOriginalModule I k ℕ).colon
        ((localizedSecondVariableFullGroundModule I k ℕ :
          Submodule (secondVariablePID P n)
            (localizedSecondVariableNatTailAmbient I k)) :
          Set (localizedSecondVariableNatTailAmbient I k)) =
          Ideal.span ({localizedSecondVariableSmithCoefficients I k i} :
            Set (secondVariablePID P n)) ∧
      (localizedSecondVariableFullOriginalModule I k ℕ).colon
        ((localizedSecondVariableNatTailOriginalAdjoinEta I k i :
          Submodule (secondVariablePID P n)
            (localizedSecondVariableNatTailAmbient I k)) :
          Set (localizedSecondVariableNatTailAmbient I k)) =
          Ideal.span ({localizedSecondVariableSmithCoefficients I k i} :
            Set (secondVariablePID P n)) :=
  localizedSecondVariableFull_distinguished_scalar_quotient_chain I k ℕ i h

#print axioms localizedSecondVariable_mem_denominatorCarrier_iff_dvd
#print axioms localizedSecondVariableSmithFiltration
#print axioms localizedSecondVariable_mem_SmithFiltration_iff
#print axioms localizedSecondVariableSmithFiltration_empty
#print axioms localizedSecondVariableSmithFiltration_colon_insert_eq_span
#print axioms localizedSecondVariableSmithFiltration_colon_ground_eq_iInf
#print axioms localizedSecondVariableIsGreatestRemainingDivisor
#print axioms localizedSecondVariableSmithFiltration_colon_ground_eq_span_of_greatest
#print axioms localizedSecondVariableFullSmithFiltration
#print axioms localizedSecondVariableFullSmithFiltration_empty
#print axioms localizedSecondVariableFullOriginalAdjoinEta
#print axioms localizedSecondVariableFullOriginalAdjoinEta_eq_filtration_singleton
#print axioms localizedSecondVariableFullOriginal_colon_adjoinEta_eq_span
#print axioms localizedSecondVariableFullSmithFiltration_colon_ground_eq_iInf
#print axioms localizedSecondVariableFullSmithFiltration_colon_ground_eq_span_of_greatest
#print axioms localizedSecondVariableFull_distinguished_scalar_quotient_chain
#print axioms localizedSecondVariableNatTailSmithFiltration
#print axioms localizedSecondVariableNatTailOriginalAdjoinEta
#print axioms localizedSecondVariableNatTailOriginal_colon_adjoinEta_eq_span
#print axioms localizedSecondVariableNatTail_distinguished_scalar_quotient_chain

end

end RegularIdealDecomposition

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
