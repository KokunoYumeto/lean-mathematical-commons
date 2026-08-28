import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.FirstLinearFormModules

/-!
# Hentzelt--Noether Satz VII: the first finite ground module

Module for P22, controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
Definition I and Satz I at lines 12752--12795 and the cutoff-one application
at line 13162.

Formula (4) characterizes the ground module of a linear-form module `M` as
the forms `g` for which some nonzero coefficient-ring scalar `b` has
`b • g ∈ M`.  This file first packages that nonzero-scalar saturation for a
module over a domain.  It then proves that source stage-one multipliers--the
nonzero polynomials free of the first variable--become precisely nonzero
scalars under `MvPolynomial.finSuccEquiv`.  Consequently the bounded part of
the transported stage-one ground ideal is exactly the ground module of the
bounded part of the transported original ideal, which is line 13162.

No Smith-basis or resultant conclusion is used here.  Those require the
separate localization and finite-free hypotheses recorded after equation (24).
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open MvPolynomial

namespace RegularIdealDecomposition

noncomputable section

section AbstractGroundModule

variable {R E : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
variable [AddCommMonoid E] [Module R E]

/-- Formula (4): enlarge a submodule by all elements whose nonzero scalar
multiple belongs to it. -/
def nonzeroScalarSaturation (M : Submodule R E) : Submodule R E where
  carrier := {x | ∃ b : R, b ≠ 0 ∧ b • x ∈ M}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha, hax⟩ ⟨b, hb, hby⟩
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    simpa [smul_add, smul_smul, mul_comm] using
      M.add_mem (M.smul_mem b hax) (M.smul_mem a hby)
  smul_mem' := by
    rintro c x ⟨b, hb, hbx⟩
    refine ⟨b, hb, ?_⟩
    simpa [smul_smul, mul_comm] using M.smul_mem c hbx

@[simp]
theorem mem_nonzeroScalarSaturation_iff (M : Submodule R E) (x : E) :
    x ∈ nonzeroScalarSaturation M ↔
      ∃ b : R, b ≠ 0 ∧ b • x ∈ M :=
  Iff.rfl

/-- Every module is contained in its nonzero-scalar saturation. -/
theorem le_nonzeroScalarSaturation (M : Submodule R E) :
    M ≤ nonzeroScalarSaturation M := by
  intro x hx
  exact ⟨1, one_ne_zero, by simpa using hx⟩

/-- Saturation is monotone in the original module. -/
theorem nonzeroScalarSaturation_mono {M N : Submodule R E} (hMN : M ≤ N) :
    nonzeroScalarSaturation M ≤ nonzeroScalarSaturation N := by
  rintro x ⟨b, hb, hbx⟩
  exact ⟨b, hb, hMN hbx⟩

/-- Formula (2): a ground module is closed under cancelling any nonzero
coefficient-ring scalar. -/
def IsGroundModule (G : Submodule R E) : Prop :=
  ∀ (b : R) (g : E), b ≠ 0 → b • g ∈ G → g ∈ G

/-- Formula (2) is equivalent to being fixed by formula-(4) saturation. -/
theorem isGroundModule_iff_nonzeroScalarSaturation_eq
    (G : Submodule R E) :
    IsGroundModule G ↔ nonzeroScalarSaturation G = G := by
  constructor
  · intro hG
    apply le_antisymm
    · rintro g ⟨b, hb, hbg⟩
      exact hG b g hb hbg
    · exact le_nonzeroScalarSaturation G
  · intro hG b g hb hbg
    have hg : g ∈ nonzeroScalarSaturation G := ⟨b, hb, hbg⟩
    rwa [hG] at hg

/-- Applying formula (4) twice adds nothing. -/
theorem nonzeroScalarSaturation_idem (M : Submodule R E) :
    nonzeroScalarSaturation (nonzeroScalarSaturation M) =
      nonzeroScalarSaturation M := by
  apply le_antisymm
  · rintro x ⟨a, ha, hax⟩
    rcases hax with ⟨b, hb, hbax⟩
    refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
    simpa [smul_smul] using hbax
  · exact le_nonzeroScalarSaturation (nonzeroScalarSaturation M)

/-- The saturation constructed by formula (4) is itself a ground module. -/
theorem nonzeroScalarSaturation_isGroundModule (M : Submodule R E) :
    IsGroundModule (nonzeroScalarSaturation M) :=
  (isGroundModule_iff_nonzeroScalarSaturation_eq _).2
    (nonzeroScalarSaturation_idem M)

/-- Formula (4) is contained in every ground module which contains the
original module. -/
theorem nonzeroScalarSaturation_le_of_le_of_isGroundModule
    {M G : Submodule R E} (hMG : M ≤ G) (hG : IsGroundModule G) :
    nonzeroScalarSaturation M ≤ G := by
  rintro x ⟨b, hb, hbx⟩
  exact hG b x hb (hMG hbx)

/-- Satz I: formula (4) constructs the smallest ground module containing
the given module. -/
theorem nonzeroScalarSaturation_isLeast (M : Submodule R E) :
    IsLeast {G : Submodule R E | M ≤ G ∧ IsGroundModule G}
      (nonzeroScalarSaturation M) := by
  refine ⟨⟨le_nonzeroScalarSaturation M,
    nonzeroScalarSaturation_isGroundModule M⟩, ?_⟩
  intro G hG
  exact nonzeroScalarSaturation_le_of_le_of_isGroundModule hG.1 hG.2

end AbstractGroundModule

variable {P : Type*} [Field P]
variable {n k : ℕ}

/-- A polynomial free of the first multivariate variable becomes a constant
polynomial under `finSuccEquiv`. -/
theorem finSuccEquiv_eq_C_coeff_zero_of_first_notMem_vars
    (b : MvPolynomial (Fin (n + 2)) P)
    (hbfree : ∀ j : Fin (n + 2), j.1 < 1 → j ∉ b.vars) :
    MvPolynomial.finSuccEquiv P (n + 1) b =
      Polynomial.C ((MvPolynomial.finSuccEquiv P (n + 1) b).coeff 0) := by
  apply Polynomial.eq_C_of_natDegree_eq_zero
  rw [MvPolynomial.natDegree_finSuccEquiv]
  apply not_ne_iff.mp
  intro hdegree
  exact hbfree 0 (by simp)
    (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr hdegree)

/-- Conversely, a coefficient-ring polynomial embedded as a univariate
constant is free of the first multivariate variable. -/
theorem finSuccEquiv_symm_C_first_notMem_vars
    (b : MvPolynomial (Fin (n + 1)) P) :
    ∀ j : Fin (n + 2), j.1 < 1 →
      j ∉ ((MvPolynomial.finSuccEquiv P (n + 1)).symm
        (Polynomial.C b)).vars := by
  intro j hj hmem
  have hj0 : j = 0 := by
    apply Fin.ext
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
  subst j
  rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero] at hmem
  apply hmem
  rw [← MvPolynomial.natDegree_finSuccEquiv]
  simp

/-- Source stage-one ground-ideal membership, after `finSuccEquiv`, is exactly
formula-(4) saturation by nonzero scalars in the late-variable coefficient
ring. -/
theorem mem_stageOneGroundIdeal_iff_exists_smul
    (I : Ideal (MvPolynomial (Fin (n + 2)) P))
    (F : Polynomial (MvPolynomial (Fin (n + 1)) P)) :
    F ∈ stageOneGroundIdeal I ↔
      ∃ b : MvPolynomial (Fin (n + 1)) P,
        b ≠ 0 ∧ b • F ∈ finSuccIdeal (n := n + 1) I := by
  let e := MvPolynomial.finSuccEquiv P (n + 1)
  change F ∈ (stageGroundIdeal (S := P) 1 I).map e.toRingEquiv ↔ _
  rw [← Ideal.symm_apply_mem_of_equiv_iff]
  rw [mem_stageGroundIdeal_iff]
  constructor
  · rintro ⟨a, ha, hafree, haF⟩
    let b : MvPolynomial (Fin (n + 1)) P := (e a).coeff 0
    have hea : e a = Polynomial.C b :=
      finSuccEquiv_eq_C_coeff_zero_of_first_notMem_vars a hafree
    have hb : b ≠ 0 := by
      intro hb0
      apply ha
      apply e.injective
      simpa [hea, hb0]
    refine ⟨b, hb, ?_⟩
    have hmap : e (a * e.symm F) ∈ finSuccIdeal (n := n + 1) I :=
      finSuccEquiv_mem_finSuccIdeal I haF
    simpa [map_mul, e.apply_symm_apply, hea, Algebra.smul_def] using hmap
  · rintro ⟨b, hb, hbF⟩
    let a : MvPolynomial (Fin (n + 2)) P := e.symm (Polynomial.C b)
    have ha : a ≠ 0 := by
      intro ha0
      apply hb
      have := congrArg e ha0
      simpa [a] using this
    have hafree : ∀ j : Fin (n + 2), j.1 < 1 → j ∉ a.vars := by
      simpa [a, e] using
        (finSuccEquiv_symm_C_first_notMem_vars (P := P) (n := n) b)
    refine ⟨a, ha, hafree, ?_⟩
    have hback : e.symm (b • F) ∈ I :=
      Ideal.symm_apply_mem_of_equiv_iff.mpr hbF
    simpa [a, Algebra.smul_def, map_mul] using hback

/-- Line 13162: the finite bounded part of the cutoff-one ground ideal is
exactly the formula-(4) ground module of the finite bounded part of the
original ideal. -/
theorem boundedPartInDegreeLT_stageOneGroundIdeal_eq_saturation
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    boundedPartInDegreeLT (stageOneGroundIdeal I) k =
      nonzeroScalarSaturation
        (boundedPartInDegreeLT (finSuccIdeal (n := n + 1) I) k) := by
  ext r
  rw [mem_boundedPartInDegreeLT_iff,
    mem_nonzeroScalarSaturation_iff,
    mem_stageOneGroundIdeal_iff_exists_smul]
  constructor
  · rintro ⟨b, hb, hbr⟩
    refine ⟨b, hb, ?_⟩
    rw [mem_boundedPartInDegreeLT_iff]
    simpa using hbr
  · rintro ⟨b, hb, hbr⟩
    refine ⟨b, hb, ?_⟩
    rw [mem_boundedPartInDegreeLT_iff] at hbr
    simpa using hbr

/-- The source-facing formula at line 13162: a bounded form belongs to
`G₁*` exactly when a nonzero late-variable scalar sends it into `M₁*`. -/
@[simp]
theorem mem_boundedPartInDegreeLT_stageOneGroundIdeal_iff
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (r : Polynomial.degreeLT (MvPolynomial (Fin (n + 1)) P) k) :
    r ∈ boundedPartInDegreeLT (stageOneGroundIdeal I) k ↔
      ∃ b : MvPolynomial (Fin (n + 1)) P,
        b ≠ 0 ∧ b • r ∈
          boundedPartInDegreeLT (finSuccIdeal (n := n + 1) I) k := by
  rw [boundedPartInDegreeLT_stageOneGroundIdeal_eq_saturation,
    mem_nonzeroScalarSaturation_iff]

/-- The finite cutoff-one ground module satisfies Definition I's cancellation
criterion. -/
theorem boundedPartInDegreeLT_stageOneGroundIdeal_isGroundModule
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    IsGroundModule (boundedPartInDegreeLT (stageOneGroundIdeal I) k) := by
  rw [boundedPartInDegreeLT_stageOneGroundIdeal_eq_saturation]
  exact nonzeroScalarSaturation_isGroundModule _

#print axioms nonzeroScalarSaturation
#print axioms mem_nonzeroScalarSaturation_iff
#print axioms le_nonzeroScalarSaturation
#print axioms nonzeroScalarSaturation_mono
#print axioms IsGroundModule
#print axioms isGroundModule_iff_nonzeroScalarSaturation_eq
#print axioms nonzeroScalarSaturation_idem
#print axioms nonzeroScalarSaturation_isGroundModule
#print axioms nonzeroScalarSaturation_le_of_le_of_isGroundModule
#print axioms nonzeroScalarSaturation_isLeast
#print axioms finSuccEquiv_eq_C_coeff_zero_of_first_notMem_vars
#print axioms finSuccEquiv_symm_C_first_notMem_vars
#print axioms mem_stageOneGroundIdeal_iff_exists_smul
#print axioms boundedPartInDegreeLT_stageOneGroundIdeal_eq_saturation
#print axioms mem_boundedPartInDegreeLT_stageOneGroundIdeal_iff
#print axioms boundedPartInDegreeLT_stageOneGroundIdeal_isGroundModule

end

end RegularIdealDecomposition

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
