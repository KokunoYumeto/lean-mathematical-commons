/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0

The matrix proof is adapted from QICLean contributors,
`QICLean/Algebra/SkolemNoether.lean`, commit
`6bb40f17a0bed7cc62a6d5cf1ff13aaecbbdae8b`, Apache-2.0.

The quaternion proofs are adapted from The Tau Ceti contributors,
`TauCeti/Algebra/Quaternion/ComplexSubfield.lean`, commit
`ddb7e2a955836d345df91708d0cfc14a6f5c4698`, Apache-2.0.
The namespace, documentation, theorem names, and source linkage were modified
for Lean of the Mathematical Commons.
-/
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Emmy Noether, *Nichtkommutative Algebren* (1933): inner automorphisms

Controlled source: `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
lines 19477–19483.

Noether's “Satz über innere Automorphismen” says that an isomorphism between
two finite-rank simple subrings of `A_f` containing the center is induced by
an inner automorphism of `A_f`; she then records that every automorphism of
`A_f` is inner.

This module promotes two honest special cases found in the four-file external
Lean audit:

* `matrixAlgEquiv_inner` gives the full-matrix automorphism case over an
  arbitrary field. It is source-shaped packaging around Mathlib's existing
  `AlgEquiv.eq_linearEquivConjAlgEquiv`, with the explicit matrix unit
  transport adapted from QICLean.
* the declarations in `Quaternion` give a concrete noncentral-source case:
  any two real-algebra embeddings `ℂ → ℍ[ℝ]` are conjugate. The proof is
  adapted from TauCeti and uses only Mathlib.

The full printed theorem for arbitrary simple subrings is **not** claimed.
TauCeti proves a broad central-source version using its own tensor-product,
bimodule, and simple-Artinian infrastructure; its noncentral generalization
and the exact P40 hypothesis bridge remain explicit dependencies.
-/

namespace MathematicalCommons.Noether.NoncommutativeAlgebras1933

open scoped Matrix

/-- Full-matrix special case of P40 line 19483: every algebra automorphism of
`Matrix n n K` is conjugation by an invertible matrix.

This is `NEW_PACKAGING` around
`AlgEquiv.eq_linearEquivConjAlgEquiv`. The explicit transport from an
endomorphism-space linear equivalence to `GL n K` is adapted from QICLean's
Apache-2.0 `Matrix.skolemNoether_matrix`, generalized from `ℂ` to a field
`K`. -/
theorem matrixAlgEquiv_inner
    {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (f : Matrix n n K ≃ₐ[K] Matrix n n K) :
    ∃ X : GL n K, ∀ M : Matrix n n K,
      f M = (X : Matrix n n K) * M * ((X⁻¹ : GL n K) : Matrix n n K) := by
  classical
  let e : Matrix n n K ≃ₐ[K] Module.End K (n → K) := Matrix.toLinAlgEquiv'
  let fEnd : Module.End K (n → K) ≃ₐ[K] Module.End K (n → K) :=
    e.symm.trans (f.trans e)
  obtain ⟨T, hT⟩ := AlgEquiv.eq_linearEquivConjAlgEquiv (f := fEnd)
  let X : GL n K :=
    (Matrix.GeneralLinearGroup.toLin (n := n) (R := K)).symm
      (LinearMap.GeneralLinearGroup.ofLinearEquiv T)
  refine ⟨X, fun M => ?_⟩
  apply e.injective
  have hX_toLin : Matrix.GeneralLinearGroup.toLin X =
      LinearMap.GeneralLinearGroup.ofLinearEquiv T := by
    simp [X]
  have hX_lin : e (X : Matrix n n K) = (T : (n → K) →ₗ[K] n → K) := by
    change ((Matrix.GeneralLinearGroup.toLin X :
      LinearMap.GeneralLinearGroup K (n → K)) :
        (n → K) →ₗ[K] n → K) = (T : (n → K) →ₗ[K] n → K)
    rw [hX_toLin]
    rfl
  have hX_lin_inv :
      e ((X⁻¹ : GL n K) : Matrix n n K) =
        (T.symm : (n → K) →ₗ[K] n → K) := by
    have hX_toLin_inv : Matrix.GeneralLinearGroup.toLin (X⁻¹) =
        LinearMap.GeneralLinearGroup.ofLinearEquiv T.symm := by
      simp only [MulEquiv.map_inv, hX_toLin]
      exact (LinearMap.GeneralLinearGroup.ofLinearEquiv_inv (f := T)).symm
    change ((Matrix.GeneralLinearGroup.toLin (X⁻¹) :
      LinearMap.GeneralLinearGroup K (n → K)) :
        (n → K) →ₗ[K] n → K) =
      (T.symm : (n → K) →ₗ[K] n → K)
    rw [hX_toLin_inv]
    rfl
  calc
    e (f M) = fEnd (e M) := by simp [fEnd]
    _ = (T : (n → K) →ₗ[K] n → K) ∘ₗ e M ∘ₗ
          (T.symm : (n → K) →ₗ[K] n → K) := by
        rw [congrArg (· (e M)) hT]
        simp [LinearEquiv.conjAlgEquiv_apply]
    _ = e (X : Matrix n n K) * e M *
          e ((X⁻¹ : GL n K) : Matrix n n K) := by
        rw [← hX_lin, ← hX_lin_inv]
        simp [Module.End.mul_eq_comp, LinearMap.comp_assoc]
    _ = e ((X : Matrix n n K) * M *
          ((X⁻¹ : GL n K) : Matrix n n K)) := by
        simp [mul_assoc]

namespace Quaternion

open scoped _root_.Quaternion

/-- The standard real-algebra embedding of `ℂ` into the real quaternions.

TauCeti uses `Quaternion.ofComplex` from `Mathlib.Analysis.Quaternion`.  The
pinned low-footprint cache does not contain that analytic module, so this
source-equivalent algebraic definition keeps the P40 proof independent of the
normed-quaternion layer. -/
def ofComplex : ℂ →ₐ[ℝ] ℍ[ℝ] where
  toFun z := ⟨z.re, z.im, 0, 0⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp
  map_mul' z w := by ext <;> simp [Complex.mul_re, Complex.mul_im]
  commutes' r := by ext <;> simp

/-- The quaternion `j`, as a unit of the real quaternion division ring. -/
def jUnit : ℍ[ℝ]ˣ where
  val := ⟨0, 0, 1, 0⟩
  inv := ⟨0, 0, -1, 0⟩
  val_inv :=
    (by ext <;> simp :
      (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) * (⟨0, 0, -1, 0⟩ : ℍ[ℝ]) = 1)
  inv_val :=
    (by ext <;> simp :
      (⟨0, 0, -1, 0⟩ : ℍ[ℝ]) * (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) = 1)

theorem coe_jUnit : (jUnit : ℍ[ℝ]) = ⟨0, 0, 1, 0⟩ := (rfl)

theorem coe_inv_jUnit : ((jUnit⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) = ⟨0, 0, -1, 0⟩ := (rfl)

/-- Coordinates of the standard quaternion image of `Complex.I`. -/
theorem ofComplex_I :
    ofComplex Complex.I = (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) := by
  ext <;> simp [ofComplex]

/-- Conjugation by `j` negates the standard quaternion `i`. -/
theorem conj_jUnit_ofComplex_I :
    (jUnit : ℍ[ℝ]) * ofComplex Complex.I *
        ((jUnit⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) =
      -ofComplex Complex.I := by
  have h :
      (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) * (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) *
          (⟨0, 0, -1, 0⟩ : ℍ[ℝ]) =
        -(⟨0, 1, 0, 0⟩ : ℍ[ℝ]) := by
    ext <;> simp
  rw [ofComplex_I, coe_jUnit, coe_inv_jUnit]
  exact h

/-- Two square roots of `-1` that are not negatives of one another are
conjugate. The witness is `1 - u * x`. -/
private theorem exists_unit_conj_of_mul_ne_one
    {x u : ℍ[ℝ]} (hx : x * x = -1) (hu : u * u = -1)
    (h : u * x ≠ 1) :
    ∃ w : ℍ[ℝ]ˣ, u = (w : ℍ[ℝ]) * x * ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) := by
  have hw : (1 : ℍ[ℝ]) - u * x ≠ 0 := fun hz =>
    h (by rw [sub_eq_zero] at hz; exact hz.symm)
  have h1 : u * x * x = -u := by
    rw [mul_assoc, hx]
    exact mul_neg_one u
  have h2 : u * (u * x) = -x := by
    rw [← mul_assoc, hu]
    exact neg_one_mul x
  have key : ((1 : ℍ[ℝ]) - u * x) * x = u * ((1 : ℍ[ℝ]) - u * x) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, h1, h2, sub_neg_eq_add,
      sub_neg_eq_add]
    exact add_comm x u
  refine ⟨Units.mk0 _ hw, ?_⟩
  rw [Units.val_inv_eq_inv_val, Units.val_mk0, key, mul_assoc,
    mul_inv_cancel₀ hw, mul_one]

/-- Every square root of `-1` in the real quaternions is conjugate to the
standard quaternion `i`. -/
theorem exists_unit_conj_ofComplex_I {u : ℍ[ℝ]} (hu : u * u = -1) :
    ∃ w : ℍ[ℝ]ˣ,
      u = (w : ℍ[ℝ]) * ofComplex Complex.I *
        ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) := by
  have hx :
      ofComplex Complex.I * ofComplex Complex.I = -1 :=
    (Complex.lift.symm ofComplex).prop
  by_cases h : u * ofComplex Complex.I = 1
  · have h2 : -u = ofComplex Complex.I := by
      have h3 :
          u * ofComplex Complex.I * ofComplex Complex.I =
            1 * ofComplex Complex.I := by
        rw [h]
      rw [mul_assoc, hx] at h3
      exact (mul_neg_one u).symm.trans (by simpa only [one_mul] using h3)
    exact ⟨jUnit, by rw [conj_jUnit_ofComplex_I, ← h2, neg_neg]⟩
  · exact exists_unit_conj_of_mul_ne_one hx hu h

/-- Any two square roots of `-1` in the real quaternions are conjugate. -/
theorem exists_unit_conj_of_mul_self_eq_neg_one
    {u v : ℍ[ℝ]} (hu : u * u = -1) (hv : v * v = -1) :
    ∃ w : ℍ[ℝ]ˣ, v = (w : ℍ[ℝ]) * u * ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) := by
  obtain ⟨a, ha⟩ := exists_unit_conj_ofComplex_I hu
  obtain ⟨b, hb⟩ := exists_unit_conj_ofComplex_I hv
  refine ⟨b * a⁻¹, ?_⟩
  rw [ha, hb]
  simp only [Units.val_mul, mul_inv_rev, inv_inv, mul_assoc,
    Units.inv_mul_cancel_left]

/-- Conjugacy of real-algebra maps from `ℂ` is detected on `Complex.I`. -/
private theorem conj_unit_complexAlgHom_apply
    (w : ℍ[ℝ]ˣ) (f g : ℂ →ₐ[ℝ] ℍ[ℝ])
    (h : g Complex.I =
      (w : ℍ[ℝ]) * f Complex.I * ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]))
    (z : ℂ) :
    g z = (w : ℍ[ℝ]) * f z * ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) := by
  have hA :
      (w : ℍ[ℝ]) * algebraMap ℝ ℍ[ℝ] z.re *
          ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) =
        algebraMap ℝ ℍ[ℝ] z.re := by
    rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]
  have hB :
      (w : ℍ[ℝ]) * (z.im • f Complex.I) *
          ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) =
        z.im • ((w : ℍ[ℝ]) * f Complex.I *
          ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ])) := by
    rw [← _root_.Quaternion.coe_mul_eq_smul,
      ← _root_.Quaternion.coe_mul_eq_smul]
    rw [← mul_assoc (w : ℍ[ℝ]) (z.im : ℍ[ℝ]) (f Complex.I),
      ← _root_.Quaternion.coe_commutes]
    simp only [mul_assoc]
  conv_lhs => rw [← Complex.lift.apply_symm_apply g]
  conv_rhs => rw [← Complex.lift.apply_symm_apply f]
  simp only [Complex.lift_apply, Complex.liftAux_apply,
    Complex.lift_symm_apply_coe]
  rw [h, mul_add, add_mul, hA, hB]

/-- Concrete noncentral-source instance of P40 lines 19477–19483: any two
real-algebra embeddings of `ℂ` into the real quaternions are conjugate by a
quaternion unit. -/
theorem exists_unit_conj_complexAlgHom (f g : ℂ →ₐ[ℝ] ℍ[ℝ]) :
    ∃ w : ℍ[ℝ]ˣ, ∀ z : ℂ,
      g z = (w : ℍ[ℝ]) * f z * ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) := by
  have hf : f Complex.I * f Complex.I = -1 := (Complex.lift.symm f).prop
  have hg : g Complex.I * g Complex.I = -1 := (Complex.lift.symm g).prop
  obtain ⟨w, hw⟩ := exists_unit_conj_of_mul_self_eq_neg_one hf hg
  exact ⟨w, conj_unit_complexAlgHom_apply w f g hw⟩

/-- Complex conjugation on the standard copy `ℂ ⊆ ℍ[ℝ]` is explicitly
conjugation by `j`. -/
theorem ofComplex_conjAe (z : ℂ) :
    ofComplex (Complex.conjAe z) =
      (jUnit : ℍ[ℝ]) * ofComplex z *
        ((jUnit⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) := by
  refine conj_unit_complexAlgHom_apply jUnit ofComplex
    (ofComplex.comp Complex.conjAe.toAlgHom) ?_ z
  change ofComplex (Complex.conjAe Complex.I) = _
  have hconj : Complex.conjAe Complex.I = -Complex.I := by
    exact Complex.conj_I
  rw [hconj, map_neg]
  exact conj_jUnit_ofComplex_I.symm

#print axioms jUnit
#print axioms ofComplex
#print axioms coe_jUnit
#print axioms coe_inv_jUnit
#print axioms ofComplex_I
#print axioms conj_jUnit_ofComplex_I
#print axioms exists_unit_conj_ofComplex_I
#print axioms exists_unit_conj_of_mul_self_eq_neg_one
#print axioms exists_unit_conj_complexAlgHom
#print axioms ofComplex_conjAe

end Quaternion

#print axioms matrixAlgEquiv_inner

end MathematicalCommons.Noether.NoncommutativeAlgebras1933
