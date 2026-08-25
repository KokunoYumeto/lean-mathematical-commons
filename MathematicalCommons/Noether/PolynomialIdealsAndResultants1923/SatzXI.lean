/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Hentzelt--Noether 1923, Satz XI: rank of a principal ideal modulo an element

Controlled source: Kurt Hentzelt, freely edited and conceptually recast by
Emmy Noether, *Zur Theorie der Polynomideale und Resultanten*, witness
`NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
Satz XI at lines 13426--13433.

If `h ∈ (f)` and `h ≠ 0`, the image of `(f)` in `K[X] / (h)` has dimension
`natDegree h - natDegree f` over `K`.  The file also records the exact
third-isomorphism equivalence underlying that dimension calculation.
-/

open Polynomial

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.SatzXI

variable {K : Type*} [Field K]

/-- The ideal of residue classes of multiples of `f` modulo `h`.  This is
Noether's linear-forms module into which the principal ideal `(f)` passes
modulo `h(t)`. -/
noncomputable def residueIdeal (f h : K[X]) : Ideal (K[X] ⧸ Ideal.span {h}) :=
  (Ideal.span {f}).map (Ideal.Quotient.mkₐ K (Ideal.span {h}))

/-- The same residue-class ideal, regarded as a `K`-linear subspace. -/
noncomputable def residueSubspace (f h : K[X]) :
    Submodule K (K[X] ⧸ Ideal.span {h}) :=
  (residueIdeal f h).restrictScalars K

/-- Quotienting `K[X] / (h)` by the image of `(f)` recovers `K[X] / (f)`
whenever `h ∈ (f)`.  This is the third-isomorphism bridge used in the rank
proof. -/
noncomputable def residueIdealQuotientEquiv (f h : K[X])
    (hhf : h ∈ Ideal.span {f}) :
    ((K[X] ⧸ Ideal.span {h}) ⧸ residueIdeal f h) ≃ₐ[K]
      K[X] ⧸ Ideal.span {f} :=
  DoubleQuot.quotQuotEquivQuotOfLEₐ K <| by
    refine (Ideal.span_le).2 ?_
    rintro _ rfl
    exact hhf

/-- **Hentzelt--Noether 1923, Satz XI.**  If the nonzero polynomial `h`
belongs to the principal ideal `(f)`, then the `K`-rank of the residue classes
of `(f)` modulo `(h)` is `deg h - deg f`.

Noether writes `k = deg h` and `p = deg f`, and exhibits the classes of
`f, X*f, ..., X^(k-p-1)*f`.  This theorem proves the exact rank conclusion;
an explicit-basis refinement identifies those representatives. -/
theorem finrank_residueSubspace_eq_natDegree_sub (f h : K[X]) (hh : h ≠ 0)
    (hhf : h ∈ Ideal.span {f}) :
    Module.finrank K (residueSubspace f h) = h.natDegree - f.natDegree := by
  letI : Module.Finite K (K[X] ⧸ Ideal.span {h}) :=
    (AdjoinRoot.powerBasis hh).finite
  have hquotient :
      Module.finrank K
          ((K[X] ⧸ Ideal.span {h}) ⧸ residueSubspace f h) =
        f.natDegree := by
    calc
      Module.finrank K
          ((K[X] ⧸ Ideal.span {h}) ⧸ residueSubspace f h) =
          Module.finrank K
            ((K[X] ⧸ Ideal.span {h}) ⧸ residueIdeal f h) :=
        (Submodule.Quotient.restrictScalarsEquiv K (residueIdeal f h)).finrank_eq
      _ = Module.finrank K (K[X] ⧸ Ideal.span {f}) :=
        (residueIdealQuotientEquiv f h hhf).toLinearEquiv.finrank_eq
      _ = f.natDegree := finrank_quotient_span_eq_natDegree
  have hsum := (residueSubspace f h).finrank_quotient_add_finrank
  rw [hquotient, finrank_quotient_span_eq_natDegree] at hsum
  omega

/-- Multiplication by `f`, followed by reduction modulo `h₁ * f`, with
codomain restricted to the residue classes of the principal ideal `(f)`. -/
noncomputable def multiplyIntoResidue (f h₁ : K[X]) :
    K[X] →ₗ[K] residueSubspace f (h₁ * f) :=
  LinearMap.codRestrict (residueSubspace f (h₁ * f))
    ((Ideal.Quotient.mkₐ K (Ideal.span {h₁ * f})).toLinearMap.comp
      (LinearMap.mul K K[X] f)) fun g ↦ by
        change Ideal.Quotient.mk (Ideal.span {h₁ * f}) (f * g) ∈
          residueIdeal f (h₁ * f)
        apply Ideal.mem_map_of_mem
        exact Ideal.mem_span_singleton.mpr ⟨g, rfl⟩

@[simp]
theorem coe_multiplyIntoResidue (f h₁ g : K[X]) :
    ((multiplyIntoResidue f h₁ g : residueSubspace f (h₁ * f)) :
        K[X] ⧸ Ideal.span {h₁ * f}) =
      Ideal.Quotient.mk (Ideal.span {h₁ * f}) (f * g) :=
  rfl

/-- Every residue class of a multiple of `f` has a preimage under
`multiplyIntoResidue`. -/
theorem multiplyIntoResidue_surjective (f h₁ : K[X]) :
    Function.Surjective (multiplyIntoResidue f h₁) := by
  rintro ⟨y, hy⟩
  change y ∈ residueIdeal f (h₁ * f) at hy
  obtain ⟨g, hg, hgy⟩ :=
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hg
  refine ⟨a, Subtype.ext ?_⟩
  change Ideal.Quotient.mk (Ideal.span {h₁ * f}) (f * a) = y
  rw [← hgy, ha]

/-- For nonzero `f`, the kernel of multiplication by `f` modulo `h₁ * f`
is exactly `(h₁)`. -/
theorem ker_multiplyIntoResidue (f h₁ : K[X]) (hf : f ≠ 0) :
    LinearMap.ker (multiplyIntoResidue f h₁) =
      (Ideal.span {h₁}).restrictScalars K := by
  ext g
  simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem]
  rw [Subtype.ext_iff]
  change
    Ideal.Quotient.mk (Ideal.span {h₁ * f}) (f * g) = 0 ↔
      g ∈ Ideal.span {h₁}
  rw [Ideal.Quotient.eq_zero_iff_mem]
  simp only [Ideal.mem_span_singleton]
  simpa [mul_comm] using
    (mul_dvd_mul_iff_left hf : f * h₁ ∣ f * g ↔ h₁ ∣ g)

/-- Multiplication by `f` identifies `K[X] / (h₁)` with the residue classes
of `(f)` modulo `(h₁ * f)`. -/
noncomputable def quotientMulEquivResidue (f h₁ : K[X]) (hf : f ≠ 0) :
    (K[X] ⧸ Ideal.span {h₁}) ≃ₗ[K] residueSubspace f (h₁ * f) :=
  (Submodule.quotEquivOfEq
      ((Ideal.span {h₁}).restrictScalars K)
      (LinearMap.ker (multiplyIntoResidue f h₁))
      (ker_multiplyIntoResidue f h₁ hf).symm).trans
    ((multiplyIntoResidue f h₁).quotKerEquivOfSurjective
      (multiplyIntoResidue_surjective f h₁))

@[simp]
theorem quotientMulEquivResidue_mk (f h₁ : K[X]) (hf : f ≠ 0)
    (g : K[X]) :
    quotientMulEquivResidue f h₁ hf
        (Ideal.Quotient.mk (Ideal.span {h₁}) g) =
      multiplyIntoResidue f h₁ g := by
  rfl

/-- The explicit basis displayed in Satz XI. -/
noncomputable def displayedBasis (f h₁ : K[X]) (hf : f ≠ 0)
    (hh₁ : h₁ ≠ 0) :
    Module.Basis (Fin h₁.natDegree) K (residueSubspace f (h₁ * f)) :=
  (AdjoinRoot.powerBasis hh₁).basis.map
    (quotientMulEquivResidue f h₁ hf)

/-- The `i`th basis vector is represented by `X^i * f`, exactly as in
Noether's displayed list. -/
theorem coe_displayedBasis_apply (f h₁ : K[X]) (hf : f ≠ 0)
    (hh₁ : h₁ ≠ 0) (i : Fin h₁.natDegree) :
    ((displayedBasis f h₁ hf hh₁ i : residueSubspace f (h₁ * f)) :
        K[X] ⧸ Ideal.span {h₁ * f}) =
      Ideal.Quotient.mk (Ideal.span {h₁ * f}) (X ^ (i : ℕ) * f) := by
  rw [show displayedBasis f h₁ hf hh₁ i =
      quotientMulEquivResidue f h₁ hf
        ((AdjoinRoot.powerBasis hh₁).basis i) from rfl]
  rw [(AdjoinRoot.powerBasis hh₁).basis_eq_pow]
  have hpow : (AdjoinRoot.powerBasis hh₁).gen ^ (i : ℕ) =
      Ideal.Quotient.mk (Ideal.span {h₁}) (X ^ (i : ℕ)) := by
    rw [AdjoinRoot.powerBasis_gen]
    change
      (Ideal.Quotient.mk (Ideal.span {h₁}) X) ^ (i : ℕ) =
        Ideal.Quotient.mk (Ideal.span {h₁}) (X ^ (i : ℕ))
    rw [map_pow]
  rw [hpow, quotientMulEquivResidue_mk]
  simp [mul_comm]

#print axioms residueIdeal
#print axioms residueSubspace
#print axioms residueIdealQuotientEquiv
#print axioms finrank_residueSubspace_eq_natDegree_sub
#print axioms multiplyIntoResidue
#print axioms coe_multiplyIntoResidue
#print axioms multiplyIntoResidue_surjective
#print axioms ker_multiplyIntoResidue
#print axioms quotientMulEquivResidue
#print axioms quotientMulEquivResidue_mk
#print axioms displayedBasis
#print axioms coe_displayedBasis_apply

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.SatzXI
