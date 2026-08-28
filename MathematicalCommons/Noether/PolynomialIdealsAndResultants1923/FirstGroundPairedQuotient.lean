/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.StageMultipliers
import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.RegularPairedQuotient

/-!
# Hentzelt--Noether Satz VII: the first nontrivial ground-ideal pair

Controlled source: Kurt Hentzelt, freely edited and conceptually recast by
Emmy Noether, *Zur Theorie der Polynomideale und Resultanten*, witness
`NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`.

Definition V at lines 13039--13052 defines the ground ideal `g_1` of stage one
by allowing a nonzero multiplier free of the first variable. The literal first
ground ideal is `g_0`, handled by the base case on line 13130. The first
nontrivial paired step of Satz VII at lines 13132--13160 compares the original
ideal with this containing ground ideal, singles out a polynomial regular in
the first variable, and identifies the relative quotient with a quotient of
bounded coefficient modules.

This file gives a modern ideal-quotient bridge from those source-shaped ideals
to the reusable result in `RegularPairedQuotient`. The source's associated
linear-form modules are not constructed or related to this ideal quotient by a
proved equivalence here. The historical
divisibility relation is stated in
modern inclusion orientation: the mapped original ideal is contained in the
mapped stage-one ground ideal. The extra assertion on line 13162, that the
bounded numerator is itself the ground module of the bounded denominator,
is **not** proved here and remains an explicitly open formalization target.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open MvPolynomial
open RegularitySpecialization

namespace RegularIdealDecomposition

noncomputable section

variable {P : Type*} [Field P]
variable {m n k : ℕ}

/-- Transport an ideal in all `n + 1` variables across `finSuccEquiv`, viewing
the first variable as the polynomial variable and the remaining variables as
coefficients. -/
noncomputable def finSuccIdeal
    (I : Ideal (MvPolynomial (Fin (n + 1)) P)) :
    Ideal (Polynomial (MvPolynomial (Fin n) P)) :=
  I.map (MvPolynomial.finSuccEquiv P n).toRingEquiv

/-- The source stage-one ground ideal `g_1`, transported to the univariate-over-the-
remaining-variables presentation used by regular polynomial division.

The cutoff is one because source `b^(2)` is free of the first (zero-based
variable `0`) variable. -/
noncomputable def stageOneGroundIdeal
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) :
    Ideal (Polynomial (MvPolynomial (Fin (n + 1)) P)) :=
  (stageGroundIdeal (S := P) 1 I).map
    (MvPolynomial.finSuccEquiv P (n + 1)).toRingEquiv

/-- Every ideal lies in each of its ground ideals: in Definition V, choose
the admissible multiplier `b = 1`. -/
theorem le_stageGroundIdeal
    (cutoff : ℕ) (I : Ideal (MvPolynomial (Fin m) P)) :
    I ≤ stageGroundIdeal (S := P) cutoff I := by
  intro F hFI
  rw [mem_stageGroundIdeal_iff]
  refine ⟨1, one_ne_zero, ?_, ?_⟩
  · intro j _hj
    simp
  · simpa using hFI

/-- Source line 13130's base case: over the polynomial domain, the cutoff-zero
ground ideal is the unit ideal exactly when the original ideal is nonzero. -/
theorem stageGroundIdeal_zero_eq_top_iff
    (I : Ideal (MvPolynomial (Fin m) P)) :
    stageGroundIdeal (S := P) 0 I = ⊤ ↔ I ≠ ⊥ := by
  constructor
  · intro htop
    have hOne : (1 : MvPolynomial (Fin m) P) ∈
        stageGroundIdeal (S := P) 0 I := by
      rw [htop]
      simp
    rw [mem_stageGroundIdeal_iff] at hOne
    obtain ⟨b, hb0, _hbfree, hbI⟩ := hOne
    exact I.ne_bot_iff.mpr ⟨b, by simpa using hbI, hb0⟩
  · intro hI
    rw [Ideal.eq_top_iff_one]
    obtain ⟨b, hbI, hb0⟩ := I.ne_bot_iff.mp hI
    rw [mem_stageGroundIdeal_iff]
    exact ⟨b, hb0, by simp, by simpa using hbI⟩

/-- A regular member makes the source's base ground ideal `g_0` the unit ideal,
as asserted on line 13130. -/
theorem stageGroundIdeal_zero_eq_top_of_regular_mem
    (I : Ideal (MvPolynomial (Fin (n + 2)) P))
    (C : MvPolynomial (Fin (n + 2)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 2)) k C)
    (hCI : C ∈ I) :
    stageGroundIdeal (S := P) 0 I = ⊤ := by
  apply (stageGroundIdeal_zero_eq_top_iff I).2
  apply I.ne_bot_iff.mpr
  refine ⟨C, hCI, ?_⟩
  intro hCzero
  apply hC.2
  simp [hCzero]

/-- After transport by `finSuccEquiv`, the original ideal is contained in its
stage-one ground ideal. This is the modern inclusion orientation of the source's
divisibility relation between `g_1` and `m`. -/
theorem finSuccIdeal_le_stageOneGroundIdeal
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) :
    finSuccIdeal (n := n + 1) I ≤ stageOneGroundIdeal I := by
  exact Ideal.map_mono (le_stageGroundIdeal 1 I)

/-- Exact membership transport through the multivariate/univariate ring
equivalence. -/
@[simp] theorem finSuccEquiv_mem_finSuccIdeal_iff
    (I : Ideal (MvPolynomial (Fin (n + 1)) P))
    (C : MvPolynomial (Fin (n + 1)) P) :
    MvPolynomial.finSuccEquiv P n C ∈ finSuccIdeal I ↔ C ∈ I := by
  exact Ideal.apply_mem_of_equiv_iff

/-- Membership in the original ideal transports to membership in its
`finSuccEquiv` image. -/
theorem finSuccEquiv_mem_finSuccIdeal
    (I : Ideal (MvPolynomial (Fin (n + 1)) P))
    {C : MvPolynomial (Fin (n + 1)) P} (hCI : C ∈ I) :
    MvPolynomial.finSuccEquiv P n C ∈ finSuccIdeal I :=
  (finSuccEquiv_mem_finSuccIdeal_iff I C).2 hCI

/-- The quotient of the stage-one ground ideal by the original ideal is linearly
equivalent to the quotient of their bounded coefficient modules.  This is the
source-shaped instance of equations (22)--(23) and line 13160. -/
noncomputable def stageOneGroundIdealQuotientEquivBounded
    (I : Ideal (MvPolynomial (Fin (n + 2)) P))
    (C : MvPolynomial (Fin (n + 2)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 2)) k C)
    (hCI : C ∈ I) :
    CommonTailQuotient.relativeQuotient
        ((stageOneGroundIdeal I).restrictScalars (MvPolynomial (Fin (n + 1)) P))
        ((finSuccIdeal (n := n + 1) I).restrictScalars
          (MvPolynomial (Fin (n + 1)) P)) ≃ₗ[
      MvPolynomial (Fin (n + 1)) P]
      CommonTailQuotient.relativeQuotient
        (boundedPart (stageOneGroundIdeal I) k)
        (boundedPart (finSuccIdeal (n := n + 1) I) k) :=
  regularPairedQuotientEquivBounded
    (stageOneGroundIdeal I) (finSuccIdeal (n := n + 1) I) C hC
    (finSuccEquiv_mem_finSuccIdeal (n := n + 1) I hCI)
    (finSuccIdeal_le_stageOneGroundIdeal I)

/-- The source-shaped stage-one ground/original ideal quotient is finite over the
remaining-variable polynomial ring. -/
theorem stageOneGroundIdealQuotient_moduleFinite
    (I : Ideal (MvPolynomial (Fin (n + 2)) P))
    (C : MvPolynomial (Fin (n + 2)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 2)) k C)
    (hCI : C ∈ I) :
    Module.Finite (MvPolynomial (Fin (n + 1)) P)
      (CommonTailQuotient.relativeQuotient
        ((stageOneGroundIdeal I).restrictScalars (MvPolynomial (Fin (n + 1)) P))
        ((finSuccIdeal (n := n + 1) I).restrictScalars
          (MvPolynomial (Fin (n + 1)) P))) :=
  regularPairedQuotient_moduleFinite
    (stageOneGroundIdeal I) (finSuccIdeal (n := n + 1) I) C hC
    (finSuccEquiv_mem_finSuccIdeal (n := n + 1) I hCI)
    (finSuccIdeal_le_stageOneGroundIdeal I)

/-- Every class in the stage-one ground/original ideal quotient has a
representative in the bounded part of the stage-one ground ideal. -/
theorem exists_stageOneGroundIdeal_boundedRepresentative
    (I : Ideal (MvPolynomial (Fin (n + 2)) P))
    (C : MvPolynomial (Fin (n + 2)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 2)) k C)
    (hCI : C ∈ I)
    (q : CommonTailQuotient.relativeQuotient
      ((stageOneGroundIdeal I).restrictScalars (MvPolynomial (Fin (n + 1)) P))
      ((finSuccIdeal (n := n + 1) I).restrictScalars
        (MvPolynomial (Fin (n + 1)) P))) :
    ∃ g : boundedPart (stageOneGroundIdeal I) k,
      q = (stageOneGroundIdealQuotientEquivBounded I C hC hCI).symm
        (Submodule.Quotient.mk g) :=
  exists_regularPaired_boundedRepresentative
    (stageOneGroundIdeal I) (finSuccIdeal (n := n + 1) I) C hC
    (finSuccEquiv_mem_finSuccIdeal (n := n + 1) I hCI)
    (finSuccIdeal_le_stageOneGroundIdeal I) q

#print axioms finSuccIdeal
#print axioms stageOneGroundIdeal
#print axioms le_stageGroundIdeal
#print axioms stageGroundIdeal_zero_eq_top_iff
#print axioms stageGroundIdeal_zero_eq_top_of_regular_mem
#print axioms finSuccIdeal_le_stageOneGroundIdeal
#print axioms finSuccEquiv_mem_finSuccIdeal_iff
#print axioms finSuccEquiv_mem_finSuccIdeal
#print axioms stageOneGroundIdealQuotientEquivBounded
#print axioms stageOneGroundIdealQuotient_moduleFinite
#print axioms exists_stageOneGroundIdeal_boundedRepresentative

end

end RegularIdealDecomposition

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
