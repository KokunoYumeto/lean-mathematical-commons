/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.FirstSmithGreatestCoefficientBridge

/-!
# Hentzelt--Noether Satz VIII: an integral numerator for the first localized Smith coefficient

Module for P22, controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
lines 13323--13349, especially the return from the localized highest
elementary divisor to the integral equation (33).

For the cutoff-one Smith pair, the coefficient ring before localization is
`A = P[x₃, ...][x₂]` and the PID after localization is
`L = Frac(P[x₃, ...])[x₂]`.  Mathlib's localization surjectivity supplies a
nonzero integral numerator `a : A` for the selected localized coefficient.
The generic denominator-clearing lemma below then proves that, for every
member of the bounded cutoff-one ground module, one genuinely late-variable
denominator sends `a` times that member into the bounded original module.

This is the integral, bounded-module kernel of equation (33).  It does not
normalize `a` to Hentzelt's primitive `E^(2)`, prove independence of the Smith
choices, transport the assertion from bounded coordinates to every element of
the full stage ground ideal, construct later stages, or prove equation (34).
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

namespace LocalizedSubmoduleDenominator

section Generic

variable {A L E F : Type*}
variable [CommRing A] [CommRing L] [Algebra A L]
variable [AddCommGroup E] [Module A E]
variable [AddCommGroup F] [Module A F] [Module L F] [IsScalarTower A L F]
variable (D : Submonoid A) [IsLocalization D L]
variable (f : E →ₗ[A] F) [IsLocalizedModule D f]

/-- Membership of the image of `x` in the localized extension of `M` can be
cleared by one denominator.  No injectivity or regularity hypothesis is
needed: a second denominator supplied by `IsLocalizedModule.exists_of_eq`
absorbs the possible localization torsion. -/
theorem exists_denominator_smul_mem_of_map_mem_localized
    (M : Submodule A E) {x : E}
    (hx : f x ∈ M.localized' L D f) :
    ∃ d : D, (d : A) • x ∈ M := by
  rw [Submodule.mem_localized'] at hx
  obtain ⟨m, hm, s, hs⟩ := hx
  have hfm : f m = f ((s : A) • x) := by
    have hfm' := IsLocalizedModule.mk'_eq_iff.mp hs
    change f m = (s : A) • f x at hfm'
    simpa using hfm'
  obtain ⟨c, hc⟩ :=
    IsLocalizedModule.exists_of_eq (S := D) (f := f) hfm
  refine ⟨c * s, ?_⟩
  change (c : A) • m = (c : A) • ((s : A) • x) at hc
  have hmem : (c : A) • ((s : A) • x) ∈ M := by
    rw [← hc]
    exact M.smul_mem (c : A) hm
  simpa [smul_smul] using hmem

/-- Scalar-action form of denominator clearing.  An action by the image of an
integral scalar in the localized module descends after one denominator to the
unlocalized submodule. -/
theorem exists_denominator_smul_smul_mem_of_algebraMap_smul_mem_localized
    (M : Submodule A E) (a : A) (x : E)
    (hx : algebraMap A L a • f x ∈ M.localized' L D f) :
    ∃ d : D, (d : A) • (a • x) ∈ M := by
  apply exists_denominator_smul_mem_of_map_mem_localized
    (L := L) D f M
  simpa only [f.map_smul, algebraMap_smul L] using hx

end Generic

end LocalizedSubmoduleDenominator

namespace RegularIdealDecomposition

noncomputable section

variable {P : Type*} [Field P]
variable {n : ℕ}

attribute [local instance] Polynomial.algebra

local instance lateVariablePolynomialIsLocalizationForIntegralNumerator :
    IsLocalization (lateVariableDenominators (P := P) (n := n))
      (Polynomial (FractionRing (MvPolynomial (Fin n) P))) :=
  Polynomial.isLocalization
    (nonZeroDivisors (MvPolynomial (Fin n) P))
    (FractionRing (MvPolynomial (Fin n) P))

local instance secondVariableBoundedLocalizationMapIsLocalizedForIntegralNumerator
    (k : ℕ) :
    IsLocalizedModule (lateVariableDenominators (P := P) (n := n))
      (secondVariableBoundedLocalizationMap (P := P) (n := n) k) :=
  secondVariableBoundedLocalizationMap_isLocalizedModule (P := P) (n := n) k

/-- The selected greatest Smith coefficient sends the image of every member
of the unlocalized bounded ground module into the localized original module.
This is the exact localized action that will be cleared in the next theorem. -/
theorem localizedSecondVariableSmithCoefficient_smul_localizationMap_mem_original
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (i : localizedSecondVariableSmithIndex I k)
    (h : localizedSecondVariableIsGreatestRemainingDivisor I k ∅ i)
    (x : secondVariableBoundedAmbient P n k)
    (hx : x ∈ secondVariableGroundModule I k) :
    localizedSecondVariableSmithCoefficients I k i •
        secondVariableBoundedLocalizationMap (P := P) (n := n) k x ∈
      localizedSecondVariableOriginalModule I k := by
  let f := secondVariableBoundedLocalizationMap (P := P) (n := n) k
  have hfx : f x ∈ localizedSecondVariableGroundModule I k := by
    exact ⟨x, hx, 1, by simp [f]⟩
  rw [localizedSecondVariableGroundModule_eq_moduleQuotientBySmithCoefficient
    I k i h] at hfx
  exact (SmithGroundReciprocity.mem_moduleQuotientByIdeal
    (localizedSecondVariableOriginalModule I k)
    (Ideal.span
      ({localizedSecondVariableSmithCoefficients I k i} :
        Set (secondVariablePID P n)))
    (f x)).mp hfx _ (Ideal.subset_span (by simp))

/-- A nonzero integral numerator exists for the selected localized Smith
coefficient, and it satisfies the bounded-module denominator action required
by equation (33).

The first returned denominator clears the coefficients of the Smith element
itself.  The denominator returned for each `x` clears membership in the
localized original module.  Both lie in the literal submonoid of nonzero
polynomials in the genuinely later variables. -/
theorem exists_nonzero_integralSmithNumerator_with_denominator_action
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (i : localizedSecondVariableSmithIndex I k)
    (h : localizedSecondVariableIsGreatestRemainingDivisor I k ∅ i) :
    ∃ a : Polynomial (MvPolynomial (Fin n) P), a ≠ 0 ∧
      ∃ s : lateVariableDenominators (P := P) (n := n),
        localizedSecondVariableSmithCoefficients I k i *
            Polynomial.map
              (algebraMap (MvPolynomial (Fin n) P)
                (FractionRing (MvPolynomial (Fin n) P)))
              (s : Polynomial (MvPolynomial (Fin n) P)) =
          Polynomial.map
            (algebraMap (MvPolynomial (Fin n) P)
              (FractionRing (MvPolynomial (Fin n) P))) a ∧
        ∀ x : secondVariableBoundedAmbient P n k,
          x ∈ secondVariableGroundModule I k →
            ∃ d : lateVariableDenominators (P := P) (n := n),
              (d : Polynomial (MvPolynomial (Fin n) P)) • (a • x) ∈
                secondVariableOriginalModule I k := by
  let A := Polynomial (MvPolynomial (Fin n) P)
  let L := secondVariablePID P n
  let D := lateVariableDenominators (P := P) (n := n)
  let e := localizedSecondVariableSmithCoefficients I k i
  let φ : A →+* L := algebraMap A L
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj D e
  have hsφ : e * φ (s : A) = φ a := by
    simpa [φ, A, L] using hs
  have hsOut :
      e * Polynomial.map
            (algebraMap (MvPolynomial (Fin n) P)
              (FractionRing (MvPolynomial (Fin n) P))) (s : A) =
        Polynomial.map
          (algebraMap (MvPolynomial (Fin n) P)
            (FractionRing (MvPolynomial (Fin n) P))) a := by
    simpa [φ, A, L] using hsφ
  have hsUnit : IsUnit (φ (s : A)) := by
    simpa [φ, A, L] using (IsLocalization.map_units L s)
  have ha : a ≠ 0 := by
    intro ha0
    have hprod : e * φ (s : A) ≠ 0 :=
      mul_ne_zero (localizedSecondVariableSmithCoefficients_ne_zero I k i)
        hsUnit.ne_zero
    apply hprod
    simpa [ha0] using hsφ
  refine ⟨a, ha, s, hsOut, ?_⟩
  intro x hx
  have hex : e •
        secondVariableBoundedLocalizationMap (P := P) (n := n) k x ∈
      localizedSecondVariableOriginalModule I k :=
    localizedSecondVariableSmithCoefficient_smul_localizationMap_mem_original
      I k i h x hx
  have hax : φ a •
        secondVariableBoundedLocalizationMap (P := P) (n := n) k x ∈
      localizedSecondVariableOriginalModule I k := by
    have hscaled := (localizedSecondVariableOriginalModule I k).smul_mem
      (φ (s : A)) hex
    rw [← hsφ]
    simpa only [← mul_smul, mul_comm] using hscaled
  have hax' : algebraMap A L a •
        secondVariableBoundedLocalizationMap (P := P) (n := n) k x ∈
      localizedSecondVariableOriginalModule I k := by
    simpa [φ] using hax
  exact
    LocalizedSubmoduleDenominator.exists_denominator_smul_smul_mem_of_algebraMap_smul_mem_localized
        (A := A) (L := L)
        D (secondVariableBoundedLocalizationMap (P := P) (n := n) k)
        (secondVariableOriginalModule I k) a x hax'

#print axioms localizedSecondVariableSmithCoefficient_smul_localizationMap_mem_original
#print axioms exists_nonzero_integralSmithNumerator_with_denominator_action

end

end RegularIdealDecomposition

#print axioms LocalizedSubmoduleDenominator.exists_denominator_smul_mem_of_map_mem_localized
#print axioms LocalizedSubmoduleDenominator.exists_denominator_smul_smul_mem_of_algebraMap_smul_mem_localized

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
