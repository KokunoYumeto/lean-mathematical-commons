import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.FirstSmithScalarQuotients
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Hentzelt--Noether Satz VIII: finite Smith annihilator bounds

Module for P22, controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
lines 13340--13342.

The opening algebraic step of Satz VIII says that the norm (the product of
the elementary divisors) is divisible by the greatest elementary divisor,
and conversely that a power of the greatest elementary divisor is divisible
by the norm.  Mathlib v4.31's selected Smith coefficients are not supplied
with a divisibility ordering.  We therefore use the intrinsic replacement

`A = annihilator (Pi i, R / (e_i)) = inf_i (e_i)`.

For a finite family of coefficients, with `D = prod_i e_i`, this file proves

`(D) <= A` and `A ^ card ι <= (D)`.

Over a principal ideal ring, if `a` is Mathlib's chosen generator of `A`,
these inclusions say `a ∣ D` and `D ∣ a ^ card ι`; in particular `(D)` and
`A` have the same radical.  The results are then instantiated for the actual
localized first Smith quotient and related to the source's scalar-colon
description.

This is the finite localized Smith-algebra kernel of Satz VIII.  It does not
identify `D` with Hentzelt's primitive resultant form `R^(i)`, identify `a`
with a normalized historical `E^(i)`, order the selected Smith coefficients,
prove choice independence, or treat later stages and equations (33)--(34).
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open Module MvPolynomial

namespace SmithAnnihilatorBounds

noncomputable section

variable {ι R Q : Type*}
variable [CommRing R]

/-- The intrinsic ideal attached to a family of cyclic Smith factors. -/
def coefficientIdeal (e : ι → R) : Ideal R :=
  ⨅ i, Ideal.span ({e i} : Set R)

/-- The finite product of a family of Smith coefficients. -/
def coefficientProduct [Fintype ι] (e : ι → R) : R :=
  ∏ i, e i

/-- The annihilator of a product of cyclic quotients is the intersection of
their defining principal ideals. -/
theorem annihilator_pi_quotients_eq_coefficientIdeal (e : ι → R) :
    Module.annihilator R
        (∀ i : ι, R ⧸ Ideal.span ({e i} : Set R)) =
      coefficientIdeal e := by
  rw [Module.annihilator_pi]
  simp only [Ideal.annihilator_quotient, coefficientIdeal]

/-- Transport the preceding annihilator computation across any displayed
Smith cyclic decomposition. -/
theorem annihilator_eq_coefficientIdeal_of_equiv
    [AddCommGroup Q] [Module R Q] (e : ι → R)
    (equiv : Q ≃ₗ[R] (∀ i : ι, R ⧸ Ideal.span ({e i} : Set R))) :
    Module.annihilator R Q = coefficientIdeal e := by
  rw [equiv.annihilator_eq,
    annihilator_pi_quotients_eq_coefficientIdeal]

/-- The principal ideal of the coefficient product lies in the intersection
of the individual coefficient ideals. -/
theorem span_coefficientProduct_le_coefficientIdeal
    [Fintype ι] (e : ι → R) :
    Ideal.span ({coefficientProduct e} : Set R) ≤ coefficientIdeal e := by
  classical
  rw [coefficientProduct, coefficientIdeal,
    ← Finset.inf_univ_eq_iInf, ← Ideal.prod_span_singleton]
  exact Ideal.prod_le_inf

/-- The `card ι`-th power of the coefficient-ideal intersection lies in the
principal ideal of the coefficient product. -/
theorem coefficientIdeal_pow_card_le_span_coefficientProduct
    [Fintype ι] (e : ι → R) :
    coefficientIdeal e ^ Fintype.card ι ≤
      Ideal.span ({coefficientProduct e} : Set R) := by
  classical
  rw [coefficientIdeal, coefficientProduct,
    ← Finset.inf_univ_eq_iInf, ← Finset.card_univ,
    ← Ideal.prod_span_singleton]
  apply Finset.pow_card_le_prod
  intro i _
  exact Finset.inf_le (Finset.mem_univ i)

/-- The two finite product bounds, transported to the annihilator of a module
with the displayed cyclic decomposition. -/
theorem annihilator_product_bounds_of_equiv
    [Fintype ι] [AddCommGroup Q] [Module R Q] (e : ι → R)
    (equiv : Q ≃ₗ[R] (∀ i : ι, R ⧸ Ideal.span ({e i} : Set R))) :
    Ideal.span ({coefficientProduct e} : Set R) ≤
        Module.annihilator R Q ∧
      (Module.annihilator R Q) ^ Fintype.card ι ≤
        Ideal.span ({coefficientProduct e} : Set R) := by
  rw [annihilator_eq_coefficientIdeal_of_equiv e equiv]
  exact ⟨span_coefficientProduct_le_coefficientIdeal e,
    coefficientIdeal_pow_card_le_span_coefficientProduct e⟩

/-- In a principal ideal ring, the annihilator generator divides the product
of the displayed Smith coefficients. -/
theorem annihilator_generator_dvd_coefficientProduct_of_equiv
    [Fintype ι] [AddCommGroup Q] [Module R Q]
    [IsPrincipalIdealRing R] (e : ι → R)
    (equiv : Q ≃ₗ[R] (∀ i : ι, R ⧸ Ideal.span ({e i} : Set R))) :
    Submodule.IsPrincipal.generator (Module.annihilator R Q) ∣
      coefficientProduct e := by
  rw [← Submodule.IsPrincipal.mem_iff_generator_dvd]
  exact (annihilator_product_bounds_of_equiv e equiv).1
    (Ideal.subset_span (Set.mem_singleton _))

/-- Conversely, the coefficient product divides the `card ι`-th power of
the annihilator generator. -/
theorem coefficientProduct_dvd_annihilator_generator_pow_card_of_equiv
    [Fintype ι] [AddCommGroup Q] [Module R Q]
    [IsPrincipalIdealRing R] (e : ι → R)
    (equiv : Q ≃ₗ[R] (∀ i : ι, R ⧸ Ideal.span ({e i} : Set R))) :
    coefficientProduct e ∣
      Submodule.IsPrincipal.generator (Module.annihilator R Q) ^
        Fintype.card ι := by
  apply Ideal.mem_span_singleton.mp
  apply (annihilator_product_bounds_of_equiv e equiv).2
  exact Ideal.pow_mem_pow
    (Submodule.IsPrincipal.generator_mem (Module.annihilator R Q))
    (Fintype.card ι)

/-- The product ideal and the intrinsic annihilator have the same radical.
The empty-index case is included: both ideals are then the unit ideal. -/
theorem radical_span_coefficientProduct_eq_annihilator_of_equiv
    [Fintype ι] [AddCommGroup Q] [Module R Q] (e : ι → R)
    (equiv : Q ≃ₗ[R] (∀ i : ι, R ⧸ Ideal.span ({e i} : Set R))) :
    (Ideal.span ({coefficientProduct e} : Set R)).radical =
      (Module.annihilator R Q).radical := by
  classical
  have hbounds := annihilator_product_bounds_of_equiv e equiv
  by_cases hcard : Fintype.card ι = 0
  · have hspan :
        Ideal.span ({coefficientProduct e} : Set R) = ⊤ := by
      apply top_unique
      simpa only [hcard, pow_zero, Ideal.one_eq_top] using hbounds.2
    have hann : Module.annihilator R Q = ⊤ := by
      apply top_unique
      simpa only [hspan] using hbounds.1
    rw [hspan, hann]
  · apply le_antisymm
    · exact Ideal.radical_mono hbounds.1
    · rw [← Ideal.radical_pow (Module.annihilator R Q) hcard]
      exact Ideal.radical_mono hbounds.2

#print axioms coefficientIdeal
#print axioms coefficientProduct
#print axioms annihilator_pi_quotients_eq_coefficientIdeal
#print axioms annihilator_eq_coefficientIdeal_of_equiv
#print axioms span_coefficientProduct_le_coefficientIdeal
#print axioms coefficientIdeal_pow_card_le_span_coefficientProduct
#print axioms annihilator_product_bounds_of_equiv
#print axioms annihilator_generator_dvd_coefficientProduct_of_equiv
#print axioms coefficientProduct_dvd_annihilator_generator_pow_card_of_equiv
#print axioms radical_span_coefficientProduct_eq_annihilator_of_equiv

end

end SmithAnnihilatorBounds

namespace RegularIdealDecomposition

noncomputable section

variable {P : Type*} [Field P]
variable {n : ℕ}

/-- The product of the actual selected first localized Smith coefficients. -/
noncomputable def localizedSecondVariableSmithCoefficientProduct
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    secondVariablePID P n :=
  SmithAnnihilatorBounds.coefficientProduct
    (localizedSecondVariableSmithCoefficients I k)

/-- The annihilator of the actual first localized relative quotient is the
intersection of its selected coefficient ideals. -/
theorem annihilator_localizedSecondVariableRelativeQuotient_eq_iInf
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    Module.annihilator (secondVariablePID P n)
        (CommonTailQuotient.relativeQuotient
          (localizedSecondVariableGroundModule I k)
          (localizedSecondVariableOriginalModule I k)) =
      ⨅ i : localizedSecondVariableSmithIndex I k,
        Ideal.span ({localizedSecondVariableSmithCoefficients I k i} :
          Set (secondVariablePID P n)) := by
  simpa only [SmithAnnihilatorBounds.coefficientIdeal] using
    (SmithAnnihilatorBounds.annihilator_eq_coefficientIdeal_of_equiv
      (localizedSecondVariableSmithCoefficients I k)
      (localizedSecondVariableRelativeQuotientEquivSmithCyclic I k))

/-- The same annihilator is the scalar colon of the actual relative
denominator by its whole localized ground carrier. -/
theorem annihilator_localizedSecondVariableRelativeQuotient_eq_colon
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    Module.annihilator (secondVariablePID P n)
        (CommonTailQuotient.relativeQuotient
          (localizedSecondVariableGroundModule I k)
          (localizedSecondVariableOriginalModule I k)) =
      (localizedSecondVariableDenominatorCarrier I k).colon
        ((⊤ : Submodule (secondVariablePID P n)
          (localizedSecondVariableGroundCarrier I k)) :
          Set (localizedSecondVariableGroundCarrier I k)) := by
  simpa only [Submodule.top_coe] using
    (Submodule.annihilator_quotient
      (R := secondVariablePID P n)
      (M := localizedSecondVariableGroundCarrier I k)
      (N := localizedSecondVariableDenominatorCarrier I k))

/-- Finite localized Satz-VIII bounds: the selected coefficient-product
ideal lies in the quotient annihilator, and the rank-th power of that
annihilator lies in the product ideal. -/
theorem localizedSecondVariableSmith_annihilator_product_bounds
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    Ideal.span ({localizedSecondVariableSmithCoefficientProduct I k} :
        Set (secondVariablePID P n)) ≤
        Module.annihilator (secondVariablePID P n)
          (CommonTailQuotient.relativeQuotient
            (localizedSecondVariableGroundModule I k)
            (localizedSecondVariableOriginalModule I k)) ∧
      (Module.annihilator (secondVariablePID P n)
        (CommonTailQuotient.relativeQuotient
          (localizedSecondVariableGroundModule I k)
          (localizedSecondVariableOriginalModule I k))) ^
          localizedSecondVariableSmithRank I k ≤
        Ideal.span ({localizedSecondVariableSmithCoefficientProduct I k} :
          Set (secondVariablePID P n)) := by
  simpa only [localizedSecondVariableSmithCoefficientProduct,
    localizedSecondVariableSmithIndex, Fintype.card_fin] using
    (SmithAnnihilatorBounds.annihilator_product_bounds_of_equiv
      (localizedSecondVariableSmithCoefficients I k)
      (localizedSecondVariableRelativeQuotientEquivSmithCyclic I k))

/-- Generator form of the two finite localized divisibilities in Satz VIII.
The chosen annihilator generator replaces the unavailable ordered greatest
Smith coefficient. -/
theorem localizedSecondVariableSmith_annihilator_generator_divisibilities
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    Submodule.IsPrincipal.generator
        (Module.annihilator (secondVariablePID P n)
          (CommonTailQuotient.relativeQuotient
            (localizedSecondVariableGroundModule I k)
            (localizedSecondVariableOriginalModule I k))) ∣
        localizedSecondVariableSmithCoefficientProduct I k ∧
      localizedSecondVariableSmithCoefficientProduct I k ∣
        Submodule.IsPrincipal.generator
          (Module.annihilator (secondVariablePID P n)
            (CommonTailQuotient.relativeQuotient
              (localizedSecondVariableGroundModule I k)
              (localizedSecondVariableOriginalModule I k))) ^
          localizedSecondVariableSmithRank I k := by
  constructor
  · simpa only [localizedSecondVariableSmithCoefficientProduct] using
      (SmithAnnihilatorBounds.annihilator_generator_dvd_coefficientProduct_of_equiv
        (localizedSecondVariableSmithCoefficients I k)
        (localizedSecondVariableRelativeQuotientEquivSmithCyclic I k))
  · simpa only [localizedSecondVariableSmithCoefficientProduct,
      localizedSecondVariableSmithIndex, Fintype.card_fin] using
      (SmithAnnihilatorBounds.coefficientProduct_dvd_annihilator_generator_pow_card_of_equiv
        (localizedSecondVariableSmithCoefficients I k)
        (localizedSecondVariableRelativeQuotientEquivSmithCyclic I k))

/-- The actual selected coefficient-product ideal and the actual quotient
annihilator have the same radical. -/
theorem radical_span_localizedSecondVariableSmithCoefficientProduct_eq_annihilator
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    (Ideal.span ({localizedSecondVariableSmithCoefficientProduct I k} :
      Set (secondVariablePID P n))).radical =
        (Module.annihilator (secondVariablePID P n)
          (CommonTailQuotient.relativeQuotient
            (localizedSecondVariableGroundModule I k)
            (localizedSecondVariableOriginalModule I k))).radical := by
  simpa only [localizedSecondVariableSmithCoefficientProduct] using
    (SmithAnnihilatorBounds.radical_span_coefficientProduct_eq_annihilator_of_equiv
      (localizedSecondVariableSmithCoefficients I k)
      (localizedSecondVariableRelativeQuotientEquivSmithCyclic I k))

#print axioms localizedSecondVariableSmithCoefficientProduct
#print axioms annihilator_localizedSecondVariableRelativeQuotient_eq_iInf
#print axioms annihilator_localizedSecondVariableRelativeQuotient_eq_colon
#print axioms localizedSecondVariableSmith_annihilator_product_bounds
#print axioms localizedSecondVariableSmith_annihilator_generator_divisibilities
#print axioms radical_span_localizedSecondVariableSmithCoefficientProduct_eq_annihilator

end


end RegularIdealDecomposition

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
