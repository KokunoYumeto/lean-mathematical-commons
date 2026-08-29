/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.FirstSmithGroundReciprocity
import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.FirstSmithAnnihilatorBounds

/-!
# Hentzelt--Noether: explicit greatest-coefficient bridge for Satz II and VIII

Module for P22, controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
Satz II and Definition VI--Satz VIII, lines 12815--12844 and 13323--13342.

`FirstSmithGroundReciprocity` states the two reciprocal Satz-II identities
under the explicit hypothesis that every selected Smith coefficient divides a
distinguished coefficient `e_i`.  `FirstSmithAnnihilatorBounds` replaces the
unavailable ordered greatest elementary divisor by the intrinsic ideal

`A = inf_j (e_j) = Ann (Pi j, R / (e_j))`.

This file connects those two formulations under the same visible hypothesis.
It proves `A = (e_i)`, transports the finite product bounds to

`e_i | prod_j e_j` and `prod_j e_j | e_i ^ card ι`,

and packages the result for the actual localized cutoff-one Smith pair.  It
does not prove that such an index exists, order or normalize Mathlib's selected
Smith coefficients, establish choice independence, identify the selected
product with Hentzelt's primitive resultant form `R^(1)`, identify `e_i` with
the historical primitive elementary-divisor form `E^(1)`, descend from the
coefficient localization, or construct later stages and equations (33)--(34).
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open Module MvPolynomial

namespace SmithGreatestCoefficientBridge

noncomputable section

variable {ι R K : Type*} [CommRing R]

/-- If every selected coefficient divides `e_i`, the intrinsic intersection
of the coefficient ideals is the displayed principal ideal `(e_i)`.  The
greatest-coefficient condition remains an explicit hypothesis. -/
theorem coefficientIdeal_eq_span_of_isGreatest
    (e : ι → R) (i : ι)
    (h : SmithScalarQuotients.IsGreatestRemainingDivisor e ∅ i) :
    SmithAnnihilatorBounds.coefficientIdeal e =
      Ideal.span ({e i} : Set R) := by
  rw [SmithAnnihilatorBounds.coefficientIdeal]
  apply le_antisymm
  · exact iInf_le _ i
  · apply le_iInf
    intro j
    exact Ideal.span_singleton_le_span_singleton.mpr
      (h.2 j (by simp))

/-- Under the explicit greatest-coefficient hypothesis, the distinguished
coefficient divides the finite coefficient product and that product divides
the `card ι`-th power of the distinguished coefficient. -/
theorem greatest_coefficient_product_divisibilities
    [Fintype ι] (e : ι → R) (i : ι)
    (h : SmithScalarQuotients.IsGreatestRemainingDivisor e ∅ i) :
    e i ∣ SmithAnnihilatorBounds.coefficientProduct e ∧
      SmithAnnihilatorBounds.coefficientProduct e ∣
        e i ^ Fintype.card ι := by
  classical
  have hideal := coefficientIdeal_eq_span_of_isGreatest e i h
  constructor
  · apply Ideal.mem_span_singleton.mp
    rw [← hideal]
    exact SmithAnnihilatorBounds.span_coefficientProduct_le_coefficientIdeal e
      (Ideal.subset_span (Set.mem_singleton _))
  · apply Ideal.mem_span_singleton.mp
    apply SmithAnnihilatorBounds.coefficientIdeal_pow_card_le_span_coefficientProduct e
    rw [hideal]
    exact Ideal.pow_mem_pow
      (Ideal.subset_span (Set.mem_singleton _))
      (Fintype.card ι)

/-- The finite coefficient product and the explicitly distinguished greatest
coefficient generate ideals with the same radical. -/
theorem radical_span_coefficientProduct_eq_span_of_isGreatest
    [Fintype ι] (e : ι → R) (i : ι)
    (h : SmithScalarQuotients.IsGreatestRemainingDivisor e ∅ i) :
    (Ideal.span ({SmithAnnihilatorBounds.coefficientProduct e} : Set R)).radical =
      (Ideal.span ({e i} : Set R)).radical := by
  have hdiv := greatest_coefficient_product_divisibilities e i h
  exact radical_span_eq_of_dvd_pow hdiv.1 (Fintype.card ι) hdiv.2

/-- The selected product and explicitly distinguished coefficient vanish
together after every map to a field.  This is an intrinsic localized Smith
consequence, not an identification with the historical primitive forms. -/
theorem map_coefficientProduct_eq_zero_iff_of_isGreatest
    [Fintype ι] [Field K] (φ : R →+* K) (e : ι → R) (i : ι)
    (h : SmithScalarQuotients.IsGreatestRemainingDivisor e ∅ i) :
    φ (SmithAnnihilatorBounds.coefficientProduct e) = 0 ↔ φ (e i) = 0 := by
  have hdiv := greatest_coefficient_product_divisibilities e i h
  exact map_eq_zero_iff_of_dvd_pow φ hdiv.1 (Fintype.card ι) hdiv.2

#print axioms coefficientIdeal_eq_span_of_isGreatest
#print axioms greatest_coefficient_product_divisibilities
#print axioms radical_span_coefficientProduct_eq_span_of_isGreatest
#print axioms map_coefficientProduct_eq_zero_iff_of_isGreatest

end

end SmithGreatestCoefficientBridge

namespace RegularIdealDecomposition

noncomputable section

variable {P : Type*} [Field P]
variable {n : ℕ}

/-- Under the same explicit greatest-coefficient hypothesis used in Satz II,
the annihilator of the actual localized first relative quotient is `(e_i)`. -/
theorem annihilator_localizedSecondVariableRelativeQuotient_eq_span_of_greatest
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (i : localizedSecondVariableSmithIndex I k)
    (h : localizedSecondVariableIsGreatestRemainingDivisor I k ∅ i) :
    Module.annihilator (secondVariablePID P n)
        (CommonTailQuotient.relativeQuotient
          (localizedSecondVariableGroundModule I k)
          (localizedSecondVariableOriginalModule I k)) =
      Ideal.span
        ({localizedSecondVariableSmithCoefficients I k i} :
          Set (secondVariablePID P n)) := by
  calc
    Module.annihilator (secondVariablePID P n)
        (CommonTailQuotient.relativeQuotient
          (localizedSecondVariableGroundModule I k)
          (localizedSecondVariableOriginalModule I k)) =
        SmithAnnihilatorBounds.coefficientIdeal
          (localizedSecondVariableSmithCoefficients I k) := by
      simpa only [SmithAnnihilatorBounds.coefficientIdeal] using
        (annihilator_localizedSecondVariableRelativeQuotient_eq_iInf I k)
    _ = Ideal.span
          ({localizedSecondVariableSmithCoefficients I k i} :
            Set (secondVariablePID P n)) :=
      SmithGreatestCoefficientBridge.coefficientIdeal_eq_span_of_isGreatest
        (localizedSecondVariableSmithCoefficients I k) i h

/-- Source-shaped generator divisibilities for the actual localized first
Smith pair, conditional on the displayed greatest-coefficient hypothesis. -/
theorem localizedSecondVariableSmith_greatest_product_divisibilities
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (i : localizedSecondVariableSmithIndex I k)
    (h : localizedSecondVariableIsGreatestRemainingDivisor I k ∅ i) :
    localizedSecondVariableSmithCoefficients I k i ∣
        localizedSecondVariableSmithCoefficientProduct I k ∧
      localizedSecondVariableSmithCoefficientProduct I k ∣
        localizedSecondVariableSmithCoefficients I k i ^
          localizedSecondVariableSmithRank I k := by
  simpa only [localizedSecondVariableSmithCoefficientProduct,
    localizedSecondVariableSmithIndex, Fintype.card_fin] using
    (SmithGreatestCoefficientBridge.greatest_coefficient_product_divisibilities
      (localizedSecondVariableSmithCoefficients I k) i h)

/-- The actual selected coefficient product and the explicitly distinguished
greatest coefficient generate ideals with the same radical. -/
theorem radical_span_localizedSecondVariableSmithCoefficientProduct_eq_span_of_greatest
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (i : localizedSecondVariableSmithIndex I k)
    (h : localizedSecondVariableIsGreatestRemainingDivisor I k ∅ i) :
    (Ideal.span ({localizedSecondVariableSmithCoefficientProduct I k} :
      Set (secondVariablePID P n))).radical =
        (Ideal.span
          ({localizedSecondVariableSmithCoefficients I k i} :
            Set (secondVariablePID P n))).radical := by
  rw [radical_span_localizedSecondVariableSmithCoefficientProduct_eq_annihilator,
    annihilator_localizedSecondVariableRelativeQuotient_eq_span_of_greatest
      I k i h]

/-- Combined localized Satz-II/Satz-VIII endpoint under one explicit
greatest-coefficient hypothesis.  It joins the two reciprocal quotient
operations, the quotient annihilator, and the finite product divisibilities.
No existence, canonical-order, primitive-form, or resultant claim is made. -/
theorem localizedSecondVariableSatzII_VIII_bridge_of_greatest
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (i : localizedSecondVariableSmithIndex I k)
    (h : localizedSecondVariableIsGreatestRemainingDivisor I k ∅ i) :
    ((localizedSecondVariableDenominatorCarrier I k).colon
        ((⊤ : Submodule (secondVariablePID P n)
          (localizedSecondVariableGroundCarrier I k)) :
          Set (localizedSecondVariableGroundCarrier I k)) =
        Ideal.span
          ({localizedSecondVariableSmithCoefficients I k i} :
            Set (secondVariablePID P n)) ∧
      localizedSecondVariableGroundModule I k =
        SmithGroundReciprocity.moduleQuotientByIdeal
          (localizedSecondVariableOriginalModule I k)
          (Ideal.span
            ({localizedSecondVariableSmithCoefficients I k i} :
              Set (secondVariablePID P n)))) ∧
    (Module.annihilator (secondVariablePID P n)
        (CommonTailQuotient.relativeQuotient
          (localizedSecondVariableGroundModule I k)
          (localizedSecondVariableOriginalModule I k)) =
        Ideal.span
          ({localizedSecondVariableSmithCoefficients I k i} :
            Set (secondVariablePID P n)) ∧
      localizedSecondVariableSmithCoefficients I k i ∣
          localizedSecondVariableSmithCoefficientProduct I k ∧
        localizedSecondVariableSmithCoefficientProduct I k ∣
          localizedSecondVariableSmithCoefficients I k i ^
            localizedSecondVariableSmithRank I k) := by
  refine ⟨localizedSecondVariableSatzII_reciprocity I k i h, ?_⟩
  refine ⟨
    annihilator_localizedSecondVariableRelativeQuotient_eq_span_of_greatest
      I k i h, ?_⟩
  exact localizedSecondVariableSmith_greatest_product_divisibilities I k i h

#print axioms annihilator_localizedSecondVariableRelativeQuotient_eq_span_of_greatest
#print axioms localizedSecondVariableSmith_greatest_product_divisibilities
#print axioms radical_span_localizedSecondVariableSmithCoefficientProduct_eq_span_of_greatest
#print axioms localizedSecondVariableSatzII_VIII_bridge_of_greatest

end

end RegularIdealDecomposition

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
