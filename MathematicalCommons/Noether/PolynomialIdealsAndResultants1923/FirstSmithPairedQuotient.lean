import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.FirstGroundModuleLocalization
import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.SmithPairedQuotient
import Mathlib.LinearAlgebra.StdBasis

/-!
# Hentzelt--Noether equation (24): the first localized Smith pair

Module for P22, controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
lines 13162--13173.

`FirstGroundModuleLocalization` constructs the actual cutoff-one ground and
original modules over the PID `Frac(P[x₃, ...])[x₂]` and proves that the
relative denominator has full finite rank.  This file is the thin
source-facing instantiation of `SmithPairedQuotient`: it chooses a finite
basis of the localized ground module, calls Mathlib's Smith construction, and
names the resulting vectors `ηᵢ` and coefficients `eᵢ` from equation (24).

The coefficients here are the nonzero diagonal entries selected by Mathlib's
Smith construction.  Mathlib v4.31 does not supply a divisibility-ordered
canonical elementary-divisor system through this API.  The determinant
identity is therefore an equality in the selected Smith bases; arbitrary
independent basis choices give equality only up to association.  No
determinant norm, resultant, compatible-zero, primitive-normalization, or
multiplicity conclusion is asserted here.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open Module MvPolynomial

namespace RegularIdealDecomposition

noncomputable section

variable {P : Type*} [Field P]
variable {n : ℕ}

/-- The standard basis of the finite localized coefficient-vector ambient
module. -/
noncomputable def localizedSecondVariableAmbientBasis (k : ℕ) :
    Basis (Fin k) (secondVariablePID P n)
      (localizedSecondVariableBoundedAmbient P n k) :=
  Pi.basisFun (secondVariablePID P n) (Fin k)

/-- The finite rank and basis of the localized ground module supplied by
`Submodule.basisOfPid`. -/
noncomputable def localizedSecondVariableGroundBasisSigma
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    Σ ρ : ℕ, Basis (Fin ρ) (secondVariablePID P n)
      (localizedSecondVariableGroundModule I k) :=
  Submodule.basisOfPid
    (localizedSecondVariableAmbientBasis (P := P) (n := n) k)
    (localizedSecondVariableGroundModule I k)

/-- The source-facing finite rank `ρ` selected by `basisOfPid`. -/
noncomputable def localizedSecondVariableSmithRank
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) : ℕ :=
  (localizedSecondVariableGroundBasisSigma I k).1

/-- The finite index type for the first localized Smith bases. -/
abbrev localizedSecondVariableSmithIndex
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :=
  Fin (localizedSecondVariableSmithRank I k)

/-- The initial finite basis passed to Mathlib's Smith construction. -/
noncomputable def localizedSecondVariableGroundBasis
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    Basis (localizedSecondVariableSmithIndex I k)
      (secondVariablePID P n)
      (localizedSecondVariableGroundModule I k) := by
  change Basis
    (Fin (localizedSecondVariableGroundBasisSigma I k).1)
    (secondVariablePID P n)
    (localizedSecondVariableGroundModule I k)
  exact (localizedSecondVariableGroundBasisSigma I k).2

/-- The localized numerator Smith basis; its vectors are the source's
`η₁, ..., ηρ`. -/
noncomputable def localizedSecondVariableEtaBasis
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    Basis (localizedSecondVariableSmithIndex I k)
      (secondVariablePID P n)
      (localizedSecondVariableGroundModule I k) :=
  SmithPairedQuotient.relativeSmithTopBasis
    (localizedSecondVariableGroundModule I k)
    (localizedSecondVariableOriginalModule I k)
    (localizedSecondVariableGroundBasis I k)
    (finrank_localizedSecondVariable_relativeDenominator_eq I k)

/-- The Smith basis of the actual localized relative denominator. -/
noncomputable def localizedSecondVariableDenominatorBasis
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    Basis (localizedSecondVariableSmithIndex I k)
      (secondVariablePID P n)
      (CommonTailQuotient.relativeDenominator
        (R := secondVariablePID P n)
        (E := localizedSecondVariableBoundedAmbient P n k)
        (localizedSecondVariableGroundModule I k)
        (localizedSecondVariableOriginalModule I k)) :=
  SmithPairedQuotient.relativeSmithBottomBasis
    (localizedSecondVariableGroundModule I k)
    (localizedSecondVariableOriginalModule I k)
    (localizedSecondVariableGroundBasis I k)
    (finrank_localizedSecondVariable_relativeDenominator_eq I k)

/-- The localized diagonal coefficients corresponding to the source's
`e₁, ..., eρ`. -/
noncomputable def localizedSecondVariableSmithCoefficients
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    localizedSecondVariableSmithIndex I k → secondVariablePID P n :=
  SmithPairedQuotient.relativeSmithCoefficients
    (localizedSecondVariableGroundModule I k)
    (localizedSecondVariableOriginalModule I k)
    (localizedSecondVariableGroundBasis I k)
    (finrank_localizedSecondVariable_relativeDenominator_eq I k)

/-- Equation (24): the denominator Smith-basis vector is `eᵢ • ηᵢ` in
the localized ground module. -/
@[simp]
theorem localizedSecondVariableDenominatorBasis_eq_smul_eta
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (i : localizedSecondVariableSmithIndex I k) :
    ((localizedSecondVariableDenominatorBasis I k i :
        CommonTailQuotient.relativeDenominator
          (R := secondVariablePID P n)
          (E := localizedSecondVariableBoundedAmbient P n k)
          (localizedSecondVariableGroundModule I k)
          (localizedSecondVariableOriginalModule I k)) :
      localizedSecondVariableGroundModule I k) =
        localizedSecondVariableSmithCoefficients I k i •
          localizedSecondVariableEtaBasis I k i := by
  exact SmithPairedQuotient.relativeSmithBottomBasis_eq_smul
    (localizedSecondVariableGroundModule I k)
    (localizedSecondVariableOriginalModule I k)
    (localizedSecondVariableGroundBasis I k)
    (finrank_localizedSecondVariable_relativeDenominator_eq I k)
    i

/-- Each actual vector `eᵢ • ηᵢ` belongs to the localized original
module. -/
theorem localizedSecondVariable_smul_eta_mem_original
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (i : localizedSecondVariableSmithIndex I k) :
    ((localizedSecondVariableSmithCoefficients I k i •
        localizedSecondVariableEtaBasis I k i :
      localizedSecondVariableGroundModule I k) :
        localizedSecondVariableBoundedAmbient P n k) ∈
      localizedSecondVariableOriginalModule I k := by
  rw [← localizedSecondVariableDenominatorBasis_eq_smul_eta]
  exact SmithPairedQuotient.relativeSmithBottomBasis_mem
    (localizedSecondVariableGroundModule I k)
    (localizedSecondVariableOriginalModule I k)
    (localizedSecondVariableGroundBasis I k)
    (finrank_localizedSecondVariable_relativeDenominator_eq I k)
    i

/-- Every localized Smith coefficient `eᵢ` is nonzero. -/
theorem localizedSecondVariableSmithCoefficients_ne_zero
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (i : localizedSecondVariableSmithIndex I k) :
    localizedSecondVariableSmithCoefficients I k i ≠ 0 := by
  exact SmithPairedQuotient.relativeSmithCoefficients_ne_zero
    (localizedSecondVariableGroundModule I k)
    (localizedSecondVariableOriginalModule I k)
    (localizedSecondVariableGroundBasis I k)
    (finrank_localizedSecondVariable_relativeDenominator_eq I k)
    i

/-- The actual first localized quotient is the product of the cyclic
quotients by the principal ideals generated by the selected `eᵢ`. -/
noncomputable def localizedSecondVariableRelativeQuotientEquivSmithCyclic
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) :
    CommonTailQuotient.relativeQuotient
        (R := secondVariablePID P n)
        (E := localizedSecondVariableBoundedAmbient P n k)
        (localizedSecondVariableGroundModule I k)
        (localizedSecondVariableOriginalModule I k) ≃ₗ[secondVariablePID P n]
      (∀ i : localizedSecondVariableSmithIndex I k,
        secondVariablePID P n ⧸
          Ideal.span
            ({localizedSecondVariableSmithCoefficients I k i} :
              Set (secondVariablePID P n))) :=
  SmithPairedQuotient.relativeQuotientEquivSmithCyclic
    (localizedSecondVariableGroundModule I k)
    (localizedSecondVariableOriginalModule I k)
    (localizedSecondVariableGroundBasis I k)
    (finrank_localizedSecondVariable_relativeDenominator_eq I k)

/-- In the selected localized Smith bases, the determinant of the relative
denominator inclusion is the product of the selected `eᵢ`. -/
noncomputable def det_localizedSecondVariableSmithBasisTransition_eq_prod :=
    fun (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ) =>
      SmithPairedQuotient.det_relativeSmithBasisTransition_eq_prod
        (localizedSecondVariableGroundModule I k)
        (localizedSecondVariableOriginalModule I k)
        (localizedSecondVariableGroundBasis I k)
        (finrank_localizedSecondVariable_relativeDenominator_eq I k)

#print axioms localizedSecondVariableAmbientBasis
#print axioms localizedSecondVariableGroundBasisSigma
#print axioms localizedSecondVariableSmithRank
#print axioms localizedSecondVariableSmithIndex
#print axioms localizedSecondVariableGroundBasis
#print axioms localizedSecondVariableEtaBasis
#print axioms localizedSecondVariableDenominatorBasis
#print axioms localizedSecondVariableSmithCoefficients
#print axioms localizedSecondVariableDenominatorBasis_eq_smul_eta
#print axioms localizedSecondVariable_smul_eta_mem_original
#print axioms localizedSecondVariableSmithCoefficients_ne_zero
#print axioms localizedSecondVariableRelativeQuotientEquivSmithCyclic
#print axioms det_localizedSecondVariableSmithBasisTransition_eq_prod

end

end RegularIdealDecomposition

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
