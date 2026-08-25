/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/

import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.CoordinateTransform
import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.FiniteParameterBridge
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Independent parameters for Hentzelt--Noether equation (12)

This module gives the lower-unitriangular coordinate equivalence its
source-faithful family of algebraically independent parameters.  The natural
parameter index consists of pairs `(mu, nu)` with `nu < mu`.  The generalized
finite-parameter bridge uses that pair type directly, without choosing an
enumeration by `Fin m`.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open MvPolynomial

namespace CoordinateShear.IndependentParameters

noncomputable section

variable {P : Type*} [Field P]
variable {n : ℕ}

/-- The genuinely independent parameter positions in a strictly lower
triangular `n`-by-`n` matrix: pairs `(mu, nu)` with `nu < mu`. -/
abbrev LowerParameter (n : ℕ) :=
  {p : Fin n × Fin n // p.2 < p.1}

/-- The generic strictly lower-triangular coefficient matrix over the rational
function field in one variable for every pair `(mu, nu)` with `nu < mu`.
Entries on and above the diagonal are zero and are ignored by equation (12). -/
def independentLowerMatrix (P : Type*) [Field P] (i j : Fin n) :
    FractionRing (MvPolynomial (LowerParameter n) P) :=
  if h : j < i then
    algebraMap (MvPolynomial (LowerParameter n) P)
      (FractionRing (MvPolynomial (LowerParameter n) P))
      (X (⟨(i, j), h⟩ : LowerParameter n))
  else 0

/-- The lower-triangular coefficient variables remain algebraically
independent after embedding the parameter-polynomial ring into its fraction
field. -/
theorem independentParameterVariables_algebraicIndependent :
    AlgebraicIndependent P
      (fun p : LowerParameter n ↦
        algebraMap (MvPolynomial (LowerParameter n) P)
          (FractionRing (MvPolynomial (LowerParameter n) P)) (X p)) := by
  let ι : MvPolynomial (LowerParameter n) P →ₐ[P]
      FractionRing (MvPolynomial (LowerParameter n) P) :=
    IsScalarTower.toAlgHom P _ _
  have hι : Function.Injective ι :=
    IsFractionRing.injective
      (MvPolynomial (LowerParameter n) P)
      (FractionRing (MvPolynomial (LowerParameter n) P))
  change AlgebraicIndependent P
    (ι ∘ (X : LowerParameter n → MvPolynomial (LowerParameter n) P))
  exact (MvPolynomial.algebraicIndependent_X (LowerParameter n) P).map' hι

@[simp]
theorem independentLowerMatrix_of_lt (i j : Fin n) (h : j < i) :
    independentLowerMatrix P i j =
      algebraMap (MvPolynomial (LowerParameter n) P)
        (FractionRing (MvPolynomial (LowerParameter n) P))
        (X (⟨(i, j), h⟩ : LowerParameter n)) := by
  simp [independentLowerMatrix, h]

@[simp]
theorem independentLowerMatrix_of_not_lt (i j : Fin n) (h : ¬j < i) :
    independentLowerMatrix P i j = 0 := by
  simp [independentLowerMatrix, h]

/-- Equation (12) over the rational function field in its natural family of
independent parameters. -/
def independentLowerUnitriangularEquiv (P : Type*) [Field P] :
    MvPolynomial (Fin n) (FractionRing (MvPolynomial (LowerParameter n) P)) ≃ₐ[
      FractionRing (MvPolynomial (LowerParameter n) P)]
    MvPolynomial (Fin n) (FractionRing (MvPolynomial (LowerParameter n) P)) :=
  CoordinateShear.lowerUnitriangularEquiv (independentLowerMatrix P)

/-- The generator formula for equation (12).  The theorem
`independentLowerMatrix_of_lt` identifies each displayed coefficient with the
variable indexed by its unique lower-triangular pair `(i,j)`. -/
@[simp]
theorem independentLowerUnitriangularEquiv_X (i : Fin n) :
    independentLowerUnitriangularEquiv (P := P) (n := n) (X i) =
      X i + ∑ j ∈ Finset.Iio i,
        C (independentLowerMatrix P i j) * X j := by
  exact CoordinateShear.lowerUnitriangularEquiv_X
    (independentLowerMatrix P) i

/-- The natural independent-parameter equivalence directly instantiates the
`tau` argument of `genericTransformHom`. -/
@[simp]
theorem genericTransformHom_independent_X (i : Fin n) :
    genericTransformHom (P := P) (U := LowerParameter n)
        (independentLowerUnitriangularEquiv (P := P) (n := n)) (X i) =
      X i + ∑ j ∈ Finset.Iio i,
        C (independentLowerMatrix P i j) * X j := by
  change
    independentLowerUnitriangularEquiv (P := P) (n := n)
        (MvPolynomial.map
          (algebraMap P
            (FractionRing (MvPolynomial (LowerParameter n) P))) (X i)) = _
  rw [MvPolynomial.map_X]
  exact independentLowerUnitriangularEquiv_X i

/-- The source-faithful independent-parameter equivalence directly
instantiates the enumeration-free finite-parameter ground-ideal bridge. -/
theorem parameterCoefficient_mem_groundIdealAlong_independent
    (M : Submonoid
      (MvPolynomial (Fin n)
        (FractionRing (MvPolynomial (LowerParameter n) P))))
    (I : Ideal (MvPolynomial (Fin n) P))
    (phi Gamma :
      MvPolynomial (LowerParameter n)
        (MvPolynomial (Fin n) P))
    (hphi : parameterTransformHom (P := P)
      (U := LowerParameter n)
      (independentLowerUnitriangularEquiv (P := P) (n := n)) phi ∈ M)
    (hprod : phi * Gamma ∈
      Ideal.map
        (MvPolynomial.C : MvPolynomial (Fin n) P →+*
          MvPolynomial (LowerParameter n)
            (MvPolynomial (Fin n) P)) I)
    {gamma : MvPolynomial (Fin n) P} (hgamma : gamma ∈ Gamma.coeffs) :
    genericTransformHom (P := P) (U := LowerParameter n)
        (independentLowerUnitriangularEquiv (P := P) (n := n)) gamma ∈
      groundIdealAlong M
        (genericTransformIdeal (P := P) (U := LowerParameter n)
          (independentLowerUnitriangularEquiv (P := P) (n := n)) I) := by
  exact FiniteParameterBridge.parameterCoefficient_mem_groundIdealAlong_finite
    M I (independentLowerUnitriangularEquiv (P := P) (n := n))
    phi Gamma hphi hprod hgamma

#print axioms LowerParameter
#print axioms independentLowerMatrix
#print axioms independentParameterVariables_algebraicIndependent
#print axioms independentLowerMatrix_of_lt
#print axioms independentLowerMatrix_of_not_lt
#print axioms independentLowerUnitriangularEquiv
#print axioms independentLowerUnitriangularEquiv_X
#print axioms genericTransformHom_independent_X
#print axioms parameterCoefficient_mem_groundIdealAlong_independent

end

end CoordinateShear.IndependentParameters

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
