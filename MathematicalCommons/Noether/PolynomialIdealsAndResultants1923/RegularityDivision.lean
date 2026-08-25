import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.RegularitySpecialization
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Monic

/-!
# Hentzelt--Noether regular division substrate

Module for P22 equation (21), controlled witness `NOETH-DE-ED-0014`,
SHA-256 `EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
lines 13134--13139. A polynomial regular in the first variable can be scaled
to a monic univariate polynomial over the remaining-variable coefficient ring,
so every polynomial has a representative of smaller first-variable degree.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open MvPolynomial
open RegularitySpecialization

namespace RegularityDivision

noncomputable section

variable {P : Type*} [Field P]
variable {n k : ℕ}

private lemma degreeOf_zero_eq_totalDegree_of_regular
    (C : MvPolynomial (Fin (n + 1)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 1)) k C) :
    C.degreeOf 0 = k := by
  apply le_antisymm
  · exact (MvPolynomial.degreeOf_le_totalDegree C 0).trans_eq hC.1
  · have hmem : Finsupp.single (0 : Fin (n + 1)) k ∈ C.support := by
      rw [MvPolynomial.mem_support_iff]
      exact hC.2
    simpa using MvPolynomial.monomial_le_degreeOf 0 hmem

/-- The coefficient of first-variable degree `k` is exactly the constant
polynomial formed from the pure `x₀^k` coefficient. -/
theorem finSuccEquiv_coeff_eq_C_of_regular
    (C : MvPolynomial (Fin (n + 1)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 1)) k C) :
    (MvPolynomial.finSuccEquiv P n C).coeff k =
      MvPolynomial.C (MvPolynomial.coeff
        (Finsupp.single (0 : Fin (n + 1)) k) C) := by
  let c : P := MvPolynomial.coeff
    (Finsupp.single (0 : Fin (n + 1)) k) C
  have hcons : (0 : Fin n →₀ ℕ).cons k =
      Finsupp.single (0 : Fin (n + 1)) k := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  have hcoeff : (MvPolynomial.finSuccEquiv P n C).coeff k ≠ 0 := by
    intro hz
    have hz0 := congrArg (MvPolynomial.coeff (0 : Fin n →₀ ℕ)) hz
    apply hC.2
    rw [MvPolynomial.finSuccEquiv_coeff_coeff, hcons] at hz0
    exact hz0
  have htotal : ((MvPolynomial.finSuccEquiv P n C).coeff k).totalDegree = 0 := by
    have hle := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le C k hcoeff
    rw [hC.1] at hle
    omega
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htotal]
  congr 1
  have h := MvPolynomial.finSuccEquiv_coeff_coeff
    (0 : Fin n →₀ ℕ) C k
  rw [hcons] at h
  exact h

/-- The univariate view of a regular polynomial has degree exactly `k`. -/
theorem natDegree_finSuccEquiv_eq_of_regular
    (C : MvPolynomial (Fin (n + 1)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 1)) k C) :
    (MvPolynomial.finSuccEquiv P n C).natDegree = k := by
  rw [MvPolynomial.natDegree_finSuccEquiv]
  exact degreeOf_zero_eq_totalDegree_of_regular C hC

/-- Scale the regular divisor so that it becomes monic over the polynomial
ring in the remaining variables. -/
def monicRegularDivisor
    (C : MvPolynomial (Fin (n + 1)) P) (k : ℕ) :
    Polynomial (MvPolynomial (Fin n) P) :=
  let c := MvPolynomial.coeff
    (Finsupp.single (0 : Fin (n + 1)) k) C
  Polynomial.C (MvPolynomial.C c⁻¹) * MvPolynomial.finSuccEquiv P n C

/-- The scaled univariate view of a regular polynomial is monic. -/
theorem monic_monicRegularDivisor
    (C : MvPolynomial (Fin (n + 1)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 1)) k C) :
    (monicRegularDivisor C k).Monic := by
  let c : P := MvPolynomial.coeff
    (Finsupp.single (0 : Fin (n + 1)) k) C
  have hc : c ≠ 0 := hC.2
  have hcUnit : IsUnit (MvPolynomial.C c⁻¹ : MvPolynomial (Fin n) P) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero hc)).map MvPolynomial.C
  change (Polynomial.C (MvPolynomial.C c⁻¹) *
    MvPolynomial.finSuccEquiv P n C).leadingCoeff = 1
  rw [Polynomial.leadingCoeff_C_mul_of_isUnit hcUnit,
    Polynomial.leadingCoeff, natDegree_finSuccEquiv_eq_of_regular C hC,
    finSuccEquiv_coeff_eq_C_of_regular C hC]
  rw [← MvPolynomial.C_mul]
  simp [c, hC.2]

/-- Scaling by the inverse pure-power coefficient does not change the degree
of the regular divisor. -/
theorem natDegree_monicRegularDivisor
    (C : MvPolynomial (Fin (n + 1)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 1)) k C) :
    (monicRegularDivisor C k).natDegree = k := by
  let c : P := MvPolynomial.coeff
    (Finsupp.single (0 : Fin (n + 1)) k) C
  have hc : c ≠ 0 := hC.2
  have hcUnit : IsUnit (MvPolynomial.C c⁻¹ : MvPolynomial (Fin n) P) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero hc)).map MvPolynomial.C
  rw [monicRegularDivisor, Polynomial.natDegree_C_mul_of_isUnit hcUnit,
    natDegree_finSuccEquiv_eq_of_regular C hC]

/-- The canonical remainder of `H` after making the regular divisor monic. -/
def regularRemainder
    (C : MvPolynomial (Fin (n + 1)) P) (k : ℕ)
    (H : MvPolynomial (Fin (n + 1)) P) :
    Polynomial (MvPolynomial (Fin n) P) :=
  MvPolynomial.finSuccEquiv P n H %ₘ monicRegularDivisor C k

/-- The quotient is rescaled so that the decomposition uses the original
univariate view of `C`, rather than its monic scalar multiple. -/
def regularQuotient
    (C : MvPolynomial (Fin (n + 1)) P) (k : ℕ)
    (H : MvPolynomial (Fin (n + 1)) P) :
    Polynomial (MvPolynomial (Fin n) P) :=
  let c := MvPolynomial.coeff
    (Finsupp.single (0 : Fin (n + 1)) k) C
  Polynomial.C (MvPolynomial.C c⁻¹) *
    (MvPolynomial.finSuccEquiv P n H /ₘ monicRegularDivisor C k)

/-- Equation (21), in the univariate-over-the-remaining-variables model:
the canonical remainder plus the original divisor times a quotient recovers
`H`. -/
theorem regularRemainder_add_mul_regularQuotient
    (C H : MvPolynomial (Fin (n + 1)) P) (k : ℕ) :
    regularRemainder C k H +
        MvPolynomial.finSuccEquiv P n C * regularQuotient C k H =
      MvPolynomial.finSuccEquiv P n H := by
  have h := Polynomial.modByMonic_add_div
    (MvPolynomial.finSuccEquiv P n H) (monicRegularDivisor C k)
  simpa [regularRemainder, regularQuotient, monicRegularDivisor,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- The representative in equation (21) has first-variable degree strictly
less than the regular divisor's degree. The `WithBot` formulation also covers
the constant (`k = 0`) case without an artificial positivity assumption. -/
theorem degree_regularRemainder_lt
    (C H : MvPolynomial (Fin (n + 1)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 1)) k C) :
    (regularRemainder C k H).degree < (k : WithBot ℕ) := by
  have hmonic := monic_monicRegularDivisor C hC
  have hdegree := Polynomial.degree_modByMonic_lt
    (MvPolynomial.finSuccEquiv P n H) hmonic
  rw [Polynomial.degree_eq_natDegree hmonic.ne_zero,
    natDegree_monicRegularDivisor C hC] at hdegree
  exact hdegree

/-- The bounded representative transported back to the original multivariate
polynomial ring. -/
def boundedRepresentative
    (C : MvPolynomial (Fin (n + 1)) P) (k : ℕ)
    (H : MvPolynomial (Fin (n + 1)) P) :
    MvPolynomial (Fin (n + 1)) P :=
  (MvPolynomial.finSuccEquiv P n).symm (regularRemainder C k H)

/-- Multivariate form of equation (21): `H` is the bounded representative
plus a multiple of the regular polynomial `C`. -/
theorem exists_eq_boundedRepresentative_add_mul
    (C H : MvPolynomial (Fin (n + 1)) P) (k : ℕ) :
    ∃ Q : MvPolynomial (Fin (n + 1)) P,
      H = boundedRepresentative C k H + C * Q := by
  let Q := (MvPolynomial.finSuccEquiv P n).symm (regularQuotient C k H)
  refine ⟨Q, ?_⟩
  apply (MvPolynomial.finSuccEquiv P n).injective
  simpa [boundedRepresentative, Q] using
    (regularRemainder_add_mul_regularQuotient C H k).symm

/-- The transported representative retains the strict univariate degree bound
of equation (21). -/
theorem degree_finSuccEquiv_boundedRepresentative_lt
    (C H : MvPolynomial (Fin (n + 1)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 1)) k C) :
    (MvPolynomial.finSuccEquiv P n (boundedRepresentative C k H)).degree <
      (k : WithBot ℕ) := by
  simpa [boundedRepresentative] using degree_regularRemainder_lt C H hC

#print axioms finSuccEquiv_coeff_eq_C_of_regular
#print axioms natDegree_finSuccEquiv_eq_of_regular
#print axioms monicRegularDivisor
#print axioms monic_monicRegularDivisor
#print axioms natDegree_monicRegularDivisor
#print axioms regularRemainder
#print axioms regularQuotient
#print axioms regularRemainder_add_mul_regularQuotient
#print axioms degree_regularRemainder_lt
#print axioms boundedRepresentative
#print axioms exists_eq_boundedRepresentative_add_mul
#print axioms degree_finSuccEquiv_boundedRepresentative_lt

end

end RegularityDivision

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
