import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.RegularQuotient
import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.CommonTailQuotient
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Hentzelt--Noether Satz VII: the first paired finite-stage quotient

Module for P22, controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
  lines 13141--13160. Equations (22)--(23) replace the two containing ideals by
bounded coefficient modules plus the same independent principal tail. The
source then identifies their quotient with the quotient of the bounded
modules and observes that the latter is finite.

Historical divisibility is typed explicitly in modern orientation: the
denominator ideal `M` satisfies `M ≤ G`. The quotient equivalence specializes
`CommonTailQuotient.commonTailQuotientEquiv`; finite generation additionally
uses that a bounded coefficient module embeds into the finite module of
polynomials of degree `< k` over the Noetherian remaining-variable ring.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open MvPolynomial
open RegularitySpecialization

namespace RegularIdealDecomposition

noncomputable section

variable {P : Type*} [Field P]
variable {n k : ℕ}

/-- Inclusion of ideals restricts to inclusion of their bounded coefficient
modules. -/
theorem boundedPart_mono
    {M G : Ideal (Polynomial (MvPolynomial (Fin n) P))} (hMG : M ≤ G) :
    boundedPart M k ≤ boundedPart G k := by
  intro f hf
  exact ⟨hMG hf.1, hf.2⟩

/-- Every bounded part lies in the ambient degree-`< k` coefficient module. -/
theorem boundedPart_le_degreeLT
    (I : Ideal (Polynomial (MvPolynomial (Fin n) P))) :
    boundedPart I k ≤ Polynomial.degreeLT (MvPolynomial (Fin n) P) k :=
  inf_le_right

/-- A bounded coefficient module is finite over the polynomial ring in the
remaining variables. -/
theorem boundedPart_moduleFinite
    (I : Ideal (Polynomial (MvPolynomial (Fin n) P))) :
    Module.Finite (MvPolynomial (Fin n) P) (boundedPart I k) := by
  letI : IsNoetherian (MvPolynomial (Fin n) P)
      (Polynomial.degreeLT (MvPolynomial (Fin n) P) k) :=
    isNoetherian_of_linearEquiv
      (Polynomial.degreeLTEquiv (MvPolynomial (Fin n) P) k).symm
  exact Module.Finite.of_injective
    (Submodule.inclusion (boundedPart_le_degreeLT I))
    (Submodule.inclusion_injective (boundedPart_le_degreeLT I))

/-- For two ideals containing the same regular polynomial, their relative
quotient is the relative quotient of the bounded coefficient modules. This is
the concrete first-stage `G₁/M₁ ≃ G₁*/M₁*` passage after equation (23). -/
noncomputable def regularPairedQuotientEquivBounded
    (G M : Ideal (Polynomial (MvPolynomial (Fin n) P)))
    (C : MvPolynomial (Fin (n + 1)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 1)) k C)
    (hCM : MvPolynomial.finSuccEquiv P n C ∈ M)
    (hMG : M ≤ G) :
    CommonTailQuotient.relativeQuotient
        (G.restrictScalars (MvPolynomial (Fin n) P))
        (M.restrictScalars (MvPolynomial (Fin n) P)) ≃ₗ[
      MvPolynomial (Fin n) P]
      CommonTailQuotient.relativeQuotient
        (boundedPart G k) (boundedPart M k) := by
  rw [regularIdeal_eq_boundedPart_sup_principalTail G C hC (hMG hCM),
    regularIdeal_eq_boundedPart_sup_principalTail M C hC hCM]
  exact CommonTailQuotient.commonTailQuotientEquiv
    (boundedPart G k) (boundedPart M k) (principalTail C)
    (boundedPart_mono hMG) (boundedPart_disjoint_principalTail G C hC)

/-- The paired quotient in the first regular stage is a finite module over the
remaining-variable coefficient ring. -/
theorem regularPairedQuotient_moduleFinite
    (G M : Ideal (Polynomial (MvPolynomial (Fin n) P)))
    (C : MvPolynomial (Fin (n + 1)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 1)) k C)
    (hCM : MvPolynomial.finSuccEquiv P n C ∈ M)
    (hMG : M ≤ G) :
    Module.Finite (MvPolynomial (Fin n) P)
      (CommonTailQuotient.relativeQuotient
        (G.restrictScalars (MvPolynomial (Fin n) P))
        (M.restrictScalars (MvPolynomial (Fin n) P))) := by
  letI : Module.Finite (MvPolynomial (Fin n) P) (boundedPart G k) :=
    boundedPart_moduleFinite G
  letI : Module.Finite (MvPolynomial (Fin n) P)
      (CommonTailQuotient.relativeQuotient
        (boundedPart G k) (boundedPart M k)) :=
    Module.Finite.quotient _ _
  exact Module.Finite.equiv
    (regularPairedQuotientEquivBounded G M C hC hCM hMG).symm

/-- Every class of the paired ideal quotient has a representative in the
bounded numerator module, matching the representative-system argument on
line 13160. -/
theorem exists_regularPaired_boundedRepresentative
    (G M : Ideal (Polynomial (MvPolynomial (Fin n) P)))
    (C : MvPolynomial (Fin (n + 1)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 1)) k C)
    (hCM : MvPolynomial.finSuccEquiv P n C ∈ M)
    (hMG : M ≤ G)
    (q : CommonTailQuotient.relativeQuotient
      (G.restrictScalars (MvPolynomial (Fin n) P))
      (M.restrictScalars (MvPolynomial (Fin n) P))) :
    ∃ g : boundedPart G k,
      q = (regularPairedQuotientEquivBounded G M C hC hCM hMG).symm
        (Submodule.Quotient.mk g) := by
  let e := regularPairedQuotientEquivBounded G M C hC hCM hMG
  obtain ⟨g, hg⟩ := Submodule.Quotient.mk_surjective _ (e q)
  refine ⟨g, ?_⟩
  change q = e.symm (Submodule.Quotient.mk g)
  apply e.injective
  simpa only [e.apply_symm_apply] using hg.symm

#print axioms boundedPart_mono
#print axioms boundedPart_le_degreeLT
#print axioms boundedPart_moduleFinite
#print axioms regularPairedQuotientEquivBounded
#print axioms regularPairedQuotient_moduleFinite
#print axioms exists_regularPaired_boundedRepresentative

end


end RegularIdealDecomposition

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
