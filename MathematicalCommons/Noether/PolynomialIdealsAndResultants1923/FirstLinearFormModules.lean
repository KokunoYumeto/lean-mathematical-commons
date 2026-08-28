import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.FirstGroundPairedQuotient

/-!
# Hentzelt--Noether equations (22)--(23): the first linear-form modules

Module for P22, controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
lines 13141--13160.  The source replaces the bounded first-variable
coefficients by finitely many independent variables `ξ` and the multiples of
the regular polynomial by an independent tail `ζ`.  Equation (23) then reads
`G₁ = (G₁*, C₁)` and `M₁ = (M₁*, C₁)`.

Here the `ξ` and `ζ` coordinates are modeled by the product of the
degree-`< k` remainder module and the regular principal tail.  The regular
division complement realizes this product as the original polynomial module
by `(r, t) ↦ r + t`.  The bounded, tail, and full linear-form modules map to
Noether's bounded part, principal tail, and containing ideal respectively.
Under supplied regularity and membership hypotheses, the common-tail quotient
equivalence is instantiated through the actual cutoff-one ground/original ideal
quotient chain.

The last claim on line 13162--that `G₁*` is the ground module of `M₁*`--is not
proved here.  It requires a separate transport of the source's admissible
nonzero multipliers to saturation of the bounded coordinate module.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open MvPolynomial
open RegularitySpecialization

namespace RegularIdealDecomposition

noncomputable section

variable {P : Type*} [Field P]
variable {n k : ℕ}

/-- Coordinate space of the first historical linear-form module: the finite
`ξ` coordinates followed by the independent `ζ` tail. -/
abbrev firstLinearFormSpace
    (C : MvPolynomial (Fin (n + 1)) P) (k : ℕ) :=
  Polynomial.degreeLT (MvPolynomial (Fin n) P) k × principalTail C

/-- Realize the independent `ξ` and `ζ` coordinates as a polynomial by
addition.  Regularity makes this a linear equivalence. -/
noncomputable def firstLinearFormRealization
    (C : MvPolynomial (Fin (n + 1)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 1)) k C) :
    firstLinearFormSpace C k ≃ₗ[MvPolynomial (Fin n) P]
      Polynomial (MvPolynomial (Fin n) P) :=
  Submodule.prodEquivOfIsCompl
    (Polynomial.degreeLT (MvPolynomial (Fin n) P) k)
    (principalTail C) (principalTail_isCompl_degreeLT C hC).symm

/-- The finite `ξ`-linear-form module attached to a containing ideal. -/
def firstBoundedLinearFormModule
    (I : Ideal (Polynomial (MvPolynomial (Fin n) P)))
    (C : MvPolynomial (Fin (n + 1)) P) (k : ℕ) :
    Submodule (MvPolynomial (Fin n) P) (firstLinearFormSpace C k) :=
  (boundedPartInDegreeLT I k).prod ⊥

/-- The common independent `ζ` tail. -/
def firstTailLinearFormModule
    (C : MvPolynomial (Fin (n + 1)) P) (k : ℕ) :
    Submodule (MvPolynomial (Fin n) P) (firstLinearFormSpace C k) :=
  (⊥ : Submodule (MvPolynomial (Fin n) P)
      (Polynomial.degreeLT (MvPolynomial (Fin n) P) k)).prod ⊤

/-- The full coordinate linear-form module: the finite `ξ` module plus the
independent `ζ` tail, exactly as in equation (23). -/
def firstLinearFormModule
    (I : Ideal (Polynomial (MvPolynomial (Fin n) P)))
    (C : MvPolynomial (Fin (n + 1)) P) (k : ℕ) :
    Submodule (MvPolynomial (Fin n) P) (firstLinearFormSpace C k) :=
  firstBoundedLinearFormModule I C k ⊔ firstTailLinearFormModule C k

/-- Realization sends the finite coordinate module exactly onto the bounded
part of the ideal. -/
theorem map_firstBoundedLinearFormModule
    (I : Ideal (Polynomial (MvPolynomial (Fin n) P)))
    (C : MvPolynomial (Fin (n + 1)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 1)) k C) :
    (firstBoundedLinearFormModule I C k).map
        (firstLinearFormRealization C hC :
          firstLinearFormSpace C k →ₗ[MvPolynomial (Fin n) P]
            Polynomial (MvPolynomial (Fin n) P)) =
      boundedPart I k := by
  apply le_antisymm
  · rintro f ⟨x, hx, rfl⟩
    rcases x with ⟨r, t⟩
    have hr : r ∈ boundedPartInDegreeLT I k := hx.1
    have ht : t = 0 := by simpa using hx.2
    subst t
    have hrI : (r : Polynomial (MvPolynomial (Fin n) P)) ∈ I :=
      (mem_boundedPartInDegreeLT_iff I r).1 hr
    simpa [firstLinearFormRealization, boundedPart] using
      (show (r : Polynomial (MvPolynomial (Fin n) P)) ∈
          I.restrictScalars (MvPolynomial (Fin n) P) ∧
        (r : Polynomial (MvPolynomial (Fin n) P)) ∈
          Polynomial.degreeLT (MvPolynomial (Fin n) P) k from
        ⟨hrI, r.property⟩)
  · intro f hf
    let r : Polynomial.degreeLT (MvPolynomial (Fin n) P) k :=
      ⟨f, hf.2⟩
    refine ⟨(r, 0), ?_, ?_⟩
    · refine ⟨(mem_boundedPartInDegreeLT_iff I r).2 ?_, by simp⟩
      exact hf.1
    · simp [firstLinearFormRealization, r]

/-- Realization sends the independent coordinate tail exactly onto the
regular principal tail. -/
theorem map_firstTailLinearFormModule
    (C : MvPolynomial (Fin (n + 1)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 1)) k C) :
    (firstTailLinearFormModule C k).map
        (firstLinearFormRealization C hC :
          firstLinearFormSpace C k →ₗ[MvPolynomial (Fin n) P]
            Polynomial (MvPolynomial (Fin n) P)) =
      principalTail C := by
  apply le_antisymm
  · rintro f ⟨x, hx, rfl⟩
    rcases x with ⟨r, t⟩
    have hr : r = 0 := by simpa using hx.1
    subst r
    simp [firstLinearFormRealization]
  · intro f hf
    let t : principalTail C := ⟨f, hf⟩
    refine ⟨(0, t), ?_, ?_⟩
    · exact ⟨by simp, by simp⟩
    · simp [firstLinearFormRealization, t]

/-- Realization sends the full coordinate module exactly onto the containing
ideal viewed over the remaining-variable coefficient ring. -/
theorem map_firstLinearFormModule
    (I : Ideal (Polynomial (MvPolynomial (Fin n) P)))
    (C : MvPolynomial (Fin (n + 1)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 1)) k C)
    (hCI : MvPolynomial.finSuccEquiv P n C ∈ I) :
    (firstLinearFormModule I C k).map
        (firstLinearFormRealization C hC :
          firstLinearFormSpace C k →ₗ[MvPolynomial (Fin n) P]
            Polynomial (MvPolynomial (Fin n) P)) =
      I.restrictScalars (MvPolynomial (Fin n) P) := by
  rw [firstLinearFormModule, Submodule.map_sup,
    map_firstBoundedLinearFormModule, map_firstTailLinearFormModule]
  exact (regularIdeal_eq_boundedPart_sup_principalTail I C hC hCI).symm

/-- Inclusion of ideals restricts to inclusion of their finite coordinate
linear-form modules. -/
theorem firstBoundedLinearFormModule_mono
    {M G : Ideal (Polynomial (MvPolynomial (Fin n) P))}
    (C : MvPolynomial (Fin (n + 1)) P) (hMG : M ≤ G) :
    firstBoundedLinearFormModule M C k ≤
      firstBoundedLinearFormModule G C k := by
  apply Submodule.prod_mono
  · intro r hr
    apply (mem_boundedPartInDegreeLT_iff G r).2
    exact hMG ((mem_boundedPartInDegreeLT_iff M r).1 hr)
  · exact le_rfl

/-- The finite `ξ` coordinates are independent of the `ζ` tail. -/
theorem firstBoundedLinearFormModule_disjoint_tail
    (I : Ideal (Polynomial (MvPolynomial (Fin n) P)))
    (C : MvPolynomial (Fin (n + 1)) P) :
    Disjoint (firstBoundedLinearFormModule I C k)
      (firstTailLinearFormModule C k) := by
  rw [disjoint_iff_inf_le, firstBoundedLinearFormModule,
    firstTailLinearFormModule, Submodule.prod_inf_prod]
  simp

/-- Coordinate form of equation (23): a containing ideal's full linear-form
module is its finite bounded module plus the common independent tail. -/
theorem firstLinearFormModule_eq_bounded_sup_tail
    (I : Ideal (Polynomial (MvPolynomial (Fin n) P)))
    (C : MvPolynomial (Fin (n + 1)) P) :
    firstLinearFormModule I C k =
      firstBoundedLinearFormModule I C k ⊔
        firstTailLinearFormModule C k := rfl

/-- A linear equivalence carrying numerator and denominator submodules onto
new submodules induces an equivalence of their relative quotients. -/
noncomputable def relativeQuotientEquivOfLinearEquiv
    {R E F : Type*} [Ring R]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    (e : E ≃ₗ[R] F)
    (G M : Submodule R E) (G' M' : Submodule R F)
    (hG : G.map (e : E →ₗ[R] F) = G')
    (hM : M.map (e : E →ₗ[R] F) = M') :
    CommonTailQuotient.relativeQuotient G M ≃ₗ[R]
      CommonTailQuotient.relativeQuotient G' M' := by
  let eG : G ≃ₗ[R] G' := e.ofSubmodules G G' hG
  apply Submodule.Quotient.equiv
    (CommonTailQuotient.relativeDenominator G M)
    (CommonTailQuotient.relativeDenominator G' M') eG
  ext y
  simp only [Submodule.mem_map_equiv]
  change (((eG.symm y : G) : E) ∈ M) ↔ ((y : G') : F) ∈ M'
  rw [← hM, Submodule.mem_map_equiv]
  rfl

/-- The common-tail quotient equivalence specialized to the explicit finite
coordinate modules and their independent tail. -/
noncomputable def firstBoundedCommonTailQuotientEquiv
    (G M : Ideal (Polynomial (MvPolynomial (Fin n) P)))
    (C : MvPolynomial (Fin (n + 1)) P) (hMG : M ≤ G) :=
  CommonTailQuotient.commonTailQuotientEquiv
    (R := MvPolynomial (Fin n) P) (E := firstLinearFormSpace C k)
    (firstBoundedLinearFormModule G C k)
    (firstBoundedLinearFormModule M C k)
    (firstTailLinearFormModule C k)
    (firstBoundedLinearFormModule_mono C hMG)
    (firstBoundedLinearFormModule_disjoint_tail G C)

/-- Equations (22)--(23) and independence of `ξ` from `ζ` identify the full
relative quotient with the quotient of the finite linear-form modules. -/
noncomputable def firstLinearFormQuotientEquivBounded
    (G M : Ideal (Polynomial (MvPolynomial (Fin n) P)))
    (C : MvPolynomial (Fin (n + 1)) P) (hMG : M ≤ G) :=
  firstBoundedCommonTailQuotientEquiv (k := k) G M C hMG

/-- The coordinate linear-form quotient realizes as the relative quotient of
the corresponding containing ideals. -/
noncomputable def firstLinearFormQuotientEquivIdeal
    (G M : Ideal (Polynomial (MvPolynomial (Fin n) P)))
    (C : MvPolynomial (Fin (n + 1)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 1)) k C)
    (hCG : MvPolynomial.finSuccEquiv P n C ∈ G)
    (hCM : MvPolynomial.finSuccEquiv P n C ∈ M) :=
  relativeQuotientEquivOfLinearEquiv
    (R := MvPolynomial (Fin n) P) (E := firstLinearFormSpace C k)
    (F := Polynomial (MvPolynomial (Fin n) P))
    (firstLinearFormRealization C hC)
    (firstLinearFormModule G C k) (firstLinearFormModule M C k)
    (G.restrictScalars (MvPolynomial (Fin n) P))
    (M.restrictScalars (MvPolynomial (Fin n) P))
    (map_firstLinearFormModule G C hC hCG)
    (map_firstLinearFormModule M C hC hCM)

/-- The cutoff-one ground linear-form module realizes exactly as the
cutoff-one ground ideal. -/
theorem map_stageOneGroundLinearFormModule
    (I : Ideal (MvPolynomial (Fin (n + 2)) P))
    (C : MvPolynomial (Fin (n + 2)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 2)) k C)
    (hCI : C ∈ I) :
    (firstLinearFormModule (stageOneGroundIdeal I) C k).map
        (firstLinearFormRealization C hC :
          firstLinearFormSpace C k →ₗ[MvPolynomial (Fin (n + 1)) P]
            Polynomial (MvPolynomial (Fin (n + 1)) P)) =
      (stageOneGroundIdeal I).restrictScalars
        (MvPolynomial (Fin (n + 1)) P) :=
  map_firstLinearFormModule (stageOneGroundIdeal I) C hC
    (finSuccIdeal_le_stageOneGroundIdeal I
      (finSuccEquiv_mem_finSuccIdeal (n := n + 1) I hCI))

/-- The original stage-one denominator linear-form module realizes exactly
as the transported original ideal. -/
theorem map_stageOneOriginalLinearFormModule
    (I : Ideal (MvPolynomial (Fin (n + 2)) P))
    (C : MvPolynomial (Fin (n + 2)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 2)) k C)
    (hCI : C ∈ I) :
    (firstLinearFormModule (finSuccIdeal (n := n + 1) I) C k).map
        (firstLinearFormRealization C hC :
          firstLinearFormSpace C k →ₗ[MvPolynomial (Fin (n + 1)) P]
            Polynomial (MvPolynomial (Fin (n + 1)) P)) =
      (finSuccIdeal (n := n + 1) I).restrictScalars
        (MvPolynomial (Fin (n + 1)) P) :=
  map_firstLinearFormModule (finSuccIdeal (n := n + 1) I) C hC
    (finSuccEquiv_mem_finSuccIdeal (n := n + 1) I hCI)

/-- Source-specific cutoff-one instance: the full ground/original
linear-form-module quotient is the quotient of their finite `ξ` parts.  The
equivalence itself only needs the ground/original inclusion; the two preceding
map theorems identify these coordinate modules with the source ideals under
the regularity and membership hypotheses. -/
noncomputable def stageOneLinearFormQuotientEquivBounded
    (I : Ideal (MvPolynomial (Fin (n + 2)) P))
    (C : MvPolynomial (Fin (n + 2)) P) :=
  firstLinearFormQuotientEquivBounded
    (k := k)
    (stageOneGroundIdeal I) (finSuccIdeal (n := n + 1) I) C
    (finSuccIdeal_le_stageOneGroundIdeal I)

/-- At cutoff one, realization identifies the source-modeled coordinate quotient
with the transported ground/original ideal quotient. -/
noncomputable def stageOneLinearFormQuotientEquivIdeal
    (I : Ideal (MvPolynomial (Fin (n + 2)) P))
    (C : MvPolynomial (Fin (n + 2)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 2)) k C)
    (hCI : C ∈ I) :=
  firstLinearFormQuotientEquivIdeal
    (stageOneGroundIdeal I) (finSuccIdeal (n := n + 1) I) C hC
    (finSuccIdeal_le_stageOneGroundIdeal I
      (finSuccEquiv_mem_finSuccIdeal (n := n + 1) I hCI))
    (finSuccEquiv_mem_finSuccIdeal (n := n + 1) I hCI)

/-- The coordinate quotient, the transported ideal quotient, and its bounded
representative quotient form one explicit equivalence chain. -/
noncomputable def stageOneLinearFormQuotientEquivIdealBounded
    (I : Ideal (MvPolynomial (Fin (n + 2)) P))
    (C : MvPolynomial (Fin (n + 2)) P)
    (hC : IsRegularInDegree (0 : Fin (n + 2)) k C)
    (hCI : C ∈ I) :=
  (stageOneLinearFormQuotientEquivIdeal I C hC hCI).trans
    (stageOneGroundIdealQuotientEquivBounded I C hC hCI)

#print axioms firstLinearFormSpace
#print axioms firstLinearFormRealization
#print axioms firstBoundedLinearFormModule
#print axioms firstTailLinearFormModule
#print axioms firstLinearFormModule
#print axioms map_firstBoundedLinearFormModule
#print axioms map_firstTailLinearFormModule
#print axioms map_firstLinearFormModule
#print axioms firstBoundedLinearFormModule_mono
#print axioms firstBoundedLinearFormModule_disjoint_tail
#print axioms firstLinearFormModule_eq_bounded_sup_tail
#print axioms relativeQuotientEquivOfLinearEquiv
#print axioms firstBoundedCommonTailQuotientEquiv
#print axioms firstLinearFormQuotientEquivBounded
#print axioms firstLinearFormQuotientEquivIdeal
#print axioms map_stageOneGroundLinearFormModule
#print axioms map_stageOneOriginalLinearFormModule
#print axioms stageOneLinearFormQuotientEquivBounded
#print axioms stageOneLinearFormQuotientEquivIdeal
#print axioms stageOneLinearFormQuotientEquivIdealBounded

end


end RegularIdealDecomposition

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
