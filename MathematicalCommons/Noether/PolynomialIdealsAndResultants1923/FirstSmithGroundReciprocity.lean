import MathematicalCommons.Noether.PolynomialIdealsAndResultants1923.FirstSmithScalarQuotients

/-!
# Hentzelt--Noether Satz II: ground-module / highest-divisor reciprocity

Module for P22, controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
Satz II and equation (5), lines 12815--12844.

The source uses two different quotient operations.  The already formalized
scalar colon `M.colon (G : Set E)` is the ideal of scalars taking `G` into
`M`.  In the reciprocal expression `M / (e)`, however, the result is a
module: it consists of vectors `x` for which every scalar in the principal
ideal `(e)` sends `x` into `M`.  `moduleQuotientByIdeal` types this second
operation directly.

For a diagonal Smith pair, if every selected coefficient divides a
distinguished coefficient `e_i`, then quotienting the denominator module by
`(e_i)` recovers the whole numerator carrier.  For the actual localized
cutoff-one pair, the preceding ground-module theorem says that the numerator
is exactly the nonzero-scalar saturation of the original module.  This turns
the carrier result into the source-shaped ambient equality

`G_1* = M_1* / (e_i)`.

Mathlib v4.31 does not order the coefficients returned by its Smith API.
Accordingly, the greatest-coefficient divisibility condition is an explicit
hypothesis here; no canonical ordering, normalization, or choice independence
is asserted.
-/

namespace MathematicalCommons.Noether.PolynomialIdealsAndResultants1923

open Module MvPolynomial

namespace SmithGroundReciprocity

noncomputable section

variable {R E : Type*} [CommRing R]
variable [AddCommGroup E] [Module R E]

/-- Definition II's module-valued quotient `M / J`: the vectors whose scalar
multiples by every member of `J` lie in `M`.  This is distinct from
`Submodule.colon`, which is ideal-valued. -/
def moduleQuotientByIdeal (M : Submodule R E) (J : Ideal R) : Submodule R E :=
  ⨅ r : J, M.comap (LinearMap.lsmul R E r.1)

@[simp]
theorem mem_moduleQuotientByIdeal
    (M : Submodule R E) (J : Ideal R) (x : E) :
    x ∈ moduleQuotientByIdeal M J ↔
      ∀ r : R, r ∈ J → r • x ∈ M := by
  simp [moduleQuotientByIdeal]

/-- For a principal ideal, Definition II's module quotient is just the
preimage of `M` under multiplication by its generator. -/
theorem moduleQuotientByIdeal_span_singleton
    (M : Submodule R E) (e : R) :
    moduleQuotientByIdeal M (Ideal.span ({e} : Set R)) =
      M.comap (LinearMap.lsmul R E e) := by
  ext x
  rw [mem_moduleQuotientByIdeal]
  change (∀ r : R, r ∈ Ideal.span ({e} : Set R) → r • x ∈ M) ↔
    e • x ∈ M
  constructor
  · intro hx
    exact hx e (Ideal.subset_span (by simp))
  · intro hx r hr
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hr
    rw [hc]
    simpa [smul_smul, mul_comm] using M.smul_mem c hx

/-- If `G` is exactly the nonzero-scalar saturation of `M`, a nonzero scalar
whose action sends all of `G` into `M` recovers `G` as `M / (e)`. -/
theorem moduleQuotientByPrincipalIdeal_eq_of_saturation
    [NoZeroDivisors R] [Nontrivial R]
    (M G : Submodule R E) (e : R) (he : e ≠ 0)
    (hG : G = RegularIdealDecomposition.nonzeroScalarSaturation M)
    (hsmul : ∀ x ∈ G, e • x ∈ M) :
    moduleQuotientByIdeal M (Ideal.span ({e} : Set R)) = G := by
  rw [moduleQuotientByIdeal_span_singleton]
  apply le_antisymm
  · intro x hx
    change e • x ∈ M at hx
    rw [hG]
    exact ⟨e, he, hx⟩
  · intro x hx
    change e • x ∈ M
    exact hsmul x hx

variable {ι : Type*}

/-- The second half of equation (5) for a finite diagonal Smith pair.  The
distinguished coefficient must be divisible by every selected coefficient;
this ordering is not supplied by Mathlib's Smith choice. -/
theorem moduleQuotientByIdeal_span_singleton_eq_top_of_isGreatest
    (N : Submodule R E) (b : Basis ι R E) (e : ι → R)
    (hN : ∀ x, x ∈ N ↔ ∀ j, e j ∣ b.repr x j)
    (i : ι) (h : SmithScalarQuotients.IsGreatestRemainingDivisor e ∅ i) :
    moduleQuotientByIdeal N (Ideal.span ({e i} : Set R)) = ⊤ := by
  rw [moduleQuotientByIdeal_span_singleton]
  apply top_unique
  intro x _
  change e i • x ∈ N
  apply (hN (e i • x)).mpr
  intro j
  obtain ⟨c, hc⟩ := h.2 j (by simp)
  refine ⟨c * b.repr x j, ?_⟩
  rw [map_smul]
  simp only [Finsupp.smul_apply, smul_eq_mul, hc]
  ac_rfl

/-- Abstract finite form of both reciprocal identities in Satz II:
`N / E = (e_i)` and `N / (e_i) = E`, with the two quotient operations typed
separately. -/
theorem diagonalGroundReciprocity
    [Fintype ι]
    (N : Submodule R E) (b : Basis ι R E) (e : ι → R)
    (hN : ∀ x, x ∈ N ↔ ∀ j, e j ∣ b.repr x j)
    (i : ι) (h : SmithScalarQuotients.IsGreatestRemainingDivisor e ∅ i) :
    N.colon ((⊤ : Submodule R E) : Set E) =
        Ideal.span ({e i} : Set R) ∧
      moduleQuotientByIdeal N (Ideal.span ({e i} : Set R)) = ⊤ := by
  constructor
  · have hfirst := SmithScalarQuotients.filtration_colon_top_eq_span_of_isGreatest
      N b e hN ∅ i h
    rw [SmithScalarQuotients.filtration_empty] at hfirst
    exact hfirst
  · exact moduleQuotientByIdeal_span_singleton_eq_top_of_isGreatest
      N b e hN i h

#print axioms moduleQuotientByIdeal
#print axioms mem_moduleQuotientByIdeal
#print axioms moduleQuotientByIdeal_span_singleton
#print axioms moduleQuotientByPrincipalIdeal_eq_of_saturation
#print axioms moduleQuotientByIdeal_span_singleton_eq_top_of_isGreatest
#print axioms diagonalGroundReciprocity

end

end SmithGroundReciprocity

namespace RegularIdealDecomposition

noncomputable section

variable {P : Type*} [Field P]
variable {n : ℕ}

/-- The reciprocal half of Satz II for the actual localized cutoff-one pair:
the localized ground module is the original module divided by the principal
ideal of a distinguished greatest Smith coefficient. -/
theorem localizedSecondVariableGroundModule_eq_moduleQuotientBySmithCoefficient
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (i : localizedSecondVariableSmithIndex I k)
    (h : localizedSecondVariableIsGreatestRemainingDivisor I k ∅ i) :
    localizedSecondVariableGroundModule I k =
      SmithGroundReciprocity.moduleQuotientByIdeal
        (localizedSecondVariableOriginalModule I k)
        (Ideal.span
          ({localizedSecondVariableSmithCoefficients I k i} :
            Set (secondVariablePID P n))) := by
  rw [SmithGroundReciprocity.moduleQuotientByIdeal_span_singleton]
  apply le_antisymm
  · intro x hx
    change localizedSecondVariableSmithCoefficients I k i • x ∈
      localizedSecondVariableOriginalModule I k
    let xG : localizedSecondVariableGroundCarrier I k := ⟨x, hx⟩
    have hxmul :
        localizedSecondVariableSmithCoefficients I k i • xG ∈
          localizedSecondVariableDenominatorCarrier I k := by
      apply (localizedSecondVariable_mem_denominatorCarrier_iff_dvd I k _).mpr
      intro j
      obtain ⟨c, hc⟩ := h.2 j (by simp)
      refine ⟨c * (localizedSecondVariableEtaBasis I k).repr xG j, ?_⟩
      rw [map_smul]
      simp only [Finsupp.smul_apply, smul_eq_mul, hc]
      ac_rfl
    exact hxmul
  · intro x hx
    change localizedSecondVariableSmithCoefficients I k i • x ∈
      localizedSecondVariableOriginalModule I k at hx
    rw [localizedSecondVariableGroundModule_eq_saturation I k]
    exact ⟨localizedSecondVariableSmithCoefficients I k i,
      localizedSecondVariableSmithCoefficients_ne_zero I k i, hx⟩

/-- Both reciprocal identities of Satz II for the actual localized first
Smith pair.  The first component is the scalar-colon ideal; the second is the
module quotient by the displayed principal ideal. -/
theorem localizedSecondVariableSatzII_reciprocity
    (I : Ideal (MvPolynomial (Fin (n + 2)) P)) (k : ℕ)
    (i : localizedSecondVariableSmithIndex I k)
    (h : localizedSecondVariableIsGreatestRemainingDivisor I k ∅ i) :
    (localizedSecondVariableDenominatorCarrier I k).colon
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
              Set (secondVariablePID P n))) := by
  constructor
  · have hfirst :=
      localizedSecondVariableSmithFiltration_colon_ground_eq_span_of_greatest
        I k ∅ i h
    rw [localizedSecondVariableSmithFiltration_empty] at hfirst
    exact hfirst
  · exact localizedSecondVariableGroundModule_eq_moduleQuotientBySmithCoefficient
      I k i h

#print axioms localizedSecondVariableGroundModule_eq_moduleQuotientBySmithCoefficient
#print axioms localizedSecondVariableSatzII_reciprocity

end

end RegularIdealDecomposition

end MathematicalCommons.Noether.PolynomialIdealsAndResultants1923
