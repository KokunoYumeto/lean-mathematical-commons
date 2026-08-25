import Mathlib.Tactic.Ring

/-!
# Noether 1919: a Plücker support identity

This file isolates the four-index determinant identity used at controlled
source lines 9573–9581 of Emmy Noether's 1919 paper on integral invariants of
binary forms.

It covers only the quadratic identity, not Satz I, straightening, generation
of the full Plücker relation ideal, or reduction modulo every prime.
-/

namespace MathematicalCommons.Noether.IntegralInvariants1919

variable {R ι : Type*} [CommRing R]

/-- The bracket `[i,k] = αᵢ βₖ - βᵢ αₖ` of two binary linear forms. -/
def bracket (α β : ι → R) (i k : ι) : R :=
  α i * β k - β i * α k

/-- The four-index quadratic Plücker relation used in Noether's straightening
argument. This is only a support identity, not the relation-ideal theorem. -/
theorem pluckerRelation (α β : ι → R) (i k r s : ι) :
    bracket α β i k * bracket α β r s -
        bracket α β i r * bracket α β k s +
      bracket α β i s * bracket α β k r = 0 := by
  unfold bracket
  ring

#print axioms pluckerRelation

end MathematicalCommons.Noether.IntegralInvariants1919
