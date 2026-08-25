/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.RingTheory.Localization.Ideal

/-!
# Noether 1923: localization core of ground ideals

Controlled source: Emmy Noether, *Eliminationstheorie und allgemeine
Idealtheorie*, witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
ground-ideal definition at lines 13701–13705 and Hilfssatz VI at line 13943.

Noether's ground ideal is modeled here by extension to a localization followed
by contraction. The theorem proves the binary intersection core of Hilfssatz
VI in a general commutative localization. It does not construct her successive
elementary-divisor forms or elimination norm, and it does not supply primary
decomposition.
-/

namespace MathematicalCommons.Noether.EliminationIdealTheory1923

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Extension to a localization followed by contraction. This is the modern
localization model of Noether's ground-ideal operation. -/
def groundIdeal (I : Ideal R) : Ideal R :=
  (I.map (algebraMap R S)).comap (algebraMap R S)

/-- Ground-ideal formation commutes with binary intersections. This is the
localization lattice core of Noether's Hilfssatz VI. -/
theorem groundIdeal_inf (M : Submonoid R) [IsLocalization M S]
    (I J : Ideal R) :
    groundIdeal (S := S) (I ⊓ J) =
      groundIdeal (S := S) I ⊓ groundIdeal (S := S) J := by
  unfold groundIdeal
  rw [IsLocalization.map_inf M S, Ideal.comap_inf]

#print axioms groundIdeal_inf

end MathematicalCommons.Noether.EliminationIdealTheory1923
