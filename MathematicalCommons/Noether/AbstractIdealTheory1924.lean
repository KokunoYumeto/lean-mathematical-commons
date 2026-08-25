/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/
import MathematicalCommons.Noether.DedekindTheory1927

/-!
# Noether 1924: abstract characterization of ideal theory

Controlled source: Emmy Noether, *Abstrakter Aufbau der Idealtheorie im
algebraischen Zahlkörper*, witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
line 14214.

The source characterizes domains with Dedekind ideal theory by a divisor-chain
condition, an Artinian quotient condition for every nonzero ideal, and integral
closure in the fraction field. Under the explicit modern Noetherian-domain
assumptions, this file packages that characterization through Mathlib's
`IsDedekindDomain` and the local quotient-Artinian/dimension-one bridge.
-/

namespace MathematicalCommons.Noether.AbstractIdealTheory1924

open MathematicalCommons.Noether.DedekindTheory1927

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]

/-- Noether's 1924 chain-condition characterization of rings carrying
Dedekind ideal theory, in modern typeclass form. -/
theorem isDedekindDomain_iff_integrallyClosed_and_artinianQuotients :
    IsDedekindDomain R ↔
      IsIntegrallyClosed R ∧
        ∀ I : Ideal R, I ≠ ⊥ → IsArtinianRing (R ⧸ I) := by
  constructor
  · intro h
    letI : IsDedekindDomain R := h
    exact ⟨inferInstance, isArtinianRing_quotient_of_dimensionLEOne⟩
  · rintro ⟨hclosed, hquot⟩
    letI : IsIntegrallyClosed R := hclosed
    letI : Ring.DimensionLEOne R :=
      dimensionLEOne_of_artinian_nonzero_quotients hquot
    exact (isDedekindDomain_iff R (FractionRing R)).2
      ⟨inferInstance, inferInstance, inferInstance,
        (isIntegrallyClosed_iff (FractionRing R)).mp inferInstance⟩

#print axioms isDedekindDomain_iff_integrallyClosed_and_artinianQuotients

end MathematicalCommons.Noether.AbstractIdealTheory1924
