/-
Copyright (c) 2026 Lean of the Mathematical Commons contributors.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Prod

/-!
# Noether–Schmeidler, noncommutative modules (1920): Satz I support

Controlled source: Emmy Noether and Werner Schmeidler, *Moduln in
nichtkommutativen Bereichen, insbesondere aus Differential- und
Differenzenausdrücken*, witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
Satz I at line 10329 and definitions at lines 10238–10327.

The source's “right-sided modules” are additive subsets closed under left
multiplication by the operator ring, hence `Submodule R M` in Mathlib's left
module convention. This declaration captures the forward algebraic heart of
Satz I for arbitrary modules over a possibly noncommutative ring. It does not
claim the source's full iff, its custom subgroup dictionary, or its factor
identifications.
-/

namespace MathematicalCommons.NoetherSchmeidler.NoncommutativeModules1920

/-- If two submodules span the whole module, quotienting by their intersection
is linearly equivalent to the product of the two quotients.

This is the noncommutative-module Chinese-remainder map underlying the forward
direction of Noether–Schmeidler's Satz I. -/
noncomputable def quotientInfEquivProdOfSupEqTop
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (I J : Submodule R M) (h : I ⊔ J = ⊤) :
    (M ⧸ (I ⊓ J)) ≃ₗ[R] (M ⧸ I) × (M ⧸ J) := by
  let f : M →ₗ[R] (M ⧸ I) × (M ⧸ J) := I.mkQ.prod J.mkQ
  have hker : LinearMap.ker f = I ⊓ J := by
    dsimp [f]
    rw [LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]
  have hkernels : LinearMap.ker I.mkQ ⊔ LinearMap.ker J.mkQ = ⊤ := by
    simpa using h
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    calc
      LinearMap.range f =
          (LinearMap.range I.mkQ).prod (LinearMap.range J.mkQ) := by
        dsimp [f]
        exact LinearMap.range_prod_eq hkernels
      _ = ⊤ := by simp
  exact
    (Submodule.quotEquivOfEq (I ⊓ J) (LinearMap.ker f) hker.symm).trans
      (f.quotKerEquivOfSurjective hsurj)

#print axioms quotientInfEquivProdOfSupEqTop

end MathematicalCommons.NoetherSchmeidler.NoncommutativeModules1920
