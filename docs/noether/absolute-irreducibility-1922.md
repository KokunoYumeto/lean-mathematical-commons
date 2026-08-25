# Noether 1922 absolute-irreducibility formalization map

Work: Emmy Noether, *Ein algebraisches Kriterium für absolute
Irreduzibilität* (1922), controlled witness `NOETH-DE-ED-0014`, SHA-256
`EE226847656BC4D65EDDA9E9BF9BB1D25797C0C6D672D267D94A97FD88C7AD58`,
packet lines 12398–12608.

## Source result inventory

- Absolute irreducibility is defined at line 12405 as irreducibility after
  extension to an algebraic closure.
- The main theorem, lines 12407–12409 and 12581–12585, constructs a universal
  integer-coefficient polynomial `R(Γ,u)` whose nonvanishing as a polynomial in
  the auxiliary variables characterizes absolute irreducibility for fixed
  degree and at least two variables.
- The generic universal-coefficient polynomial is asserted absolutely
  irreducible at line 12417 and stated precisely at lines 12439–12444.
- For prescribed positive factor degrees, lines 12541–12573 give a necessary
  and sufficient coefficient condition; lines 12575–12579 identify exactly the
  coefficient systems parameterized by such products.
- The Ostrowski corollary, lines 12411–12413 and 12587–12600, says an absolutely
  irreducible polynomial over algebraic numbers stays absolutely irreducible
  modulo all but finitely many prime ideals of a containing number field.
- The arithmetic tail at lines 12594–12598 uses that a nonzero ideal has only
  finitely many prime-ideal divisors.

## Pinned Mathlib map

Mathlib supplies `Irreducible`, `MvPolynomial.map`, algebraic closures and their
uniqueness, geometrically irreducible/integral schemes, prime kernels,
Noetherian finite-variable polynomial rings, norms, symmetric-polynomial/Vieta
infrastructure, Dedekind-domain ideals, residue fields, and
`UniqueFactorizationMonoid.fintypeSubtypeDvd`.

It does not supply a canonical absolute-irreducibility predicate for
polynomials, the universal coefficient reducibility form, the all-degree
generic-polynomial theorem, the prescribed-bidegree coefficient criterion, or
the all-but-finitely-many-primes specialization theorem. These headline
results are recorded as `GAP_CANDIDATE`, not inferred from nearby scheme or
factorization APIs.

The promoted `finite_primeIdeal_divisors` helper is only `NEW_PACKAGING` of the
existing finite-divisor theorem and the Dedekind ideal UFM instance. It is an
honest proof component of the last arithmetic step, not the Ostrowski theorem.

## Essential caveats

- `R(Γ,u) ≠ 0` means nonzero as a polynomial in `u`, not merely nonzero at one
  field point; this distinction matters over finite fields.
- The homogeneous formulation assumes a nonzero coefficient system.
- The affine formulation must exclude a drop in total degree.
- Rational/algebraic-number coefficients require clearing denominators and
  excluding primes dividing them.
- Geometric irreducibility alone is not the same as absolute polynomial
  irreducibility when reducedness is not recorded; geometrically integral is
  the closer hypersurface analogue.

## Development order

1. Define polynomial absolute irreducibility invariantly under the chosen
   algebraic closure and prove independence of that choice.
2. Formalize universal coefficient spaces and the coefficient-convolution map
   for prescribed factor degrees.
3. Prove the relation ideal prime, finitely generated, and exact for the image.
4. Combine all factor-degree strata into Noether's reducibility form.
5. Prove the fixed-degree criterion and generic-polynomial lemma.
6. Develop specialization outside the finitely many coefficient/denominator
   prime divisors to obtain the Ostrowski corollary.
