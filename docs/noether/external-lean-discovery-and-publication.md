# External Lean discovery and an Emmy Noether public front door

Checked 2026-08-29. This note excludes repositories owned by
`KokunoYumeto`, the retained 9,834-byte Zenodo seed archive, ordinary Mathlib
forks, and projects that merely use “Noether” as a product name. The four files
discussed below are separate, actual Internet-hosted Lean sources whose full
contents were read and commit-pinned; they are not the four Lean entries in the
Zenodo seed.

## Publication state and DOI lineage

The canonical public repository is
[`KokunoYumeto/lean-mathematical-commons`](https://github.com/KokunoYumeto/lean-mathematical-commons).
The public GitHub API reports it as public, unarchived, and Apache-2.0.

The original small deposit,
[Zenodo record 21129946](https://doi.org/10.5281/zenodo.21129946), and the
current [Noether pilot 0.2.6 record](https://doi.org/10.5281/zenodo.22162481)
both belong to concept DOI
[`10.5281/zenodo.21129945`](https://doi.org/10.5281/zenodo.21129945).
So the answer to “was the old sidecar DOI co-opted?” is **yes**: its concept
lineage was continued and turned into the living, substantially larger Lean of
the Mathematical Commons series. The first 9,834-byte record is retained as
the seed version; it is not treated as the current mathematical achievement.

## Repository recommendation

A separate author-facing GitHub is worthwhile because “Emmy Noether in Lean”
is immediately legible and searchable while “Lean of the Mathematical
Commons” is an umbrella brand. The safe architecture is:

1. keep `lean-mathematical-commons` as the canonical development repository;
2. create a public `KokunoYumeto/emmy-noether-in-lean` author front door;
3. generate its Lean subtree, theorem map, coverage dashboard, source map,
   build receipts, and release links from the canonical repository;
4. prohibit independent edits or divergent theorem histories in the mirror;
5. point both repositories to the existing concept DOI rather than minting a
   second DOI for identical bytes.

A new concept DOI becomes sensible only if the author repository becomes an
independently curated scholarly artifact with a genuinely different release
unit. Duplicating the same releases under two DOI lineages would fragment
citations and provenance.

The author-facing title should be explicit: **Emmy Noether in Lean 4 —
source-linked formalizations, Mathlib coverage, and reproducible proofs**.
Repository topics should include `emmy-noether`, `lean4`, `mathlib`,
`formalization`, `history-of-mathematics`, `commutative-algebra`,
`invariant-theory`, and `noethers-theorem`.

## Third-party discovery result

Exact GitHub code searches for “Emmy Noether” and the work titles
*Idealtheorie in Ringbereichen*, *Invariante Variationsprobleme*, and *Zur
Theorie der Polynomideale und Resultanten* found no third-party source-linked
Lean corpus. The four credible theorem-level files were then content-read, not
merely indexed. Their commits, byte counts, SHA-256 digests, declarations,
licenses, and P40 crosswalk are pinned in the
[four-file audit receipt](../../artifacts/coordination/noether-external-four-file-audit-20260829.json).

| Exact file | Content read and classification | Absorption result |
|---|---|---|
| [TauCeti general Skolem–Noether](https://github.com/TauCetiProject/TauCeti/blob/ddb7e2a955836d345df91708d0cfc14a6f5c4698/TauCeti/Algebra/CentralSimple/SkolemNoether.lean), 11,368 bytes, SHA-256 `967AC2D7C4995DD866ED3AFB967468AF01880D5F3DD8AEE6A560A44A8DE40655` | Apache-2.0 central-source theorem with three public declarations. It is directly relevant but narrower than Noether's printed statement, which permits noncentral simple subrings containing the center. | Inspected as the general proof-architecture and dependency model. Its six-module TauCeti tensor-product/bimodule/simple-Artinian dependency cluster was not copied. The full P40 simple-subring theorem remains open. |
| [TauCeti quaternion/complex case](https://github.com/TauCetiProject/TauCeti/blob/ddb7e2a955836d345df91708d0cfc14a6f5c4698/TauCeti/Algebra/Quaternion/ComplexSubfield.lean), 12,695 bytes, SHA-256 `11062D84C4B0C2F2DE95BA5A8312B6B1C061F7A332E4FB04DD1A0BAC3A21B604` | Apache-2.0 concrete noncentral-source instance: any two real-algebra embeddings `ℂ → ℍ[ℝ]` are conjugate. | Adapted with attribution into the source-linked P40 module and built green. The ledger classifies the promoted target as an externally attributed `FORMALIZED_GAP`, not locally original mathematics. |
| [QICLean matrix Skolem–Noether](https://github.com/LionSR/QICLean/blob/6bb40f17a0bed7cc62a6d5cf1ff13aaecbbdae8b/QICLean/Algebra/SkolemNoether.lean), 8,562 bytes, SHA-256 `17EAE7BC696567E5A9B7F3C2595F051F66CEE41809C7647B65705D41637AFA6C` | Apache-2.0 full-matrix automorphism case, wrapping Mathlib's endomorphism-algebra conjugacy theorem. | Adapted, generalized from complex coefficients to an arbitrary field, source-linked to P40, and built green. It is `MATHLIB_MODERN_FORM` plus local `NEW_PACKAGING`. |
| [Blackfeather Jacobson–Noether](https://github.com/Blackfeather007/Jacobson_Noether_Thm/blob/19aadd04dbf52f851073dda0aeaf04f97f326b8f/JacobsonNoetherThm/JacobsonNoether.lean), 12,243 bytes, SHA-256 `B4BEF29D239941AC194D93DF71A43D9BFFD962FAC20A1AB853C2EEA17A2AA5BD` | Unlicensed standalone incubator for the Jacobson–Noether theorem, adjacent to but not the P40 inner-automorphism statement. | Already generalized, reviewed, and absorbed upstream by Mathlib PR 16525 as `JacobsonNoether.exists_separable_and_not_isCentral`; classified `MATHLIB_EXACT`. No unlicensed bytes were copied. |

The two selected adaptations live in
[`NoncommutativeAlgebras1933.lean`](../../MathematicalCommons/Noether/NoncommutativeAlgebras1933.lean).
Its [bounded green receipt](../../artifacts/build/MathematicalCommons-Noether-NoncommutativeAlgebras1933-20260829T2236562973288-8ad42b68.module.receipt.json)
records the axiom-audited build under the memory cap. The local theorem is
explicitly limited to the matrix automorphism and real-quaternion embedding
cases; it does not claim the arbitrary finite-rank simple-subring theorem at
P40 lines 19477–19483.

## Focused follow-up beyond the first four files

A second bounded GitHub round searched both `Noether language:Lean` and the
exact name `"Emmy Noether" language:Lean`, then read the actual commit-pinned
contents of three additional candidates. The complete byte counts, hashes,
URLs, and decisions are in the
[follow-up audit](../../artifacts/coordination/noether-external-github-followup-20260829.json).

| Exact file | What the file really proves | Absorption result |
|---|---|---|
| [`rjwalters/lean-genius` Hilbert14OQ04](https://github.com/rjwalters/lean-genius/blob/c36558251619115ceef7be6a6446c790fda29297/proofs/Proofs/Hilbert14OQ04.lean), 4,520 bytes, SHA-256 `E9F32433EE983DCC6251A7668396AE3B60B348292A86ECF879A2F45B8E750EED` | A qualitative fixed-ring finite-generation package. No repository license was observed during the bounded audit. | No bytes copied. Its mathematical content is already subsumed by the stronger characteristic-free local `ModularInvariants1926.fixedPoints_finiteType`, so the durable action was provenance and semantic deduplication rather than duplicate code. |
| [`rjwalters/lean-genius` AbelRuffiniGaloisExtensionsOQ11](https://github.com/rjwalters/lean-genius/blob/494c45c4a1000ba00e15ae515d87916628c9d3a2/proofs/Proofs/AbelRuffiniGaloisExtensionsOQ11.lean), 6,932 bytes, SHA-256 `3ACBE0B58F153BB753355C2F55FE04C61E51684FEEBF8B4F3E5F6C64D6EAA3B4` | Full-symmetric-group invariant-ring presentation and elementary-symmetric algebraic independence. Its prose reaches toward a fixed-field statement that its Lean declarations do not establish. No repository license was observed during the bounded audit. | The API/mathematical lead was absorbed into the new independently written [P11 module](../../MathematicalCommons/Noether/EquationsWithPrescribedGroup1918.lean); zero external source bytes were copied. The local module adds a fraction-ring equivalence, builds green, and explicitly keeps the stronger fixed-field equality open. |
| [`szl-holdings/lutar-lean` NoetherAudit](https://github.com/szl-holdings/lutar-lean/blob/d29904e1335ec6bddd6e5fca144becd1155c5123/Lutar/Innovations/round6/NoetherAudit.lean), 2,153 bytes, SHA-256 `7A5A5B6EA3BEC4BFFBDE84B6E8DD438F4259C864C5F3C0742B2C49FE7ABBFC9B` | An Apache-2.0 finite-sum permutation relabelling whose doctrine hypothesis is unused. It is not Noether's variational theorem or a theorem from the controlled paper corpus. | Rejected, with the exact reason pinned. Relabelling it as a historical Noether formalization would reduce rather than improve corpus accuracy. |

The P11 result is not merely an index entry: three declarations are compiled
in Lean 4.31 and both umbrellas are green. Its
[claim receipt](../../artifacts/build/claim-P11-prescribed-group-20260829T2315159464772-244c1dd8.json)
separates the completed symmetric-group support from six genuinely open source
targets. This is the licensing-safe meaning of “absorb” for the unlicensed
candidate: retain its exact provenance and useful API lead, independently
write and verify the applicable mathematics, and do not copy its bytes.

Further discovery hits without absorbable Noether theorem content were
dependency references:

| Project | What exists | Decision |
|---|---|---|
| [Physlib](https://github.com/leanprover-community/physlib) | Active Apache-2.0 variational-calculus, Euler–Lagrange, Lagrangian, and Hamiltonian infrastructure, but no Noether theorem found. | High-value dependency/API reference for the future variational lane; not stale code to absorb. |
| [ATOMSLab/LeanChemicalTheories](https://github.com/ATOMSLab/LeanChemicalTheories) | Lean 3.51.1 mechanics foundations; the associated paper names Noether’s theorem only as a future goal. No repository license was found. | Index as prior infrastructure; no theorem to absorb and no unlicensed copying. |

Rejected apparent hits included product-name collisions, generic uses of
“Noetherian,” and a repository whose purported `NoetherTheorem` was only a
string in a registry marked `proven := true` while mathematical obligations
were filled with `True`. Those provide no reusable proof.

The discovery conclusion is therefore strong: a dedicated Emmy Noether GitHub
would occupy an otherwise empty source-linked niche rather than duplicate an
existing paper corpus. Relevant theorem-level work does exist and has now been
absorbed where licensing, dependencies, and source fit permit; the project does
not present those attributed adaptations as local-original work.

## Highest-value formalization program

The ranking below combines historical importance, present Lean deficit, and
the chance of producing reusable infrastructure.

1. **Noether’s first and second variational theorems.** This is the most
   recognizable flagship. Only 4 of 34 inventoried variational targets are
   currently available locally or in Mathlib, and only one is newly completed
   local content. A source-faithful theorem connecting infinitesimal symmetry,
   Euler–Lagrange expressions, conservation laws, and the second-theorem
   identities would be the single most important achievement, but it requires
   major variational-calculus infrastructure.
2. **The P22 determinant/norm/resultant bridge.** This is the best near-term
   hard result. The current library covers 44 of 61 inventoried units, but the
   historical `E^(i)`/`R^(i)` families, module norm, maximal-minor gcd,
   resultant identity, later stages, and choice independence remain open.
3. **Noether’s later noncommutative algebra and representation theory.** Only
   three of eight works in this domain have partial theorem audits. Skolem–Noether,
   crossed products, normal bases, Brauer-theoretic structures, and orders need
   a source-by-source map before the genuine gaps can be selected.
4. **The Gordan–Noether invariant-theory chain.** Constructive finite bases,
   Noether bounds, and modular invariant theory are both historically central
   and comparatively underrepresented in reusable Lean infrastructure.
5. **Arithmetic, field theory, and ramification.** Existing Mathlib coverage is
   relatively strong inside the small audited slice, so the first task is
   auditing the nine unaudited works rather than writing wrappers.

Across the other on-disk authors, the recommended next order is **Paul Gordan**
for constructive invariant theory, **J. J. Sylvester** for matrices,
resultants, and invariant theory that can reuse P22 infrastructure, **Hellmuth
Kneser** as a high-risk quadratic-form/topology lane after a proper audit, and
**Ernst Steinitz** for a source-linked field-theory map where much of the modern
mathematics already exists in Mathlib. The tiny Weber and Jordan sidecars are
not enough evidence to rank their full corpora.
