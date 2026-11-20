# Leech symmetries: what is proved so far

The full Conway-group classification is **not proved yet**. The new files establish
the symmetry group as a finite group, construct its Golay sign changes, and
classify the symmetries that preserve the standard coordinate frame. They reuse
the existing lattice, minimum, shortest-vector count, basis and integrality
proofs. The volume proof is unchanged.

Here “symmetry” means a distance-preserving bijection of the lattice fixing the
origin. Translations are not part of this group. `mem_autGroup_iff` proves that
this definition agrees with the additive, squared-length-preserving bijections
used in the formalization. We do not restrict symmetries to integer matrices on
the ambient integer grid.

All coordinates retain the project's √8 scale: squared length 32 here is
squared length 4 in the usual normalization; 64 here is 8 there.

## Checked in Lean

| File | Result | Scope |
| --- | --- | --- |
| [LeechSymmetry.lean](../LeechSymmetry.lean) | `shortest_span` | The 196,560 shortest vectors generate the whole lattice over ℤ. |
| Same | `shortestAction_injective`, `aut_finite` | Every symmetry is determined by its action on that shell; the full symmetry group is finite. No order is computed. |
| Same | `mem_autGroup_iff` | The group includes every distance-preserving lattice bijection fixing zero. |
| Same | `centralNegation_sq`, `centralNegation_commutes`, `centralNegation_ne_one` | Negation is a nonidentity central involution. This does not classify the entire center. |
| Same | `norm64_sameModTwo_orthogonal` | Two norm-64 vectors in the same class modulo 2Λ are equal, opposite, or orthogonal. |
| Same | `standard_class_iff`, `card_standardFrame` | The norm-64 vectors congruent to `8e₀` modulo 2Λ are the 48 vectors `±8eᵢ`. Other classes have not been counted. |
| Same | `fixes_axis_preserves_frame` | Fixing `8e₀` forces a symmetry to preserve this frame. |
| [LeechMonomial.lean](../LeechMonomial.lean) | `signFlip_mem`, `card_signSubgroup` | Negating the coordinates selected by any Golay codeword preserves every lattice vector. These operations form a subgroup of order 4,096. |
| Same | `permute_mem`, `permutationAut` | Every coordinate permutation preserving the defined Golay code gives a lattice symmetry. The code-permutation group has not been classified as M₂₄. |
| [LeechFrameStabilizer.lean](../LeechFrameStabilizer.lean) | `frame_stabilizer_iff` | A symmetry preserves the standard frame iff it is a Golay sign change followed by a code-preserving coordinate permutation. |
| Same | `eq_top_of_norm64_transitive` | A **conditional** completeness criterion: a subgroup containing those sign changes and coordinate permutations is the full group if it can send `8e₀` to every norm-64 lattice vector. The transitivity hypothesis remains unproved. |

There are 52 new audited theorems, including supporting lemmas. The complete
inventory has 795 declarations. The [verification record](leech-symmetry-verification.json)
records the compiler commands, source hashes, reused dependencies and axiom audit.

The proof of the sign changes uses `LeechBasis.leech_inner_dvd_eight`: twice a
Golay codeword is a lattice vector, so its inner product with any lattice vector
is divisible by eight. The sum of the coordinates selected by that codeword is
therefore divisible by four. Negating them preserves the required sum modulo
eight. This uses the existing integrality proof for arbitrary lattice vectors.

## What remains for the full group

1. Supply explicit generators for the code-permutation group and prove that they
   generate all of it. Establish its order, 244,823,040, and the identification
   with M₂₄.
2. Construct symmetries that move between coordinate frames and check them against
   the existing lattice. Prove the required transitivity, or a sufficient finite
   orbit certificate, inside Lean. An external search can find witnesses; it
   cannot supply a trusted orbit or group-order assertion.
3. Count the relevant orbit and stabilizer to derive the order of the full group.
   The standard frame route has 8,292,375 frames and frame stabilizer
   `2¹² : M₂₄`, giving `8,315,553,613,086,720,000` symmetries. **Those frame counts,
   the M₂₄ order and the resulting Co₀ order are literature targets, not Lean
   results in this repository.** See [Wilson, sections 5.2–5.3](https://webspace.maths.qmul.ac.uk/r.a.wilson/simplegroups_files/notes5.pdf)
   for the frame argument and [ATLAS: M₂₄](https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M24/)
   for the stated M₂₄ order and standard generators.

The current code does not prove that a proposed Co₀ generating set is complete,
identify the full center, construct the quotient Co₁, or prove its simplicity.
The three-E₈ gluing theorem identifies the lattice being studied; it does not by
itself classify symmetries that move the chosen E₈ blocks.

## Reproduce the checks

Use the repository's Lean toolchain and pinned Mathlib revision:

```sh
lake build LeechFrameStabilizer CheckAxioms
lake env lean CheckAxioms.lean > axioms.txt
python3 .github/check_axioms.py CheckAxioms.lean axioms.txt
python3 scripts/check_leech_symmetry_evidence.py
```

The final command checks saved evidence against the current source; it does not
run Lean. The first three commands recompile the dependency chain and audit the
proofs. The expected audit is `795 declarations checked, 0 nonstandard, 0 missing`.
Only `propext`, `Classical.choice` and `Quot.sound` are accepted. No new axioms,
`sorry` proofs or native-evaluation certificates are used.

No playground JavaScript, numerical replay or animation claim is added by this
work. The earlier browser evidence remains separate from these Lean results.
