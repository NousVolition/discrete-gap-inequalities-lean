# The Leech lattice's 196,560 shortest vectors

Steps 3 and 4 are proved: every shortest nonzero vector in the lattice defined by `LeechLattice.InLeech` belongs to one of three disjoint families, and those families contain 196,560 distinct vectors in total. The proof builds on the lattice definition and minimum-length results introduced in commit `558c7524dfb0000e8198dac5d06aa3c31c8341f6`.

Coordinates remain integers in the existing `√8` scaling. Throughout these statements, squared length means `∑ i, x i ^ 2`; its minimum is 32. The work does not replace the lattice definition or assume the classification as an axiom.

| Family | Parameters and membership rule | Distinct vectors |
| --- | --- | ---: |
| Two entries ±4, all others zero | An unordered pair of positions and either sign at each position | `choose 24 2 × 4 = 1,104` |
| Eight entries ±2, all others zero | One of the 759 Golay octads, with an even number of negative entries | `759 × 128 = 97,152` |
| One entry ∓3, all others ±1 | One of the 4,096 Golay words and a distinguished position | `4,096 × 24 = 98,304` |
| **Total** | The three families are disjoint and exhaustive | **196,560** |

For the odd family, a true bit gives −1 away from the distinguished position and +3 at that position; a false bit gives +1 and −3 respectively. Thus the positions congruent to 3 modulo 4 recover the codeword. The unique coordinate with magnitude 3 recovers the distinguished position. `oddVector_injective` proves that different parameter pairs cannot produce the same vector.

The correction to the earlier outline is preserved. The sum rule alone does not exclude every all-±1 vector. The existing odd minimum-length proof also uses the fact that Golay weights are divisible by four. In the new proof, `oddVector_mem` uses that same divisibility theorem to show that every constructed odd-family vector satisfies the sum rule modulo 8.

## What Lean checks

- [LeechMinimal.lean](../LeechMinimal.lean): `minimal_iff` proves both directions of the three-shape classification for `InLeech x ∧ normSq x = 32`. Equality in coordinate-square bounds forces each shape; the converse proofs check the lattice conditions.
- [LeechCodeCounts.lean](../LeechCodeCounts.lean) and [LeechOctadCount.lean](../LeechOctadCount.lean): the encoder is injective, so its 4,096 messages give 4,096 distinct codewords. The existing block-fold weight counts count distinct octads, giving 759. This connects the computed table to the mathematical subtype; it does not insert a new table as an assumption.
- [LeechSignVectors.lean](../LeechSignVectors.lean): sign assignments recover their support and signs. Transporting the existing eight-bit even-parity count gives 128 assignments on any eight-element support.
- [LeechFourCount.lean](../LeechFourCount.lean), [LeechOctadVectors.lean](../LeechOctadVectors.lean) and [LeechOddCount.lean](../LeechOddCount.lean): bijections between the parameters and the actual vector families establish their cardinalities.
- [LeechKissing.lean](../LeechKissing.lean): the families are pairwise disjoint. `leech_kissing_number` adds their proved cardinalities to obtain 196,560 norm-32 vectors. `card_minimal_eq_code_formula` connects this cardinality to `GolayLeechBridge.leech_kissing_from_code`. `shortest_iff_norm32` identifies these with the shortest nonzero lattice vectors, and `card_shortest_vectors` counts that subtype.

The main conclusion is a cardinality theorem about the lattice already defined in Lean:

```lean
def IsShortest (x : Vec) : Prop :=
  InLeech x ∧ x ≠ 0 ∧
    ∀ y : Vec, InLeech y → y ≠ 0 → normSq x ≤ normSq y

theorem card_shortest_vectors :
    Fintype.card {x : Vec // IsShortest x} = 196560
```

The finite types used for counting are constructed from the proved bijections. Lean does not enumerate an arbitrary box of integer vectors and infer that nothing lies outside it.

## Reproducing the checks

Use the pinned Lean `v4.34.0-rc2` and Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`:

```sh
lake exe cache get
lake build
lake env lean CheckAxioms.lean > axioms.txt
python3 .github/check_axioms.py CheckAxioms.lean axioms.txt
```

The modules are Lake libraries; `LeechKissing` is a default build target and is imported by `CheckAxioms`. The [verification record](leech-shortest-verification.json) preserves the compilation scope, source hashes and audit result at commit `8dea8004e700f5ddd9eeea942ab9518d4463a28c`. The [axiom output](leech-shortest-axioms.txt) includes all 654 audited declarations, including the 50 new public theorems. The audit allows only `propext`, `Classical.choice` and `Quot.sound`; private helper proofs are covered through their public dependents.

To check that historical record, check out commit `8dea8004e700f5ddd9eeea942ab9518d4463a28c` and run `python3 scripts/check_leech_evidence.py`. For the current correspondence evidence use `python3 scripts/check_playground_evidence.py`. That command checks hashes and the saved axiom reports; it does not rerun Lean.

The audit parser also now handles theorem names ending in an apostrophe, including the existing `LeechLattice.sum_add'` and `sum_neg'`. Its five regression checks cover these names, axiom-free proofs, nonstandard axioms, missing reports and an empty inventory: `python3 .github/test_check_axioms.py`. CI runs these checks before the Lean build.

## Scope and later results

This proves the shortest-vector classification and count for `InLeech`/`leechLattice`. [LeechBasis.lean](../LeechBasis.lean), added later in commit `14518ce7be879b30310e0cc6c1c32d70318b232e`, proves the basis determinant `8^12` and the lattice's unimodularity and evenness after rescaling. The symmetry group and a separate Euclidean sphere-packing construction remain outside these proofs.

The [playground's Leech page](https://nousvolition.github.io/sparkle-sand-playground/#leech) uses a different, modulo-23 Golay generator. The [coordinate correspondence is now proved](playground-golay.md), and the existing minimum-length and shortest-vector results transfer to that code’s lattice. The actual JavaScript outputs have a separate reproducible check; browser execution and displayed trajectories are not formalized.
