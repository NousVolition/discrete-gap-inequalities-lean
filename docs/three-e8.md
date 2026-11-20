# Three E₈ lattices give the same Leech lattice

The Leech lattice already defined in this project can be built by gluing three
orthogonal copies of E₈. Lean proves equality with the existing lattice, and
proves that every lattice vector has one of 4,096 distinct gluing labels.
The minimum-length, shortest-vector count and volume results are reused.

The [playground’s Leech page](https://nousvolition.github.io/sparkle-sand-playground/#leech)
shows the three blocks and their combined projection. Its integer calculations
have a separate replay check. The graphics are not Lean proofs.

## What is glued

We keep the project's integer coordinates: divide them by √8 to get the usual
Leech normalization. In these coordinates each base block is **4E₈**. Its eight
simple roots have Gram matrix `−16 * E8PlumbingBridge.E8_matrix`. Thus the same
E₈ matrix that appears in the plumbing file specifies the geometry of each block;
this is an algebraic connection, not a claim about a plumbing manifold.

The coordinate blocks, numbered from zero in Lean's existing coordinates, are:

| Block | Coordinates | Golay message marking the block |
| --- | --- | ---: |
| I | 1, 12, 13, 14, 16, 17, 18, 22 | 2 |
| II | 0, 2, 5, 6, 7, 15, 20, 21 | 229 |
| III | 3, 4, 8, 9, 10, 11, 19, 23 | 3864 |

`base` embeds the eight roots in each block, giving 24 generators. `glue` lists
twelve explicit vectors. The construction initially takes all integer
combinations of these 36 generators. It does not use `InLeech` as its definition.

Lean checks both inclusions using integer change-of-basis witnesses:

1. Every base and glue generator belongs to the existing Leech lattice.
2. Every vector of the already proved Leech basis is a combination of the new
   base and glue generators.

`glued_eq_leech` then proves equality of the **whole infinite lattices**. It is
not a test of a finite sample or just their shortest vectors.

## Why there are 4,096 shifts

Twice every glue vector belongs to the base. Therefore an arbitrary integer
coefficient can be reduced to an on/off choice, leaving a base vector. Twelve
choices give `2^12 = 4096` labels.

To rule out duplicate cosets, twelve integer linear readouts are evaluated
modulo 8. Each readout is zero on every base generator, is 4 on its corresponding
glue generator, and is zero on the other eleven. Lean checks those finite
identities and proves their consequences for arbitrary integer combinations.

`leech_unique_glue` states that every Leech vector belongs to one and only one
binary translate of the base. `glue_label_count` counts the labels. Together
they establish 4,096 distinct translates covering the lattice. In ordinary
Leech units the base is `(√2 E₈)³`.

This is an explicit three-E₈ gluing in this project's coordinates. It does not
claim to identify our twelve switches with the labels of a particular published
Turyn glue table. For the standard polarized construction and its 4,096 cosets,
see Corlay et al., [*A Turyn-based neural Leech decoder*, §2](https://perso.telecom-paristech.fr/ciblat/docs_recherche/congres/wcc2019.pdf).
The Lean proof uses the displayed integer witnesses rather than a uniqueness
classification of even unimodular lattices.

## Lean results

| File / theorem | Result |
| --- | --- |
| [LeechThreeE8.lean](../LeechThreeE8.lean), `base_blocks`, `e8_gram`, `base_gram` | Three disjoint orthogonal E₈ blocks with the specified scale and plumbing Gram matrix. |
| `block_norm` | The coordinate split preserves squared length. |
| `glued_eq_leech` | The constructed lattice equals `LeechLattice.leechLattice`. |
| `glued_norm_ge_32`, `glued_kissing_number` | Reuse the lower bound 32 and the count of 196,560 norm-32 vectors. |
| `glued_basis_and_volume`, `glued_even` | Reuse the existing basis, determinant `8^12` and squared-length divisibility by 16. `LeechBasis.leech_unimodular` continues to give unimodularity after rescaling. |
| `playground_correspondence` | Compose construction equality with the existing playground-to-Lean coordinate permutation. |
| [LeechThreeE8Cosets.lean](../LeechThreeE8Cosets.lean), `leech_unique_glue`, `glue_label_count` | Unique binary glue labels for all lattice vectors, with 4,096 labels. |

The 32 new public theorems are included in [CheckAxioms.lean](../CheckAxioms.lean).
That verification audited 743 declarations. The later [symmetry work](leech-symmetry.md)
brings the inventory to 830. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. There are no `sorry` proofs,
`native_decide` proofs or additional assumptions about the construction data.

## Reproduce the checks

The project pins Lean `v4.34.0-rc2` and Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`.

```sh
lake build
lake env lean CheckAxioms.lean > axioms.txt
python3 .github/check_axioms.py CheckAxioms.lean axioms.txt
python3 scripts/build_three_e8_data.py --check
node scripts/check_three_e8.cjs ../sparkle-sand-playground
```

The Python script reconstructs the witnesses using rational arithmetic and
compares them with [the saved data](three-e8-construction.json) and
[LeechThreeE8Data.lean](../LeechThreeE8Data.lean). Lean independently checks each
identity used in the proof, so the Python script is outside the trusted proof.

The Node replay reads the playground's actual generator and decomposition code,
compares its tables with the Lean source, checks all 4,096 glue labels, and
reconstructs each of the 196,560 displayed vectors as a glue shift plus an
integer combination of the three E₈ bases. It also checks the 240 reference
roots in each block. These are **external execution checks**, recorded in
[three-e8-replay.json](three-e8-replay.json), not additional Lean theorems.

The replay also records the number of shortest vectors in each glue coset and
the component squared-length patterns. Those particular distributions are
measured outputs; the Lean results above do not claim to prove them.

The browser projection, glow, interaction and full lattice symmetry group are
outside these proofs. The 240-point E₈ pictures are reference root projections;
a highlighted component can lie in a shifted copy. The screen does not show
24-dimensional distances faithfully.
