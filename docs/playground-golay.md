# The playground's Golay generator

The playground's modulo-23 Golay code and the repository's modulo-11 code are the same after relabeling their 24 coordinates. Lean proves the correspondence in both directions. The existing lattice definition, minimum-length proof and shortest-vector count are used unchanged.

The map below sends each playground coordinate, numbered from 0 to 23, to its Lean coordinate:

```text
playground:  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20 21 22 23
Lean:        0  1  2  3  4  5  6 17  8 12  9 16  7 18 14 13 19 20 22 23 15 10 11 21
```

Thus `toLean x` places the value from playground position `i` at Lean position `coordinateEquiv i`. This is a coordinate permutation, not a change of scale or signs. There is no claim that the codes agree without this relabeling; they share only four words in their original numbering.

## What Lean proves

[PlaygroundGolay.lean](../PlaygroundGolay.lean) defines the modulo-23 residue loop, its 23 shifts, the parity bit and the all-ones generator. It models the page's descending numeric basis reduction with XOR and insertion into a descending list. `computedBasis_eq` checks the resulting 12 rows inside Lean's kernel. `IsPlayWord` uses this computed recipe, rather than assuming a supplied basis is correct.

`forward_row` and `reverse_row` check 12 basis identities in each direction, using explicit message witnesses and the coordinate permutation. Closure under XOR extends those identities to every codeword. The main result is:

```lean
theorem code_correspondence (w : Fin 24 → Bool) :
    IsPlayWord w ↔ LeechLattice.IsGolayWord (toLean w)
```

The inverse permutation is checked as part of `coordinateEquiv`. `weight_toLean` proves that the permutation preserves word weight; `card_play_code` transfers the existing count of 4,096 codewords. The finite checks use kernel reduction, not `native_decide` or an external certificate accepted as an axiom.

[PlaygroundLeech.lean](../PlaygroundLeech.lean) applies the same Conway–Sloane membership rule with `IsPlayWord` in place of `IsGolayWord`. It proves:

| Statement | Meaning |
| --- | --- |
| `lattice_correspondence` | `InPlayLeech x ↔ InLeech (toLean x)` for every integer vector |
| `norm_toLean` | Squared length is unchanged by the permutation |
| `play_norm_ge_32` | Every nonzero vector in this lattice has squared length at least 32 |
| `play_minimal_iff` | Norm-32 lattice vectors have the three previously proved shapes after relabeling |
| `shortest_correspondence` | A vector is shortest in one lattice exactly when its image is shortest in the other |
| `play_shortest_iff_norm32` | The shortest nonzero vectors are precisely the norm-32 lattice vectors |
| `card_play_shortest_vectors` | There are 196,560 such shortest vectors |

These are transfers from [LeechLattice.lean](../LeechLattice.lean) and [LeechKissing.lean](../LeechKissing.lean). Steps 1–4 of the original plan were already proved; this work supplies the missing coordinate connection.

## What was checked outside Lean

The [archived JavaScript slice](playground-golay-source.js) is copied from the Leech template in playground commit [c89951d](https://github.com/NousVolition/sparkle-sand-playground/blob/c89951d26251006fe9a5c6f3d12d1df61a88ddf0/index.html). Its [source record](playground-golay-source.json) specifies the selectors and normalized SHA256. It stops before DOM updates and floating-point projection.

[check_playground_golay.cjs](../scripts/check_playground_golay.cjs) executes that actual source. It reads the basis, permutation and both message witnesses from the Lean source, checks all 4,096 mapped codewords, and checks every generated vector against the existing lattice rule in Lean coordinates. The [saved replay](playground-golay-replay.json) reports:

- 4,096 distinct codewords, with weights `0 / 8 / 12 / 16 / 24` occurring `1 / 759 / 2,576 / 759 / 1` times;
- 1,104, 97,152 and 98,304 vectors in the three families;
- 196,560 distinct vectors, all of squared length 32, all satisfying the mapped lattice rule.

This replay connects the archived JavaScript outputs to the formal model. It is an external computation, not a Lean theorem about JavaScript semantics, the browser or the displayed projection. Passing an `index.html` path also requires its generator/vector source slice to match the archive; a changed slice fails the check rather than silently inheriting the result.

## Reproduce

Use the pinned Lean `v4.34.0-rc2` and Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`:

```sh
lake exe cache get
lake build
lake env lean CheckAxioms.lean > axioms.txt
python3 .github/check_axioms.py CheckAxioms.lean axioms.txt
node scripts/check_playground_golay.cjs
# Optional comparison with a playground checkout:
node scripts/check_playground_golay.cjs ../sparkle-sand-playground/index.html
```

The [verification record](playground-golay-verification.json) records fresh local compilation of the two new modules and `CheckAxioms`, using default compiler options apart from options explicitly in the source. It distinguishes reused, unchanged local artifacts from newly compiled modules. The [axiom output](playground-golay-axioms.txt) covers all 682 audited declarations, including all 28 new public theorems. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. CI builds the project and repeats the audit.

`python3 scripts/check_playground_evidence.py` checks the saved source hashes, audit inventory and replay record. It does not rerun Lean or JavaScript. The older shortest-vector receipt and its 654-declaration audit are retained as historical evidence at commit `8dea8004e700f5ddd9eeea942ab9518d4463a28c`.

## Still open

The lattice's volume/determinant and symmetry group remain unproved in this project. The coordinate permutation here identifies two presentations of a code; it is not a classification of lattice symmetries. Browser execution, floating-point projection and animation also remain outside these Lean proofs.
