# The Leech symmetry group

**The full origin-fixing symmetry group has 8,315,553,613,086,720,000 elements.** A symmetry here is a distance-preserving bijection of the Leech lattice fixing the origin. Coordinates use the existing √8 scale. Squared length 64 in these files is squared length 8 in the usual normalization.

| Milestone | Lean theorem | What it establishes |
| --- | --- | --- |
| 1. Coordinate reorderings | [`GolayMathieu.rep_code`](../MathieuGroup.lean#L52) | Each of the 129 listed permutations preserves the Golay code. |
| 2. Reordering group | [`GolayMathieu.card_mathieu`](../MathieuGroup.lean#L147) | There are 244,823,040 code-preserving permutations. The list generates them all. |
| 3. Moving an axis | [`LeechSextet.moves_frame`](../LeechSextet.lean#L135) | The involution takes the first axis vector outside the standard frame. |
| 4. Reaching every vector of squared length 64 | [`ConwayMoves.norm64_transitive`](../ConwayTransitivity.lean#L108) | Every lattice vector of this squared length is an image of `8e₀` under the generators. Squared length 64 uses the project's integer coordinates. |
| 5. Full group order | [`ConwayOrder.card_aut`](../ConwayOrder.lean#L29) | Orbit–stabilizer gives the order of the full origin-fixing group. |

For the second milestone, mark coordinates 0, 1, 2, 3, 4, 13 and 5 in that order. After fixing the earlier marks, the next one has 24, 23, 22, 21, 20, 3 and 16 possible images, respectively. Lean checks a permutation for each choice. Fixing all seven marks fixes seventeen particular octads, whose membership patterns distinguish all 24 coordinates. Multiplying the seven orbit lengths gives the group order. [Seven-point proof](../MathieuBase.lean) · [Reproducible permutation data](../scripts/build_mathieu_data.py).

For the third milestone, split the coordinates into six tetrads. In each tetrad subtract half the sum of its entries from every coordinate, then negate the second tetrad. The existing basis lets Lean check that division by two lands in the lattice for every input. The matrix identity proves preservation of squared length. [Formula and proof](../LeechSextet.lean).

## Earlier results used here

- `mem_autGroup_iff` identifies the additive norm-preserving bijections with the distance-preserving bijections fixing zero. The 196,560 shortest vectors span the lattice, and the action on them is faithful. Negation is a central involution. [LeechSymmetry.lean](../LeechSymmetry.lean).
- The squared-length-64 vectors congruent to `8e₀` modulo twice the lattice are the 48 vectors `±8eᵢ`. Fixing one axis preserves this standard frame. [Standard frame proof](../LeechSymmetry.lean).
- Golay sign changes form a subgroup of order 4,096. The sum congruence follows from integrality of the existing lattice. [LeechMonomial.lean](../LeechMonomial.lean).
- A symmetry preserves the frame iff it is a code permutation composed with a Golay sign change. The norm-64 orbit proof supplies the transitivity hypothesis in the frame argument. [Frame stabilizer](../LeechFrameStabilizer.lean) · [Transitivity](../ConwayTransitivity.lean#L108) · [Explicit generators](../ConwayGenerators.lean#L21).

The group-order proof counts ordered perpendicular pairs of shortest vectors. The separate count of 8,292,375 frames remains outside this proof. [Order argument](leech-symmetry-order.md).

## Verification

The [proof-branch audit](https://github.com/NousVolition/discrete-gap-inequalities-lean/actions/runs/44674594813) checked 900 declarations. The [PR build](https://github.com/NousVolition/discrete-gap-inequalities-lean/actions/runs/44674659364) and [merged-main build](https://github.com/NousVolition/discrete-gap-inequalities-lean/actions/runs/44675102913) checked 949, including later additions to main. Each reported zero nonstandard axioms and zero missing reports. [Full axiom output](axioms-2026-11-20-co0-release.txt) · [Saved verification](leech-symmetry-verification-2026-11-20-co0-release.json) · [Reproduction commands](leech-symmetry-order.md#reproduce-the-check).
