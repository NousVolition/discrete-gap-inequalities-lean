# The Leech symmetry group

For the Leech lattice with the origin fixed, the full symmetry group has order 8,315,553,613,086,720,000, with explicit generators, proved in Lean. The generators are the Golay sign changes, 129 code-preserving coordinate permutations and the sextet involution. [Group order](../ConwayOrder.lean#L29) · [Generating set](../ConwayGenerators.lean#L21).

A symmetry is a distance-preserving bijection fixing zero. In the integer coordinates used here, squared length 64 corresponds to squared length 8 in the usual normalization.

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
- A symmetry preserves the frame iff it is a code permutation composed with a Golay sign change. Milestone 4 proves that the generators reach every squared-length-64 vector, supplying the orbit hypothesis used to prove generation. [Frame stabilizer](../LeechFrameStabilizer.lean) · [Orbit theorem](../ConwayTransitivity.lean#L108) · [Generation theorem](../ConwayGenerators.lean#L21).

The Lean order proof counts ordered pairs of perpendicular shortest vectors and their stabilizer. Wilson gives a frame count of 8,292,375 for comparison. [Counting argument](leech-symmetry-order.md). [Wilson, §§5.2–5.3](https://webspace.maths.qmul.ac.uk/r.a.wilson/simplegroups_files/notes5.pdf).

## Publication checks

GitHub built the proof and ran the full axiom audit before and after merging PR #9. Both runs reported **949 declarations checked, 0 nonstandard, 0 missing**. Milestones 4–5 add 44 declarations to the previous 905. [Pull request build](https://github.com/NousVolition/discrete-gap-inequalities-lean/actions/runs/44674659364/job/136083513003) · [Merged build](https://github.com/NousVolition/discrete-gap-inequalities-lean/actions/runs/44675102913/job/136084952916) · [Full axiom output](axioms-2026-11-20-order-949.txt).

The earlier 830-declaration audit for milestones 1–3 is recorded in the [historical CI receipt](leech-milestones-ci.json).

## Reproduce the proofs

```sh
python3 scripts/build_mathieu_data.py --check
lake build ConwayGenerators ConwayOrder CheckAxioms
lake env lean CheckAxioms.lean > axioms.txt
python3 .github/check_axioms.py CheckAxioms.lean axioms.txt
python3 scripts/check_leech_symmetry_evidence.py
```

The inventory includes 52 symmetry foundations, 35 results for milestones 1–3 and 44 for milestones 4–5. The evidence checker compares source hashes, theorem names and all 949 axiom reports. [Current verification](leech-symmetry-verification-2026-11-20-order-publication.json) · [Previous 905-declaration verification](leech-symmetry-verification-2026-11-20-plumbing-help.json).
