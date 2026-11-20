# The Leech symmetry group

**Co₀ status is partial.** A symmetry here is a distance-preserving bijection of the Leech lattice fixing the origin. Coordinates use the existing √8 scale. Squared length 64 in these files is squared length 8 in the usual normalization.

| Milestone | Lean theorem | What it proves | What remains conditional in this release |
| --- | --- | --- | --- |
| 1. Explicit code reorderings | [GolayMathieu.rep_code](../MathieuGroup.lean#L52) | Each of 129 listed permutations of the 24 coordinates preserves the extended binary Golay code. | This theorem has no pending proof hypothesis. It does not establish reachability of the norm-64 lattice vectors. |
| 2. Size of the reordering group | [GolayMathieu.card_mathieu](../MathieuGroup.lean#L147) | The group of **all** code-preserving coordinate permutations has 244,823,040 elements. The same file proves that the displayed list generates it. | This is the reordering-group size. The full lattice-group size still needs the remaining orbit argument. |
| 3. A symmetry moving the standard axes | [LeechSextet.moves_frame](../LeechSextet.lean#L135) | An explicit lattice involution takes `8e₀` outside the 48 standard axis vectors. | Reaching every norm-64 lattice vector and deriving the full group size are outside this release. |
| 4. Reaching every vector of squared length 64 | Not included | The published conditional theorem needs this reachability hypothesis. | No proof of that hypothesis is included here. |
| 5. Size of the full symmetry group | Not included | The target is 8,315,553,613,086,720,000. | No theorem stating that full group size is included here. |

For the second milestone, mark coordinates 0, 1, 2, 3, 4, 13 and 5 in that order. After fixing the earlier marks, the next one has 24, 23, 22, 21, 20, 3 and 16 possible images, respectively. Lean checks a permutation for each choice. Fixing all seven marks fixes seventeen particular octads, whose membership patterns distinguish all 24 coordinates. Multiplying the seven orbit lengths gives the group order. [Seven-point proof](../MathieuBase.lean) · [Reproducible permutation data](../scripts/build_mathieu_data.py).

For the third milestone, split the coordinates into six tetrads. In each tetrad subtract half the sum of its entries from every coordinate, then negate the second tetrad. The existing basis lets Lean check that division by two lands in the lattice for every input. The matrix identity proves preservation of squared length. [Formula and proof](../LeechSextet.lean).

## Earlier results used here

- `mem_autGroup_iff` identifies the additive norm-preserving bijections with the distance-preserving bijections fixing zero. The 196,560 shortest vectors span the lattice, and the action on them is faithful. Negation is a central involution. [LeechSymmetry.lean](../LeechSymmetry.lean).
- The squared-length-64 vectors congruent to `8e₀` modulo twice the lattice are the 48 vectors `±8eᵢ`. Fixing one axis preserves this standard frame. [Standard frame proof](../LeechSymmetry.lean).
- Golay sign changes form a subgroup of order 4,096. The sum congruence follows from integrality of the existing lattice. [LeechMonomial.lean](../LeechMonomial.lean).
- A symmetry preserves the frame iff it is a code permutation composed with a Golay sign change. The remaining group-generation statement is conditional on reaching every squared-length-64 lattice vector. [Frame stabilizer and conditional theorem](../LeechFrameStabilizer.lean).

The literature gives 8,292,375 frames and the target Co₀ order above. Neither count is proved in this release. [Wilson, §§5.2–5.3](https://webspace.maths.qmul.ac.uk/r.a.wilson/simplegroups_files/notes5.pdf).

## Publication checks

GitHub's [PR build and full axiom audit](https://github.com/NousVolition/discrete-gap-inequalities-lean/actions/runs/44662521061) and [push build](https://github.com/NousVolition/discrete-gap-inequalities-lean/actions/runs/44662515163) passed for proof commit `37cb4d3d3142728864d6bcc0c8b279a7e051bba5` before this status update. Both logs report **830 declarations checked, 0 nonstandard, 0 missing**. The [CI receipt](leech-milestones-ci.json) records those checks.

The finished new proof modules are `MathieuData`, `MathieuBase`, `MathieuGroup` and `LeechSextet`, with their existing proved dependencies and axiom inventory. No unfinished Conway proof module is part of this release. The symmetry status remains **partial**.

## Reproduce the proofs

```sh
python3 scripts/build_mathieu_data.py --check
lake build MathieuGroup LeechSextet CheckAxioms
lake env lean CheckAxioms.lean > axioms.txt
python3 .github/check_axioms.py CheckAxioms.lean axioms.txt
python3 scripts/check_leech_symmetry_evidence.py
```

The audit covers 830 declarations, including 35 added for milestones 1–3. Lean's kernel checks the permutation tables and the doubled matrix. The last command compares saved hashes and axiom reports with the checkout. [Publication verification](leech-symmetry-verification-2026-11-20-publication.json) · [Proof-stage verification](leech-symmetry-verification-2026-11-20-m123.json) · [Earlier 795-declaration audit](leech-symmetry-verification.json).
