# Generators and order of the Leech lattice symmetry group

The group of distance-preserving bijections of this lattice fixing zero has **8,315,553,613,086,720,000 elements**. The Golay sign changes, the listed coordinate reorderings and one involution on six blocks of four coordinates generate the whole group. Both statements use the lattice defined in this project. [Order](../ConwayOrder.lean#L29) · [Generators](../ConwayGenerators.lean#L21) · [Definition of a symmetry](../LeechSymmetry.lean#L271).

| Milestone | Lean theorem | What it establishes |
| --- | --- | --- |
| 1. Coordinate reorderings | [`GolayMathieu.rep_code`](../MathieuGroup.lean#L52) | Each of the 129 listed permutations preserves the Golay code. |
| 2. Reordering group | [`GolayMathieu.card_mathieu`](../MathieuGroup.lean#L147) | There are 244,823,040 code-preserving permutations. The list generates them all. |
| 3. Moving an axis | [`LeechSextet.moves_frame`](../LeechSextet.lean#L135) | The involution takes the first axis vector outside the standard frame. |
| 4. Reaching every vector of squared length 64 | [`ConwayMoves.norm64_transitive`](../ConwayTransitivity.lean#L108) | Every lattice vector of this squared length is an image of `8e₀` under the generators. Squared length 64 uses the project's integer coordinates. |
| 5. Full group order | [`ConwayOrder.card_aut`](../ConwayOrder.lean#L29) | Orbit–stabilizer gives the order of the full origin-fixing group. |

## How an arbitrary vector reaches an axis

Start with any vector of squared length 64. Among its images under the generators, choose one with the largest possible absolute coordinate. Any four coordinates can be moved into the first block and given chosen signs. Applying the block involution then bounds the sum of their absolute values by twice that largest coordinate. With the parity and squared-length constraints, the four largest absolute values must either start with 8 or be (6,2,2,2).

An entry of size 8 uses all the squared length and gives an axis. In the second case, the block involution takes the four positive entries to (0,−4,−4,−4). The same four-coordinate bound forces every remaining entry to vanish, leaving squared length 48. This rules out the second case. [Four-coordinate bound](../ConwayMoves.lean) · [Orbit proof](../ConwayTransitivity.lean#L108).

## Where the factors come from

Choose a shortest vector and then a shortest vector perpendicular to it. There are **196,560** choices for the first and **93,150** for the second. To count the second choices for `(4,−4,0,…)`, count signed equalities between two distinct coordinates. The three shortest-vector families contribute 926, 536 and 506 equalities per vector. The 1,104 choices of an ordered coordinate pair and a sign each give the same count. [Shortest-vector families](../LeechKissing.lean) · [Double count](../ConwayNeighborCount.lean#L74) · [Count for any first vector](../ConwayOrder.lean#L15).

The sum of a perpendicular pair has squared length 64. Move the sum to `8e₀`. The two summands then each have first coordinate 4 and just one other nonzero coordinate. A code permutation and sign change take the pair to `(4,−4,0,…)` and `(4,4,0,…)`. This gives one orbit of ordered pairs. [Pair transitivity](../ConwayPairs.lean#L68).

Fixing both vectors in this pair fixes their sum and difference, the first two axes. The converse follows by preserving inner products. The stabilizer has **443,520** choices of coordinate permutation and **1,024** choices of Golay sign change. This gives **454,164,480** symmetries fixing the pair. Multiplying the three factors gives the order above. [Pair stabilizer](../ConwayPairs.lean#L151) · [Stabilizer size](../ConwayStabilizer.lean#L106).

## Reproduce the check

```sh
lake build ConwayGenerators ConwayOrder CheckAxioms
lake env lean CheckAxioms.lean > axioms.txt
python3 .github/check_axioms.py CheckAxioms.lean axioms.txt
python3 scripts/check_leech_symmetry_evidence.py
```

GitHub built the proof on the pull request and on merged main. Each full audit checked 949 declarations, with 0 nonstandard axioms and 0 missing reports. The earlier 900-declaration run records the milestone branch before it was combined with main. [Pull request build](https://github.com/NousVolition/discrete-gap-inequalities-lean/actions/runs/44674659364/job/136083513003) · [Merged build](https://github.com/NousVolition/discrete-gap-inequalities-lean/actions/runs/44675102913/job/136084952916) · [Full axiom output](axioms-2026-11-20-order-949.txt) · [Earlier branch verification](leech-symmetry-verification-2026-11-20-order-main.json).
