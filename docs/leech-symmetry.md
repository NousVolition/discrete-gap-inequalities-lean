# The Leech symmetry group

For the Leech lattice with the origin fixed, the full symmetry group has order 8,315,553,613,086,720,000, with explicit generators, proved in Lean. [Order](../ConwayOrder.lean#L29) · [Generators](../ConwayGenerators.lean#L21). A symmetry here is a distance-preserving bijection of the Leech lattice fixing the origin. Coordinates use the existing √8 scale. Squared length 64 in these files is squared length 8 in the usual normalization.

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

## Coordinate frames

A coordinate frame is an unordered set of 48 lattice vectors. Each has squared length 64 in the integer coordinates used here, and the difference of any two is twice a lattice vector. Lean counts **8,292,375** such sets. [Definition](../LeechCoordinateFrames.lean#L16) · [Count of all frames](../LeechCoordinateFrames.lean#L129).

Pick any member of a frame and carry it to the first standard axis using norm-64 transitivity. All 48 members then lie in the standard congruence class. That class contains 48 vectors of squared length 64, so the transported frame contains every one of them. This proves that every frame is an image of the standard frame. [Transitivity on frames](../LeechCoordinateFrames.lean#L86).

A symmetry preserving the standard frame is uniquely determined by a code-preserving permutation and a Golay sign change. There are 244,823,040 choices of permutation and 4,096 choices of sign change. Orbit–stabilizer gives 8,315,553,613,086,720,000 / (244,823,040 × 4,096) = 8,292,375. [Frame stabilizer](../LeechCoordinateFrames.lean#L124) · [Group order](../ConwayOrder.lean#L29).

To reproduce the frame check, run `lake build LeechCoordinateFrames CheckAxioms`, then `lake env lean CheckAxioms.lean > axioms.txt` and `python3 .github/check_axioms.py CheckAxioms.lean axioms.txt`. The [frame verification record](leech-symmetry-verification-2026-11-20-coordinate-frames.json) and [full audit](axioms-2026-11-20-coordinate-frames.txt) cover 952 declarations.

## Vectors of squared length 48

The Leech lattice has **16,773,120 vectors of squared length 48** in the project's integer coordinates. This is squared length 6 in the usual normalization. The theorem counts all lattice vectors at that length, including both signs. [Count theorem](../LeechNorm48.lean#L24).

Each coordinate lies between −6 and 6. All 24 coordinates have the same parity. In an even vector, the positions congruent to 2 modulo 4 form a Golay codeword. In an odd vector, the positions congruent to 3 do. Its weight is the number of those positions.

| Coordinate parity | Golay residue word | Words | Vectors per word | Subtotal |
| --- | --- | ---: | ---: | ---: |
| Even | Weight 8 | 759 | 4,096 | 3,108,864 |
| Even | Weight 12 | 2,576 | 2,048 | 5,275,648 |
| Odd | Any weight | 4,096 | 2,048 | 8,388,608 |
| **Total** | | | | **16,773,120** |

For a weight-eight word, eight entries have magnitude 2 and one of the other sixteen has magnitude 4. For a weight-twelve word, twelve entries of magnitude 2 use the whole squared-length budget. In each case the sum modulo eight fixes the parity of the signs on the entries of magnitude 2.

For an odd vector, each of the 24 entries contributes at least one to the squared length. To add the remaining 24, one entry can have magnitude 5, or three entries can have magnitude 3. The residue word fixes the signs once these positions are chosen. That gives 24 + 2,024 = 2,048 choices per word.

For each residue word, Lean counts the coordinate choices that give the required squared length and sum modulo eight. It removes one coordinate at a time, recording the remaining squared-length budget and the parity needed for the sum. Each vector determines its word and all its coordinate choices, and every accepted choice gives a lattice vector. The even-coordinate count vanishes for every other Golay weight. [Counting recurrence](../LeechNorm48Count.lean#L71) · [Even choices](../LeechNorm48Count.lean#L155) · [Odd choices](../LeechNorm48Count.lean#L152) · [Weight-twelve word count](../LeechDodecadCount.lean#L11).

To reproduce, run `lake build LeechNorm48 CheckAxioms`, then `lake env lean CheckAxioms.lean > axioms.txt` and `python3 .github/check_axioms.py CheckAxioms.lean axioms.txt`. The [verification record](leech-symmetry-verification-2026-11-20-norm48-shell.json) and [full transcript](axioms-2026-11-20-norm48-shell.txt) cover 959 declarations.

### Opposite pairs at squared length 48

A vector and its negative have the same squared length. Starting with either one gives the same pair {v, −v}. Only zero is its own negative, so at squared length 48 each pair contributes two vectors. Dividing 16,773,120 by two gives **8,386,560 pairs**. [One pair per vector](../LeechNorm48Pairs.lean#L15) · [Two vectors per pair](../LeechNorm48Pairs.lean#L20) · [Pair count](../LeechNorm48Pairs.lean#L25).

The [verification record](leech-symmetry-verification-2026-11-20-pair-wording.json) and [transcript](axioms-2026-11-20-norm48-pairs.txt) cover the 962 declarations in the length-48 release. The [shared proof and current check commands](#opposite-pairs-at-squared-lengths-32-and-64) cover all three lengths.

## Vectors of squared length 64

Every lattice vector of squared length 64 belongs to one coordinate frame. Move the vector to the first standard axis. Any frame containing that axis consists of the 48 norm-64 vectors in its congruence class modulo twice the lattice, so it must be the standard frame. Moving it back gives the unique frame containing the original vector. [Unique frame](../LeechCoordinateFrames.lean#L140).

A frame with one of its members marked now specifies a vector, and each vector gives one such pair. There are 8,292,375 choices of frame and 48 choices of member. Lean therefore counts **398,034,000 vectors** of squared length 64 in the integer coordinates (squared length 8 in the usual normalization). Opposite vectors count separately. [Count theorem](../LeechCoordinateFrames.lean#L151).

The reproduction commands above check both the uniqueness and count theorems. The [verification record](leech-symmetry-verification-2026-11-20-norm64-shell.json) and [full audit](axioms-2026-11-20-norm64-shell.txt) cover 954 declarations.

## Opposite pairs at squared lengths 32 and 64

Pair each vector with its negative. They have the same squared length, and only zero is its own negative. At any positive squared length, each vector belongs to one pair and each pair has two vectors. The length-32, length-48 and length-64 counts all use this [pairing rule](../LeechOppositePairs.lean#L42).

| Squared length in the integer coordinates | Vectors | Opposite pairs |
| ---: | ---: | ---: |
| 32 | [196,560](../LeechKissing.lean#L67) | [98,280](../LeechShellPairs.lean#L11) |
| 48 | [16,773,120](../LeechNorm48.lean#L24) | [8,386,560](../LeechNorm48Pairs.lean#L25) |
| 64 | [398,034,000](../LeechCoordinateFrames.lean#L151) | [199,017,000](../LeechShellPairs.lean#L19) |

To check all three counts, run `lake build LeechShellPairs LeechNorm48Pairs CheckAxioms`, then `lake env lean CheckAxioms.lean > axioms.txt` and `python3 .github/check_axioms.py CheckAxioms.lean axioms.txt`. The [verification record](leech-symmetry-verification-2026-11-20-shell-pairs.json) and [full axiom output](axioms-2026-11-20-shell-pairs.txt) cover 967 declarations.

## Vectors of squared length 80

The Leech lattice has **4,629,381,120 vectors** at squared length 80 in these integer coordinates, or squared length 10 in the usual normalization. Counting a vector and its negative together gives **2,314,690,560 opposite pairs**. [Vector proof](../LeechNorm80.lean#L88) · [Pair proof](../LeechNorm80.lean#L109) · [Shared pairing rule](../LeechOppositePairs.lean#L42).

An entry of magnitude 8 would leave a nonzero lattice vector of squared length 16 after subtracting the signed coordinate axis. The minimum is 32, so every entry lies between −7 and 7. Each vector then determines a Golay word and a choice at each of the 24 coordinates. The proof counts the choices that give squared length 80 and the required sum modulo eight. [Coordinate bound](../LeechNorm80.lean#L34) · [How the choices count vectors](../LeechShellCoordinates.lean#L164).

| Coordinates | Golay word | Words | Vectors per word | Vectors |
| --- | --- | ---: | ---: | ---: |
| Even | Weight 8 | 759 | 606,208 | 460,111,872 |
| Even | Weight 12 | 2,576 | 565,248 | 1,456,078,848 |
| Even | Weight 16 | 759 | 524,288 | 397,934,592 |
| Odd | Any weight | 4,096 | 565,248 | 2,315,255,808 |
| **Total** | | | | **4,629,381,120** |

For even coordinates, words of weight 0 or 24 give no vectors at this length. Flipping all 24 bits pairs the words of weight 16 with those of weight 8. Lean checks each entry of the counting tables against the rule for adding one coordinate. [Even choices](../LeechNorm80Count.lean#L121) · [Odd choices](../LeechNorm80Count.lean#L117) · [Weight-16 words](../LeechNorm80.lean#L72).

## Layers along a shortest vector

Choose any shortest vector *s*. The table counts shortest vectors *v* by their dot product *s · v* in the playground’s integer coordinates. [Lean proof of the whole table](../LeechLayers.lean#L304).

| Dot product | Number of shortest vectors |
|---|---:|
| 0 | 93,150 |
| −8 or +8 | 47,104 each |
| −16 or +16 | 4,600 each |
| −32 or +32 | 1 each |
| Every other integer, including −24 and +24 | 0 |

Each vector has one dot product with *s*. The seven occupied layers contain 93,150 + 2 × (47,104 + 4,600 + 1) = 196,560 vectors. That accounts for every shortest vector.

For any shortest vector in the playground coordinates, 93,150 of the 196,560 shortest vectors are perpendicular to it. The coordinate permutation preserves the dot product, so the central layer follows from the partner count. A dot product of +24 would give a difference of squared length 16. A dot product of −24 would give a sum of squared length 16. Both would be nonzero lattice vectors below the minimum of 32. [Partner count](../ConwayOrder.lean#L15) · [Central layer in playground coordinates](../LeechLayers.lean#L18) · [Empty slots](../LeechLayers.lean#L27) · [Minimum length](../PlaygroundLeech.lean#L57).

For every shortest vector *s*, the [−8](../LeechLayers.lean#L211) and [+8](../LeechLayers.lean#L206) layers each have **47,104** vectors. The [−16](../LeechLayers.lean#L221) and [+16](../LeechLayers.lean#L216) layers each have **4,600**. The signs refer to the dot product *s · v* in the playground’s integer coordinates.

In the proof’s coordinates, take the shortest vector (4, −4, 0, …). Its dot product with *v* is four times the difference of the first two coordinates. Summing the square of that difference over all shortest vectors gives 524,160. Each coordinate contributes the same sum of squares, and the cross terms cancel because a lattice symmetry can flip the second coordinate while fixing the first. [Sum of squares](../LeechLayers.lean#L106).

Let *A* and *B* count the +8 and +16 layers. Negating *v* gives the same counts on the negative side. Removing the 93,150 perpendicular vectors and the one vector at each end gives *A + B = 51,704*. The sum of squares gives *A + 4B = 65,504*. Subtracting gives *B = 4,600*, then *A = 47,104*. Every shortest vector is the image of the reference vector under a symmetry that preserves dot products. [Counting argument](../LeechLayers.lean#L180) · [Transfer to any shortest vector](../LeechLayers.lean#L186).

The [+32 layer](../LeechLayers.lean#L233) contains only *s*. When *s · v = 32*, the difference *s − v* has squared length zero, so *v = s*. The [−32 layer](../LeechLayers.lean#L246) contains only *−s*. When *s · v = −32*, the sum *s + v* has squared length zero, so *v = −s*. Negating *s* preserves its length and keeps it in the lattice. This gives [one vector at +32](../LeechLayers.lean#L272) and [one at −32](../LeechLayers.lean#L277).

The Layers view also counts the generated vectors for the current selection and draws the projection in the browser.

Run `lake build LeechNorm80 LeechLayers CheckAxioms`, then `lake env lean CheckAxioms.lean > axioms.txt` and `python3 .github/check_axioms.py CheckAxioms.lean axioms.txt`. The [full axiom output](axioms-2026-11-20-layer-table.txt) and [verification record](leech-symmetry-verification-2026-11-20-layer-table.json) cover 1018 declarations.

## Layers for squared length 48

Choose any shortest vector *s* as the axis. Let *v* run over all lattice vectors of squared length 48 in the playground’s integer coordinates. [Lean proof of the layer table](../LeechLayers.lean#L446).

| Dot product *s · v* | Number of vectors |
|---|---:|
| 0 | 6,476,800 |
| −8 or +8 | 4,147,200 each |
| −16 or +16 | 953,856 each |
| −24 or +24 | 47,104 each |
| Every other integer | 0 |

The seven counts add up to 16,773,120. Lattice dot products are multiples of 8. The vectors *s − v* and *s + v* are both nonzero, so their squared lengths are at least 32. This puts *s · v* between −24 and +24. [Allowed dot products](../LeechLayers.lean#L334).

At +24, subtract *v* from *s*. The result is a shortest vector in the +8 layer. Subtract it from *s* again to recover *v*. This pairs the two layers and gives 47,104 vectors in each. Negation gives the same count at −24. [Bijection](../LeechLayers.lean#L372).

The proof first uses the axis (4, −4, 0, …). Write *d = v₀ − v₁*, so the dot product is *4d*. Coordinate permutations, sign changes and the four-coordinate lattice move give two sums over the whole shell. The sum of *d²* is 67,092,480, and the sum of *d⁴* is 743,178,240. Together with the total and the two outer counts, these determine the counts at 0, ±8 and ±16. A lattice symmetry takes the reference axis to any shortest vector and preserves dot products. [Second and fourth powers](../LeechNorm48Moments.lean#L30) · [Layer counts](../LeechLayers.lean#L412) · [Change of axis](../LeechLayers.lean#L429).

Run `lake build LeechNorm48Moments LeechLayers CheckAxioms`, then `lake env lean CheckAxioms.lean > axioms.txt` and `python3 .github/check_axioms.py CheckAxioms.lean axioms.txt`. The [axiom output](axioms-2026-11-20-norm48-layers.txt) and [verification record](leech-symmetry-verification-2026-11-20-norm48-layers.json) cover 1021 declarations.

## Layers for squared length 64

Choose any shortest vector *s*. The table counts vectors *v* of squared length 64 in the playground’s integer coordinates. [Lean proof](../LeechNorm64Layers.lean#L159).

| Dot product *s · v* | Number of vectors |
|---|---:|
| 0 | 133,204,500 |
| −8 or +8 | 95,385,600 each |
| −16 or +16 | 32,788,800 each |
| −24 or +24 | 4,147,200 each |
| −32 or +32 | 93,150 each |
| Every other integer | 0 |

The nine layers add up to 398,034,000. To count them, first fix a length-64 vector and count the shortest vectors that meet it at each dot product. A symmetry can take that length-64 vector to (8, 0, …), where the dot product is eight times the first coordinate. All 48 signed coordinate axes give the same count. [Signed axes](../LeechNorm64Layers.lean#L78).

The three shortest-vector shapes give the counts across those axes. A vector with two entries of magnitude 4 hits zero 44 times and each of ±32 twice. A vector with eight entries of magnitude 2 hits zero 32 times and each of ±16 eight times. An odd vector hits each of ±8 on 23 axes and each of ±24 on one. There are 1,104, 97,152 and 98,304 shortest vectors of these shapes, respectively. No other dot product occurs. [Count by shape](../LeechNorm64Layers.lean#L128).

Now fix the shortest vector instead. Count all pairs (*s*, *v*) at the chosen dot product, once for each choice of *s* and once for each choice of *v*. Symmetry makes each count independent of which vector is fixed. There are 398,034,000 choices for *v* and 196,560 for *s*, so the count for a fixed *s* is 2,025 times the count for a fixed *v*. [Counting pairs](../LeechNorm64Layers.lean#L59).

Run `lake build LeechNorm64Layers CheckAxioms`, then `lake env lean CheckAxioms.lean > axioms.txt` and `python3 .github/check_axioms.py CheckAxioms.lean axioms.txt`. The [axiom output](axioms-2026-11-20-norm64-layers.txt) and [verification record](leech-symmetry-verification-2026-11-20-norm64-layers.json) cover 1022 declarations.

## Layers for squared length 80

Fix any shortest vector *s*. This table counts the vectors *v* of squared length 80 in the playground’s integer coordinates. [Lean proof](../LeechNorm80Layers.lean#L166).

| Dot product *s · v* | Number of vectors |
|---|---:|
| 0 | 1,384,998,912 |
| −8 or +8 | 1,062,195,200 each |
| −16 or +16 | 458,086,400 each |
| −24 or +24 | 95,385,600 each |
| −32 or +32 | 6,476,800 each |
| −40 or +40 | 47,104 each |
| Every other integer | 0 |

The eleven layers add up to 4,629,381,120. All lattice dot products are multiples of 8. Both *s − v* and *s + v* are nonzero lattice vectors, so each has squared length at least 32. Their squared lengths are *112 − 2(s · v)* and *112 + 2(s · v)*. This puts *s · v* between −40 and +40. [Allowed dot products](../LeechNorm80Layers.lean#L103).

Subtracting *v* from *s* pairs three layers with ones already counted. A vector at +24 goes to a vector of squared length 64 at +8. A vector at +32 goes to squared length 48 at zero. A vector at +40 goes to squared length 32 at −8. Subtract from *s* again to get the original vector back. Negating *v* gives the same counts on the negative side. [Pairing](../LeechNorm80Layers.lean#L26) · [Counts from the earlier tables](../LeechNorm80Layers.lean#L43).

For the remaining counts, take the shortest axis (4, −4, 0, …) and write *d = v₀ − v₁*. Its dot product with *v* is *4d*. The sum of *d²* over the shell is 30,862,540,800, and the sum of *d⁴* is 569,769,984,000. These two sums and the shell total determine the counts at 0, ±8 and ±16. The moment formulas also give the earlier length-48 result. A lattice symmetry takes the reference axis to any shortest vector and preserves dot products. [Moment formulas](../LeechShellMoments.lean#L154) · [Inner counts](../LeechNorm80Layers.lean#L152) · [Change of axis](../LeechNorm80Layers.lean#L109).

Run `lake build LeechNorm80Layers CheckAxioms`, then `lake env lean CheckAxioms.lean > axioms.txt` and `python3 .github/check_axioms.py CheckAxioms.lean axioms.txt`. The [axiom output](axioms-2026-11-20-norm80-dot-layers.txt) and [verification record](leech-symmetry-verification-2026-11-20-norm80-dot-layers.json) cover 1024 declarations.

## Layers for squared length 96

Choose any shortest vector *s*. For each integer *k*, Lean counts the vectors *v* of squared length 96 with *s · v = k*. The squared length is 12 in the usual scale. [Lean theorem](../LeechNorm96Layers.lean#L67).

| Dot product *s · v* | Number of vectors |
| --- | ---: |
| 0 | 9,403,968,600 |
| −8 or +8 | 7,535,462,400 each |
| −16 or +16 | 3,771,829,800 each |
| −24 or +24 | 1,062,195,200 each |
| −32 or +32 | 133,204,500 each |
| −40 or +40 | 4,147,200 each |
| −48 or +48 | 4,600 each |
| Every other integer | 0 |
| **All layers** | **34,417,656,000** |

First count the whole shell. The Golay coordinate rules give 34,416,077,280 vectors with every entry between −8 and 7. Each remaining vector has a +8 entry. Subtract 8 there and the result is a shortest vector with a zero in that position. Adding the 8 back reverses the pairing. There are 24 positions and 65,780 choices at each, giving 1,578,720 more vectors. [Golay count](../LeechNorm96.lean#L71) · [Pairing at +8](../LeechNorm96.lean#L113) · [Shell total](../LeechNorm96.lean#L141).

All dot products are multiples of 8. Both *s − v* and *s + v* have squared length at least 32. Their squared lengths are *128 − 2(s · v)* and *128 + 2(s · v)*, so the dot product lies between −48 and +48. [Allowed dot products](../LeechNorm96Layers.lean#L26).

The map *v ↦ s − v* gives the four outer counts. It carries +24 to the +8 layer at squared length 80, +32 to the zero layer at 64, +40 to the −8 layer at 48, and +48 to the −16 layer at 32. Applying the map twice returns *v*. Negating *v* gives the count for the other sign. [Four pairings](../LeechNorm96Layers.lean#L31).

For the shortest axis (4, −4, 0, …), write *d = v₀ − v₁*. The dot product is *4d*. Across the shell, the sum of *d²* is 275,341,248,000 and the sum of *d⁴* is 6,099,867,648,000. These sums and the shell total give the counts at 0, ±8 and ±16. A lattice symmetry takes this axis to any shortest vector and preserves the dot product. [Moment formulas](../LeechShellMoments.lean#L154) · [Inner counts](../LeechNorm96Layers.lean#L53) · [Change of axis](../LeechNorm80Layers.lean#L109).

Run `lake build LeechNorm96Layers CheckAxioms`, then `lake env lean CheckAxioms.lean > axioms.txt` and `python3 .github/check_axioms.py CheckAxioms.lean axioms.txt`. The [axiom output](axioms-2026-11-20-norm96-dot-layers.txt) and [verification record](leech-symmetry-verification-2026-11-20-norm96-dot-layers.json) cover 1068 declarations.

For a separate check, run `node tests/leech-three-e8.cjs` in the playground repository. It counts the layers for (4, −4, 0, …) using the playground’s Golay words and compares them with the displayed table. Lean proves the counts for every shortest axis. [Playground test](https://github.com/NousVolition/sparkle-sand-playground/blob/main/tests/leech-three-e8.cjs).

## Verification

The [proof-branch audit](https://github.com/NousVolition/discrete-gap-inequalities-lean/actions/runs/44674594813) checked 900 declarations. The [PR build](https://github.com/NousVolition/discrete-gap-inequalities-lean/actions/runs/44674659364) and [merged-main build](https://github.com/NousVolition/discrete-gap-inequalities-lean/actions/runs/44675102913) checked 949, including later additions to main. Each reported zero nonstandard axioms and zero missing reports. [Full axiom output](axioms-2026-11-20-co0-release.txt) · [Saved verification](leech-symmetry-verification-2026-11-20-co0-release.json) · [Reproduction commands](leech-symmetry-order.md#reproduce-the-check).
