# Playground connections and proof coverage

The [Sparkle Sand Playground](https://nousvolition.github.io/sparkle-sand-playground/) supplies numerical examples for several results in the README. The numerical review below added no Lean theorem; its 552-statement inventory is historical. The current [README table](../README.md) includes the later [Leech shortest-vector proof](leech-shortest-vectors.md).

The reviewed [playground source](https://github.com/NousVolition/sparkle-sand-playground/blob/03ef852cce4ae0d2cdb2319c413b6755bcf6e593/index.html) is commit `03ef852cce4ae0d2cdb2319c413b6755bcf6e593`. The deployed HTML fetched during the review matched that source after normalizing line endings. Its normalized SHA256 is `b5eb5238b1aef886b42dc3a342540ac150aa8eb1398311afdec2a74475a40fc2`.

**Path gap proved:** [PathSix.lean](../PathSix.lean) proves that the gap is `2 − √3`, including a nonzero equality case and rational bounds that justify the rounded display `0.268`. It also proves that literal `0.268` is too large to serve as a universal lower-bound coefficient. These are Lean proofs; they do not certify JavaScript floating-point execution or the browser's heat trajectories.

**Cube display fixed:** [playground commit `44ed9d0`](https://github.com/NousVolition/sparkle-sand-playground/commit/44ed9d089e5d942c82304dd8ee552bcce3c9aa41) makes Trilogy use `h(m)` for the maximum and optimality labels, while showing the logarithmic upper bound separately. Its [regression check](https://github.com/NousVolition/sparkle-sand-playground/blob/44ed9d089e5d942c82304dd8ee552bcce3c9aa41/tests/trilogy-cube.cjs) passes for all 65,808 subsets of the supported 2D, 3D and 4D cubes, including `{0,1,2}`. These JavaScript checks add no Lean theorem. The original evidence below remains pinned to `03ef852`.

The checks below execute selected numerical functions from that published HTML without opening a browser or rendering the pages. Live controls were not exercised; the review covers source code and computations.

## What connects to the proved results

| Playground | Connection | Coverage limit |
| --- | --- | --- |
| [Trilogy, entry 15](https://nousvolition.github.io/sparkle-sand-playground/#trilogy) | Path and cycle inequalities, cube edges and cuts, and a cycle heat update | `PathSix.lean` now proves the six-point path gap and its display rounding. Trilogy's corrected cube display uses the exact maximum separately from the logarithmic upper bound. Browser execution is not Lean-certified. |
| [Unit Distances, entry 32](https://nousvolition.github.io/sparkle-sand-playground/#unit-distances) | Centers the x or y coordinates of a direction ring and evaluates the two sides of `CycleWirtinger.wirtinger` | The general bound is proved. Grid pair-counting claims and the page's claim that only four-direction rings attain equality have not been formalized here. |
| [Cipher Inspector, entry 33](https://nousvolition.github.io/sparkle-sand-playground/#cipher) | Centers a time window, wraps it as a cycle, and computes `W = R / (2 - 2 cos(2π/n))` | The theorem gives `W ≥ 1` for nonconstant exact real data. It does not establish correct plaintext, convergence, uniqueness, or the heuristic stall threshold. |
| [Leech, entry 24](https://nousvolition.github.io/sparkle-sand-playground/#leech) | Builds its displayed vectors using an extended binary Golay code | The Lean lattice, its minimum squared length and its 196,560 shortest vectors are now proved. The browser's modulo-23 generator still differs from the modulo-11 systematic generator in `GolayMatrixDistance.lean`; their equivalence up to a coordinate permutation remains unproved. |

The table links are illustrations or applications of the mathematics. No formal equivalence between the browser implementation and a Lean definition has been established.

## Two display claims in the reviewed revision

**The path gap.** Trilogy displays `0.268` for its six-point path. `DiscretePoincare.poincare` proves the explicit lower bound `2 / (n(n-1))`, which is `1/15 ≈ 0.0666667` at six points. The file explicitly says its constant is not sharp, so that earlier proof did not cover the displayed gap. The later `PathSix` proof establishes the constant and its rounding, as described above.

**The cube maximum.** At the reviewed revision, Trilogy labeled `(m/2) log₂(m)` as the theoretical maximum and called a set sub-optimal when it fell below that value. This is the logarithmic upper bound from `Isoperimetric.lean`. `EdgeOptimal.lean` proves the exact maximum `h(m)`, the sum of the popcounts of the integers `0,…,m-1`.

For three vertices `{0,1,2}` of the 3-cube, that revision's own counting code gives two internal edges and five boundary edges. Its displayed upper bound is `2.377443751081734`, so its status logic reports a shortfall of about `0.38`. But `h(3)=2`: the selected set is optimal. An independent enumeration of all **56 three-vertex sets** confirms that the maximum is two. The follow-up linked above corrects the display and labels this set optimal.

## Bounded computation checks

The [reproduction script](../scripts/check_playground_connections.cjs) pins the HTML hash and extracts only the relevant calculation functions. The [saved output](playground-check.json) records:

- The cube example above and all 56 three-vertex sets.
- Trilogy's six-point cosine heat update at speeds 1, 4 and 10: steps `0.004`, `0.016` and `0.04`, all within `RingDecay`'s proved interval `0 ≤ t ≤ 1/4`. The largest difference from the expected mode multiplier is `5.552e-17`.
- Unit Distances rings with `k = 1, 2, 5, 25, 65`, using both coordinate axes. All ten numerical comparisons satisfy the bound to the stated numerical tolerance; the first two rings reach equality to rounding.
- The cipher gauge's seven cosine fixtures at lengths `3, 4, 5, 7, 12, 60, 120`. All give `W=1` within `1e-9`. A constant window is reported as flat with an undefined ratio, rather than assigned a spurious finite value. JSON records that undefined ratio as `null`.
- A four-character cipher fixture using two symbols and decoding to `ABBA`: its JavaScript certificate passes, and a changed claimed plaintext fails. The exporter emits two Lean statements, but this review did **not** compile that export. Generated key-decoding checks are outside this project's axiom audit; even a compiled decoding identity would not prove that the key is the intended one.
- Both Golay constructions enumerate 4,096 distinct codewords with weight distribution `1 / 759 / 2576 / 759 / 1` at weights `0, 8, 12, 16, 24`. With the coordinates numbered as written in the two implementations, their sets share **four** codewords and are not identical. This does not refute equivalence under a coordinate permutation; it identifies a correspondence that has not been checked in Lean here.

All of these are external computation checks. They do not supply new hypotheses or certified floating-point error bounds to Lean, and they do not increase the proof count.

## Reproduce

Download the [pinned index.html](https://raw.githubusercontent.com/NousVolition/sparkle-sand-playground/03ef852cce4ae0d2cdb2319c413b6755bcf6e593/index.html) to a separate local file, then run from this repository with Node.js:

```sh
node scripts/check_playground_connections.cjs /path/to/index.html
```

The script uses Node's built-in libraries only. It refuses another HTML revision, checks the assertions, and prints JSON. It reads `GolayMatrixDistance.lean` from this checkout and records its normalized hash. It does not execute page event handlers, send network requests, run the cipher solver, or invoke Lean.
