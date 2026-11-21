# Discrete gap inequalities

This repository contains Lean proofs of gap inequalities and their consequences for smoothing and storage.

**Wirtinger and Riemann:** [Proofs, gap measurements and the route toward RH](docs/riemann-wirtinger.md). **16 Lean checks** cover the continuous zero-endpoint inequality, its zeta application and conditional RH implications. **Five numerical gap checks** separately passed the recorded precision, endpoint and inequality criteria. **Proving RH remains our goal:** complete zero coverage and matching critical-line counts are still unproved.

Every item below has checked Lean proofs. **Proved** refers to the formal statements with their stated hypotheses. The counts include supporting lemmas.

| Result | Proof status | Checked statements | Playground connection |
| --- | --- | ---: | --- |
| Four original packages: [Poincaré](Poincare.lean), [Wirtinger](Wirtinger.lean), [Hug gap](Gap.lean) and [hypercube edge-isoperimetric inequality](Isoperimetric.lean) | **Proved** | 47 | Path/cycle/cube: [Trilogy](https://nousvolition.github.io/sparkle-sand-playground/#trilogy). Cycle applications: [Unit Distances](https://nousvolition.github.io/sparkle-sand-playground/#unit-distances) and [Cipher](https://nousvolition.github.io/sparkle-sand-playground/#cipher). |
| [Six-point path gap](PathSix.lean) | **Proved — sharp bound, equality case and rounding** | 16 | [Trilogy](https://nousvolition.github.io/sparkle-sand-playground/#trilogy): the gap is `2 − √3`, which rounds to `0.268`. |
| [Ring decay proof](RingDecay.lean) | **Proved** | 14 | [Trilogy](https://nousvolition.github.io/sparkle-sand-playground/#trilogy): six-point cycle heat update. |
| [Ring sum and −1/12](RingSumMinusTwelfth.lean) | **Proved** | 25 | [Ring](https://nousvolition.github.io/sparkle-sand-playground/#ringsum). The bars have an exact finite sum. The scaled ring remainder and the damped staircase remainder both tend to −1/12. |
| [Vertex-isoperimetric proof](HarperSquash.lean) | **Proved — full Harper theorem** | 21 | — |
| [Polygon isoperimetric inequality](Polygon.lean) | **Proved** | 10 | — |
| [The cube's gap with Cheeger's inequality](CubeCheeger.lean) | **Proved — cube gap and Cheeger's easy direction** | 17 | [Trilogy](https://nousvolition.github.io/sparkle-sand-playground/#trilogy): cube gap and cut examples. |
| [Short bridges connecting the cycle, polygon and cube](Bridges.lean) | **Proved** | 5 | — |
| [Cartesian graph products and periodic grids](Torus.lean) | **Proved** | 53 | — |
| [The wall and the push](WallPush.lean) | **Proved — for the defined models** | 52 | — |
| [Harper stage 1: the squash lemma](Harper.lean) | **Proved — conditional lemma** | 18 | — |
| [The one-floor reading that restates the wave, patch and shape](Unify.lean) | **Proved — comparison and transfer lemmas** | 16 | — |
| [The extended binary Golay code](GolayMatrixDistance.lean) | **Proved — finite checks inside Lean's kernel** | 5 | [Leech](https://nousvolition.github.io/sparkle-sand-playground/#leech): the modulo-23 generator now has a [proved coordinate correspondence](docs/playground-golay.md). |
| [Edge-optimal sets of the hypercube](EdgeOptimal.lean) | **Proved** | 25 | [Trilogy](https://nousvolition.github.io/sparkle-sand-playground/#trilogy): exact cube maximum and optimality labels, with the logarithmic upper bound shown separately. |
| [The E₈ plumbing matrix](E8PlumbingBridge.lean) | **Proved** | 8 | — |
| [Stick placement and plumbing cost](PlumbingStick.lean) | **Proved** | 15 | The determinant by attachment site, the cost floor for one E₈ plumbing, and a negative-cost assignment for every single joint between two copies. |
| [Shares and cost for a row with one stick](PlumbingHelp.lean) | **Proved** | 12 | The general determinant, the three-arm criterion, and the seven-piece positivity classification. The Hug reading is a comparison. |
| [The E₈ cost mirror](E8CostMirror.lean) | **Proved** | 1 | — |
| The gap toy's mirror in [rational](GapMirror.lean) and [real-time](GapMirrorCalculus.lean) forms | **Proved — for the explicit scalar model** | 31 | — |
| The [exact clock](GapMirrorBridge.lean) and [even-ring reflection](RingGapBridge.lean) bridges | **Proved — with different motion scopes; see below** | 47 | — |
| [The four-dot map preserving both motion and reflection](FourDotGapBridge.lean) | **Proved — for the specified four-dot family** | 26 | — |
| The two-wave heat-to-gap maps for [continuous flow](TwoWaveGapBridge.lean) and [the exact discrete step](TwoWaveDiscreteGapBridge.lean) | **Proved — under the stated mode and domain conditions** | 95 | — |
| [An amplitude map preserving motion and the actual ring flip](TwoWaveFlipBridge.lean) | **Proved — for the specified construction** | 60 | — |
| [A same-sign obstruction for global amplitude readouts](TwoWaveReadoutObstruction.lean) | **Proved — for unequal rates and the stated global identities** | 7 | — |
| [The Golay-to-Leech counting bridge](GolayLeechBridge.lean) | **Proved — tied to the proved Golay counts** | 9 | [Leech](https://nousvolition.github.io/sparkle-sand-playground/#leech): the 196,560 shortest-vector count. |
| [The Leech lattice and its smallest length](LeechLattice.lean) | **Proved — definition, closure and smallest squared length 32** | 43 | [Leech](https://nousvolition.github.io/sparkle-sand-playground/#leech): the same lattice conditions hold in the playground code’s coordinates by a proved permutation. |
| [The Leech lattice's shortest vectors](docs/leech-shortest-vectors.md) | **Proved — three disjoint shapes and 196,560 shortest vectors** | 50 | [Leech](https://nousvolition.github.io/sparkle-sand-playground/#leech): the classification and count transfer to the playground code’s coordinates. |
| [The playground’s Golay generator](docs/playground-golay.md) | **Proved — coordinate correspondence and transfer of the Leech results** | 28 | [Leech](https://nousvolition.github.io/sparkle-sand-playground/#leech): 4,096 codewords and 196,560 shortest vectors in the corresponding formal model; JavaScript output checked separately. |
| [A basis of the Leech lattice and unimodularity](LeechBasis.lean) | **Proved — explicit basis spans the lattice, determinant 8¹², unimodular and even** | 29 | [Leech](https://nousvolition.github.io/sparkle-sand-playground/#leech): the lattice's volume, for the Lean lattice. |
| [Three E₈ lattices glued into the Leech lattice](docs/three-e8.md) | **Proved — equality of lattices and 4,096 distinct gluing shifts** | 32 | [Leech](https://nousvolition.github.io/sparkle-sand-playground/#leech): three linked E₈ views; minimum, count and volume reuse the existing proofs. Browser calculations are checked separately. |
| [Leech symmetry foundations and the standard frame stabilizer](docs/leech-symmetry.md) | **Proved — faithful finite action, 4,096 sign changes and frame stabilizer** | 52 | No new browser claim. |
| [Leech symmetry milestones 1–3](docs/leech-symmetry.md) | **Proved — code reorderings, reordering-group size and a symmetry moving the axes** | 35 | [Leech](https://nousvolition.github.io/sparkle-sand-playground/#leech): named proof links. The reordering group has 244,823,040 elements. |
| [Leech symmetry milestones 4–5](docs/leech-symmetry-order.md) | **Proved** | 44 | [Every lattice vector of squared length 64 is reachable](ConwayTransitivity.lean#L108). For the Leech lattice with the origin fixed, the full symmetry group has order 8,315,553,613,086,720,000, with explicit generators, proved in Lean. [Order](ConwayOrder.lean#L29) · [Generators](ConwayGenerators.lean#L21). |
| [Leech coordinate frames](LeechCoordinateFrames.lean#L129) | **Proved** | 3 | There are 8,292,375 unordered sets of 48 squared-length-64 lattice vectors congruent modulo twice the lattice. [Frame definition](LeechCoordinateFrames.lean#L16) · [Proof walkthrough](docs/leech-symmetry.md#coordinate-frames). |
| [Leech vectors of squared length 48](LeechNorm48.lean#L24) | **Proved** | 5 | The Golay residue words give 8,384,512 even-coordinate vectors and 8,388,608 odd-coordinate vectors, for a total of 16,773,120. [How the count works](docs/leech-symmetry.md#vectors-of-squared-length-48). |
| [Opposite pairs at squared length 48](LeechNorm48Pairs.lean#L25) | **Proved** | 3 | Pairing each of the 16,773,120 vectors with its negative gives 8,386,560 pairs. |
| [Leech vectors of squared length 64](LeechCoordinateFrames.lean#L151) | **Proved** | 2 | Each vector belongs to [one coordinate frame](LeechCoordinateFrames.lean#L140). The 8,292,375 frames have 48 members apiece, giving 398,034,000 vectors. |
| [Opposite pairs at squared lengths 32 and 64](docs/leech-symmetry.md#opposite-pairs-at-squared-lengths-32-and-64) | **Proved** | 5 | Pairing each vector with its negative gives [98,280 pairs at squared length 32](LeechShellPairs.lean#L11) and [199,017,000 pairs at squared length 64](LeechShellPairs.lean#L19). |
| [Leech vectors of squared length 80](docs/leech-symmetry.md#vectors-of-squared-length-80) | **Proved** | 9 | The [4,629,381,120 vectors](LeechNorm80.lean#L88) form [2,314,690,560 opposite pairs](LeechNorm80.lean#L109). |
| [Layers along a shortest vector](docs/leech-symmetry.md#layers-along-a-shortest-vector) | **Proved** | 11 | [93,150 shortest vectors](LeechLayers.lean#L18) are perpendicular to any chosen shortest vector in the playground coordinates. [Dot products of +24 and −24 cannot occur](LeechLayers.lean#L27). The [−8](LeechLayers.lean#L211) and [+8](LeechLayers.lean#L206) layers each have 47,104 vectors. The [−16](LeechLayers.lean#L221) and [+16](LeechLayers.lean#L216) layers each have 4,600. The [+32 layer](LeechLayers.lean#L233) contains only the chosen vector. The [−32 layer](LeechLayers.lean#L246) contains only its negative. The [full table](LeechLayers.lean#L304) gives zero for every other integer dot product. |
| [Layers for squared length 48](docs/leech-symmetry.md#layers-for-squared-length-48) | **Proved** | 3 | For any shortest axis, the [layer table](LeechLayers.lean#L446) counts all 16,773,120 vectors of squared length 48. The dot products are 0, ±8, ±16 and ±24. Every other integer has count zero. |
| [Layers for squared length 64](docs/leech-symmetry.md#layers-for-squared-length-64) | **Proved** | 1 | For any shortest vector *s*, the [layer table](LeechNorm64Layers.lean#L159) counts all 398,034,000 vectors of squared length 64 by their dot product with *s*. The occupied layers are 0, ±8, ±16, ±24 and ±32. Every other integer has count zero. |
| [Layers for squared length 80](docs/leech-symmetry.md#layers-for-squared-length-80) | **Proved** | 2 | For any shortest vector *s*, the [layer table](LeechNorm80Layers.lean#L166) counts all 4,629,381,120 vectors of squared length 80. The dot products are 0, ±8, ±16, ±24, ±32 and ±40. Every other integer has count zero. |
| [Layers for squared length 96](docs/leech-symmetry.md#layers-for-squared-length-96) | **Proved** | 10 | There are [34,417,656,000 vectors](LeechNorm96.lean#L141). For any shortest vector *s*, the [layer table](LeechNorm96Layers.lean#L67) gives the count at 0, ±8, ±16, ±24, ±32, ±40 and ±48. Every other integer has count zero. |
| [Layers for squared length 112](docs/leech-symmetry.md#layers-for-squared-length-112) | **Proved** | 9 | There are [187,489,935,360 vectors](LeechNorm112.lean#L52). For any shortest vector *s*, the [layer table](LeechNorm112Layers.lean#L71) gives the count at 0, ±8, ±16, ±24, ±32, ±40 and ±48. Every other integer, including ±56, has count zero. |
| [Layers for squared length 128](docs/leech-symmetry.md#layers-for-squared-length-128) | **Proved** | 8 | There are [814,879,774,800 vectors](LeechNorm128.lean#L55). For any shortest vector *s*, the [layer table](LeechNorm128Layers.lean#L75) counts every multiple of eight from −64 to +64. Every other integer has count zero. |
| [Layers for squared length 144](docs/leech-symmetry.md#layers-for-squared-length-144) | **Proved** | 5 | There are [2,975,551,488,000 vectors](LeechNorm144.lean#L64). For any shortest vector *s*, the [layer table](LeechNorm144Layers.lean#L96) counts every multiple of eight from −56 to +56. Every other integer has count zero. |
| [Gap-wave forcing and decay](GapWaveTail.lean) | **Proved** | 26 | Tab 9. Parts 1–3 give exact wave interactions, the box gap and single-wave decay. Part 4 analyzes the forecast that omits feedback. |
| [Light bounce and capture](LightBounceAndCapture.lean) | **Proved in the model** | 31 | Reflected and absorbed light, the super-black grain on tab 34, and capture at a fixed horizon on tabs 16, 27 and 28. |
| [The shortcut on the spaces](RamanujanGap.lean) | **Proved** | 9 | The damped bars-minus-area identity, exact cancellation, finite-limit implication and agreement with ζ(−1). These statements do not locate nontrivial zeros. |
| [Reading both sides of a complex zero](GapCrossing.lean) | **Proved conditionally** | 6 | With an exact zero and a strictly increasing real component, the signs differ across it and the sizes are positive. A real-part sign change alone need not be a complex zero. |
| [Continuous Wirtinger and Riemann zero gaps](docs/riemann-wirtinger.md) | **Proved under the stated hypotheses; RH remains open** | 16 | Real and complex zero-endpoint bounds, zeta on vertical lines, and a conditional counting route toward RH. Five numerical gap checks are reported separately. |
| **Total** | | **1112** | Includes supporting lemmas and the lattice construction. |

The playground links are numerical illustrations and applications. The [six-point path proof](docs/path-six-gap.md) gives the gap `2 − √3`, which Trilogy displays as `0.268`; the rounded decimal is slightly too large to use as a lower bound. A dash means no direct example was identified in this review. The [playground comparison and reproducible checks](docs/playground-connections.md) keep browser calculations separate from Lean proofs, including the cube's exact maximum. The [Golay correspondence](docs/playground-golay.md) now connects the two code constructions.

A few scope distinctions matter:

- **Harper stage 1** proves the squash lemma assuming two results in the lower dimension: neighborhoods of initial segments are initial segments, and initial segments minimize neighborhoods. The separate `HarperSquash` package proves the full theorem.
- **The exact clock bridge** connects the rational and real-time scalar models. **The even-ring cost/size map** preserves reflection but does not preserve ordinary heat motion; the file proves a counterexample. The later four-dot and amplitude constructions prove motion and reflection together for their stated families.
- **The same-sign obstruction** assumes heat covariance for every real time and every coefficient pair, antisymmetry, and unequal rates. It requires no continuity assumption. Arbitrary readouts on restricted time or state domains are outside that theorem.

The project uses Lean `v4.34.0-rc2` and Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`. `GapMirror.lean` uses Lean core only.

[CheckAxioms.lean](CheckAxioms.lean) lists **1112 declarations**, including 25 ring-sum theorems and lemmas, 31 light-bounce and capture theorems, 12 plumbing-help theorems, 22 Cartesian-product and ring results, 15 plumbing-stick theorems, 26 gap-wave theorems, 136 symmetry, frame and Golay-reordering theorems, eight squared-length-48 counting theorems, five theorems on pairing vectors with their negatives, nine results for the length-80 count, eleven results on shortest-vector layers, three results on layers for squared length 48, one table for squared length 64, a shell moment formula and the layer table for squared length 80, the counts and layer tables for squared lengths 96, 112, 128 and 144 with their supporting results, and the 32 three-E₈ theorems. The [full axiom output](docs/axioms-2026-11-20-norm144-dot-layers.txt) covers all 1112. The [length-128 layer audit](docs/axioms-2026-11-20-norm128-dot-layers.txt) covered 1107. The [length-112 layer audit](docs/axioms-2026-11-20-norm112-dot-layers.txt) covered 1099. The [length-96 layer audit](docs/axioms-2026-11-20-norm96-dot-layers.txt) covers 1068 declarations. The six [gap-crossing results](docs/axioms-gap-crossing.txt) brought the inventory to 1074. The 16 continuous-Wirtinger and Riemann checks brought it to 1090. The new [verification guide](docs/riemann-wirtinger.md#verification) keeps the 16 proof checks separate from five numerical gap checks. The [pre-ring main audit](docs/axioms-2026-11-20-norm80-dot-layers.txt) covers 1024 declarations. The [earlier ring audit](docs/axioms-2026-11-20-ring-sum.txt) covered 1042 declarations. The ring-sum merge brought the count to 1049. The nine Ramanujan-gap results brought it to 1058. The [length-64 layer audit](docs/axioms-2026-11-20-norm64-layers.txt) covered 1022. The [length-48 layer audit](docs/axioms-2026-11-20-norm48-layers.txt) covered 1021. The [shortest-vector layer table audit](docs/axioms-2026-11-20-layer-table.txt) covered 1018. The [endpoint audit](docs/axioms-2026-11-20-end-layers.txt) covered 1017. The [signed-layer audit](docs/axioms-2026-11-20-signed-layers.txt) covered 1013. The [light-bounce and capture audit](docs/axioms-2026-11-20-light-bounce-and-capture.txt) covered 1009. The [length-80 audit](docs/axioms-2026-11-20-norm80-layers.txt) covered 978. GitHub checked [900 declarations on the proof branch](https://github.com/NousVolition/discrete-gap-inequalities-lean/actions/runs/44674594813) and [all 949 on merged main](https://github.com/NousVolition/discrete-gap-inequalities-lean/actions/runs/44675102913). The [earlier plumbing-help audit](docs/axioms-2026-11-20-plumbing-help.txt) covered 905. The [Cartesian-product verification](docs/leech-symmetry-verification-2026-11-20-products-current-main.json) records the previous 893. The [earlier product-and-gap-wave audit](docs/axioms-2026-11-20-products-and-gap-wave.txt) covered 791, and the [earlier product audit](docs/axioms-2026-11-20-cartesian-products.txt) covered 765. The [earlier symmetry verification](docs/leech-symmetry-verification-2026-11-20-gap-wave-merge.json) retains the 856-declaration audit. The [earlier publication verification](docs/leech-symmetry-verification-2026-11-20-publication.json) is preserved. The [GitHub build and full axiom audit](https://github.com/NousVolition/discrete-gap-inequalities-lean/actions/runs/44662521061) passed with **830 declarations checked, 0 nonstandard, 0 missing** for the earlier milestone revision. The merged inventory adds all 26 gap-wave entries from main; GitHub checks this combined revision separately. The [proof-stage verification](docs/leech-symmetry-verification-2026-11-20-m123.json) is preserved. The [five symmetry milestones](docs/leech-symmetry-order.md) include the generators and full group order. The [three-E₈ verification record](docs/three-e8-verification.json) records the local compilation and full axiom audit; the [integer replay](docs/three-e8-replay.json) is separate browser-source evidence. The [comment wording check](docs/lean-comment-verification-2026-11-20.json) confirms that the later prose edit changes no Lean code; [source hashes for that edit](docs/three-e8-verification-2026-11-20-comments.json) are recorded separately. The new construction reuses the 28 correspondence and transfer theorems and the 29 Leech basis theorems. The [GitHub build for `14518ce`](https://github.com/NousVolition/discrete-gap-inequalities-lean/actions/runs/44511224784) passed all 711 axiom checks. The [Golay correspondence verification](docs/playground-golay-verification.json) preserves its historical 682-declaration audit at `93bd836`, with source hashes and the scope of reused build artifacts. The earlier [Leech verification record](docs/leech-shortest-verification.json) retains its historical 654-declaration audit. The earlier [six-point path record](docs/path-six-verification.json) retains its historical 551-statement audit. These records are kept unchanged. Dated records from November 19, 2026 ([Leech](docs/leech-shortest-verification-2026-11-19.json), [Golay correspondence](docs/playground-golay-verification-2026-11-19.json), [axiom output](docs/axioms-2026-11-19.txt)) re-check the Leech and Golay correspondence evidence against the then-current 711-declaration audit, and the [November 20 Leech](docs/leech-shortest-verification-2026-11-20-three-e8.json) and [Golay](docs/playground-golay-verification-2026-11-20-three-e8.json) records extend that evidence to the 743-declaration audit. `scripts/check_leech_evidence.py` and `scripts/check_playground_evidence.py` compare the checkout against the newest dated record. The [GitHub workflow](https://github.com/NousVolition/discrete-gap-inequalities-lean/actions/workflows/lean.yml) runs the Lean build and axiom audit on every push. The [audit checker](.github/check_axioms.py) accepts only `propext`, `Classical.choice` and `Quot.sound`; it rejects `sorryAx`, other axioms and missing reports.

Author: NousVolition.

## Discrete Poincaré

**Statement.** For `f : ℕ → ℝ` and a path of `n` points with `∑_{i<n} f i = 0`,

```
2 * ∑_{i<n} f(i)^2  ≤  n (n-1) * ∑_{k<n-1} (f(k+1) - f(k))^2
```

Equivalently, the Dirichlet form of the path Laplacian is at least `2 / (n(n-1))` times the squared norm on mean-zero data.

The original note is kept, wording unchanged, at [docs/discrete-poincare.md](docs/discrete-poincare.md), and is included below.

## Six-point path gap

For six real values with zero sum, [PathSix.lean](PathSix.lean) proves

```text
(2 − √3) * ∑_{i=0}^{5} f(i)² ≤ ∑_{i=0}^{4} (f(i+1) − f(i))².
```

The nonzero vector `(1, √3−1, 2−√3, √3−2, 1−√3, −1)` attains equality, so the coefficient cannot be increased. Lean also proves `0.2679491924 < 2−√3 < 0.2679491925`: Trilogy's `0.268` is correct to three decimals, but is not itself a valid lower-bound coefficient. See the [proof explanation and reproduction instructions](docs/path-six-gap.md).

## Cycle Wirtinger

**Theorem (`wirtinger`).** For `f : ZMod n → ℝ` with `∑ j, f j = 0`,

```
(2 - 2 cos (2π/n)) * ∑ j, f j ^ 2  ≤  ∑ j, (f (j + 1) - f j) ^ 2
```

The original note is kept, wording unchanged, at [docs/cycle-wirtinger.md](docs/cycle-wirtinger.md), and is included below.

## The Hug gap

**`finite_iff_gap`:** a store that adds up a steady positive input stays finite for all time exactly when it lets go at a rate above zero.

The original note is kept, wording unchanged, at [docs/hug-gap.md](docs/hug-gap.md), and is included below.

## The gap toy's mirror

[GapMirror.lean](GapMirror.lean), beside `Gap.lean`, contains 19 theorems over rational numbers for the scalar toy with rate `u * u - g * u` and no spatial spreading. It uses Lean core only. The supplied `GapMirror_1.lean` is retained unchanged under this module name.

The algebraic evolution is

```
step g r u = g * u / (r * g - (r - 1) * u)
```

The coordinate `z = 1 - g / u` is multiplied by `r` (`z_step`). Reversing its sign pairs an above-gap starting height `A` with `mirror g A = g * A / (2 * A - g)`. The pairing commutes with evolution where the stated denominators are nonzero (`mirror_step`), and the reciprocal heights obey `mirror_sum`.

For `0 < g < A`, `blows_up` proves that every height `A + M`, with `M > 0`, is attained at a rational factor `1 ≤ r < A / (A - g)`. At the limiting factor, the below-gap mirror is `g / 2` (`mirror_time`). For `0 < u < g` and `r ≥ 1`, the below-gap solution stays positive, does not exceed its starting height, and satisfies the explicit bound `step g r u * (r * (g - u)) ≤ g * u`.

**Scope.** This module is an algebraic growth-factor model. The real clock and blow-up limit are proved in `GapMirrorCalculus.lean`, and their exact connection to this model through `r = exp(g * t)` is proved in `GapMirrorBridge.lean` below. Lean's rational division is total: division by zero evaluates to zero, not infinity. The value of `step` at its pole must therefore not be interpreted as a physical height; `blows_up` concerns unbounded heights strictly before that pole. This nonlinear toy is separate from the linear store in `Gap.lean`.

## The mirror in real clock time

[GapMirrorCalculus.lean](GapMirrorCalculus.lean) is the checked calculus companion, with 12 theorems over real numbers. It uses namespace `GapMirrorCalculus` so it can be imported together with the rational `GapMirror` module.

Its explicit scalar solution is `bump g A t = g / (1 - (1 - g / A) * exp(g * t))`. It starts at `A` (`bump_zero`) and satisfies `u' = u² - g * u` wherever its denominator is nonzero (`bump_solves`). The transformed coordinate obeys `z' = g * z` (`z_grows`).

For `0 < A < g`, the bump tends to zero as time tends to infinity (`fades`). For `0 < g < A`, the time `T = log(A / (A - g)) / g` is positive (`blowTime_pos`), the denominator stays positive before `T` (`finite_before`), and the bump tends to positive infinity as `t` approaches `T` from below (`blows_up`). At that time the below-gap mirror is exactly `g / 2` (`mirror_time`); `mirror_sum` proves the reciprocal-height identity.

The file retains all 11 theorem statements and four definitions from the supplied calculus draft, with a separate namespace, focused imports, and an additional positive-time theorem. Its axiom reports are included in `CheckAxioms.lean` and checked by CI. The blow-up result is a left-hand limit: total real division still assigns zero to the displayed formula at the pole. These are statements about an explicit scalar solution with no spatial spreading; a general uniqueness theorem is not included.

## From growth factors to real clock time

[GapMirrorBridge.lean](GapMirrorBridge.lean) proves 23 statements connecting the rational module with the real calculus module. Its `realStep` uses the same rational expression over the reals; `cast_step` proves exact agreement on rational inputs. For `A != 0`, `real_step_at_time` proves

```
realStep g (exp (g * t)) A = GapMirrorCalculus.bump g A t
```

For `0 < g < A` and `0 <= t < T`, where `T = log(A / (A - g)) / g`, `same_motion_before_blowup` also proves positivity of the algebraic denominator and the factor bounds `1 <= exp(g * t) < A / (A - g)`. Each rational factor in that forward range has exact real clock `log(r) / g` (`rational_step_at_clock`); no assumption that arbitrary real exponentials are rational is needed.

`both_in_future` retains the shared positive-time event: the upper bump diverges from the left while its mirror equals `g / 2`. That time is an endpoint only for the upper bump: `mirror_continues` proves the lower partner remains regular, keeps decreasing, and tends to zero. The remaining clock lemmas distinguish this blow-up from a lower bump's half-height crossing, whose time can be positive, zero, or negative.

## The even ring and the gap mirror: a proved algebraic connection

[RingGapBridge.lean](RingGapBridge.lean) proves 24 statements for a nonempty even ring. With `size f = sum_j f(j)^2` and `cost f = sum_j (f(j+1) - f(j))^2`, the alternating flip is `flip f j = (-1)^j.val * f j`. The wraparound edge is included. `size_flip` and `cost_flip` prove

```
size (flip f) = size f
cost (flip f) = 4 * size f - cost f
```

The new observable `height g f = 2 * g * size f / cost f` assigns a bump height to a pattern. For `g > 0`, `size f > 0`, and `0 < cost f < 4 * size f`, `height_flip` proves

```
height g (flip f) = GapMirrorCalculus.mirror g (height g f)
```

Thus flipping the ring produces exactly the mirror of its assigned bump. Equivalently, `z = 1 - g / height` equals `1 - cost / (2 * size)` and changes sign under the flip. This is a proved algebraic connection through an explicit observable. Zero and maximal cost are excluded from the finite positive pair interpretation.

**Motion.** This map preserves reflection but does not preserve the usual ring heat evolution. `height_scale` proves that nonzero rescaling leaves the assigned height unchanged. The checked six-point wave `(1, 1/2, -1/2, -1, -1/2, 1/2)` has mean zero, size and cost both 3, and discrete Laplacian `-f`. Its heat update, using exactly the defining formula of `RingDecay.heatStep`, keeps its assigned height at `2*g` for every step size other than 1, including the repository's range `0 <= t <= 1/4` (`six_wave_heat_height`). The gap rule at that height has positive rate `2*g^2` (`six_wave_gap_rate`). No further dynamics proof is needed for the reflection result; a claim of shared motion needs a different map or evolution rule. The amplitude map in `FourDotGapBridge.lean` below provides such a map for a four-dot family. This file checks the explicit heat-update formula without importing the full Fourier proof in `RingDecay.lean`.

## Four dots: preserving both motion and reflection

[FourDotGapBridge.lean](FourDotGapBridge.lean) proves 26 statements for the ring family `pattern a = (0, a, 0, -a)`. It retains signed amplitude and uses the existing alternating flip from `RingGapBridge`. The explicit continuous heat solution has amplitude `a(t) = a0 * exp(-2*t)`; `continuous_heat` checks the heat equation at every dot, including the periodic neighbors.

With gap `g = 2`, the readout is `U(a) = 2*a/(a-1)`. On this family it reads the amplitude directly from dot 1. For `a0 > 1` and `0 <= t < T`, where `T = log(a0)/2`, `preserves_motion_and_reflection` proves:

```
readout (flow a0 t) = GapMirrorCalculus.bump 2 (height a0) t
readout (flip (flow a0 t)) = GapMirrorCalculus.mirror 2 (readout (flow a0 t))
```

The flipped trajectory also equals the bump started from the mirrored initial height. Both readouts satisfy `u' = u^2 - 2*u` with the same real clock (`both_readouts_solve`). The upper height stays above 2 and its partner stays strictly between 1 and 2 before the pole. The identity `height_dilation` also connects the amplitude change to the existing real growth-factor formula.

`pole_eq_blowTime` identifies `T` with the gap toy's blow-up time. At `T`, the upper readout diverges from the left (`readout_blows_up`) and the flipped readout equals 1 (`flipped_at_pole`). The ring itself reaches `(0, 1, 0, -1)` continuously (`ring_regular_at_pole`). Thus the singularity is in the readout, while the ring heat trajectory remains regular.

This is an exact correspondence on the stated family for continuous heat, with fixed gap 2. It does not identify an Euler step with continuous heat at the same duration, nor all ring patterns with scalar bumps. The map is different from the amplitude-independent cost/size map in `RingGapBridge.lean`. The finite-height interpretation excludes the pole; Lean's totalized division value at the pole is not an infinite height.

## Two waves: the cost/size map and the signed pole

[TwoWaveGapBridge.lean](TwoWaveGapBridge.lean) proves 55 statements for orthogonal real eigenmodes on a nonempty periodic ring, with eigenvalues `ls < lr`. For initial coefficients `a`, `b` and modes `v`, `w`, their initial squared sizes are `P0 = a^2 * size v` and `Q0 = b^2 * size w`. The explicit continuous heat trajectory uses coefficients `a * exp(-ls*t)` and `b * exp(-lr*t)`.

The file proves the ring's integration-by-parts identity (`cost_eq_neg_dot_heat`), then its two-mode size and cost formulas (`flow_size`, `flow_cost`). `continuous_heat` verifies the heat equation at every coordinate. Thus `ring_readout` connects the actual pattern to Claude's formula:

```
g = 2 * (lr - ls)
P(t) = P0 * exp(-2*ls*t)
Q(t) = Q0 * exp(-2*lr*t)
u(t) = 2 * (cost/size - ls) = g * Q(t) / (P(t) + Q(t))
s(t) = g * Q(t) / (Q(t) - P(t))
```

For positive `P0` and `Q0`, the ordinary readout `u` stays between 0 and `g` and tends to zero. The signed readout `s` is exactly the gap toy's mirror of `u` (`ring_signed_mirror`). It comes from replacing the sum of the modal quadratic forms by their difference (`signed_ratio_map`); it is not the ordinary cost/size of a real pattern. The file proves exact equality with `GapMirrorCalculus.bump` using the same real clock, and the ODE `u' = u^2 - g*u` for both readouts wherever their denominators are nonzero (`ordinary_solves`, `signed_solves_regular`).

The positive squared sizes cross at exactly one real time, `T = log(Q0/P0)/g` (`energies_equal_iff`). The future-pole classification is checked explicitly:

| Initial squared sizes | Signed denominator |
|---|---|
| `Q0 > P0` | Reaches zero at the positive time `T`; the signed readout tends to positive infinity from the left. |
| `Q0 = P0` | Is already zero at tagging, `T = 0`. |
| `Q0 < P0` | Has no zero at any future time; the crossing time is negative. |

At a future pole, the ordinary readout equals `g/2`, while every ring coordinate remains continuous (`ring_signed_event`). A flat/alternating four-dot example proves that the eigenmode and orthogonality assumptions are realizable: its initial squared sizes are 4 and 16, its gap is 8, and its ordinary readout is 4 at the signed pole (`concrete_signed_event`). Pure rough and pure smooth readouts are respectively `g` and 0. `flat_gap` proves that a flat mode paired with eigenvalue `lr` gives scalar gap `2*lr`.

The generic ring theorems state their eigenmode and orthogonality hypotheses explicitly. The signed mirror here is a readout of the specified decomposition, not the alternating ring flip. The clock is continuous heat; no equivalence with an Euler step of the same duration is asserted. Blow-up is a one-sided limit of the signed readout, while the heat trajectory remains regular; Lean's totalized division value at the pole is not a finite-height continuation.

## Exact two-wave map for discrete heat

`TwoWaveDiscreteGapBridge.lean` proves the map for the repository's actual `RingDecay.heatStep τ`, including every integer iterate. There are 40 checked theorems. For orthogonal eigenmodes with eigenvalues `λs < λr`, initial squared sizes `P,Q > 0`, and gap `g = 2(λr − λs)`, set

```
cs = 1 − τ λs                 cr = 1 − τ λr
r  = cs² / cr²                Δ = log(r) / g
Pk = cs^(2k) P                Qk = cr^(2k) Q
```

The proof derives these mode sizes from actual heat-step iteration. When both multipliers are nonzero, the ordinary readout `u = 2(cost/size − λs) = g Q/(P+Q)` satisfies

```
u(heatStep τ f) = realStep g r (u f)
u((heatStep τ)^k f) = bump g (u f) (k Δ).
```

Thus the exact toy clock is `k log(r)/g`; the heat clock is `k τ`. For example, the flat and alternating four-dot modes with `τ = 1/8` have `g = 8`, `r = 4`, and `Δ = log(4)/8`. For positive steps with `cr > 0`, the theorem proves `r > 1` and `Δ > 0`. The strict stable heat range `0 ≤ τ < 1/4` guarantees `cr > 0` when `λr ≤ 4`; a zero step has `r = 1` and `Δ = 0`.

The signed readout is `s_k = g Q/(Q − P r^k)`, the gap mirror of the ordinary readout at each sample. For `0 < P < Q`, regular evolution before its pole is exactly `P r^k < Q`. Its toy pole time is `log(Q/P)/g`, and its real-valued step index is `log(Q/P)/log(r)`. A discrete sample hits the pole precisely when `P r^k = Q`. The checked four-dot examples distinguish landing on the pole (`τ = 1/8`, `P = 4`, `Q = 16`) from skipping it (`τ = 3/16`): in the latter, the signed values jump from `32/3` to `−8/3`, the toy pole lies strictly between samples 0 and 1, and every integer sample has a nonzero denominator. The ordinary readout remains finite at the sampled pole and equals `g/2`.

If `cr = 0`, one actual heat step removes the rough mode. The finite-factor and finite-clock theorems explicitly exclude that endpoint. Algebraic identities use Lean's totalized division; the strict pre-pole statements establish the domain of regular motion. Reflection here is `GapMirrorCalculus.mirror` between the ordinary and signed readouts.

## Two waves preserving motion and the actual ring flip

`TwoWaveFlipBridge.lean` gives a new amplitude-dependent construction, with 60 checked theorems. Choose nonzero orthogonal real eigenmodes `v,w` on a nonempty even ring, with `w = RingGapBridge.flip v`. The proof derives `λ1 + λ2 = 4` from the actual heat generator and spatial flip. Orthogonal projection recovers the signed coefficients `a,b` from the ring pattern `f = a v + b w`.

Define

```
A(a,b) = (a |b| − b |a|) / 2
U(f)   = 4 A(a,b) / (A(a,b) − 1).
```

The actual ring flip exchanges `a,b`, so it negates `A` and gives exactly `GapMirrorCalculus.mirror 4 (U f)`. Continuous heat multiplies `A` by `exp(−4t)`. Consequently `U` follows the gap equation with toy gap `4` and the same continuous clock. `paired_motion_and_flip` proves both correspondences on the forward interval before the pole, including the heat solution starting from the flipped initial pattern. Heat and flip can give different ring patterns when performed in different orders; this readout gives them the same value.

The checked conditions and limits are explicit:

| Question | Exact statement for this construction |
|---|---|
| When is the readout active? | Away from its pole, `U ≠ 0` exactly when `a b < 0`. Same-sign coefficients and missing modes give zero. |
| When are both mirrored heights finite? | Their denominators are nonzero exactly when `A ≠ 1` and `A ≠ −1`. |
| When are both strictly positive? | Exactly when `abs A > 1`. Choose the upper member by taking `A > 1`. |
| What is the forward upper interval? | For initial `A0 > 1`, `0 ≤ t < log(A0)/4`; the upper height exceeds `4` and its mirror lies between `2` and `4`. |
| Why toy gap 4? | For `height g A = g A/(A−1)` with a nonzero regular amplitude decaying at rate `σ`, the same-clock gap ODE holds if and only if `g = σ`. The paired product has `σ = λ1+λ2 = 4`. |
| Would a nonzero linear amplitude readout work? | Reflection and same-clock decay require coefficients `d = −c` and `λ1 = λ2 = g`; for flip-paired ring modes this is exactly `λ1 = λ2 = g = 2`. |

The discrete results use the repository's actual `RingDecay.heatStep` and all its integer iterates. With positive multipliers `c1 = 1−τλ1` and `c2 = 1−τλ2`, the exact factor and clock below apply. For `A0 ≠ 0` and `A0 ≠ 1`, the readout matches the explicit bump at that clock:

```
r = 1 / (c1 c2)               Δ = log(r) / 4
A_k = (c1 c2)^k A0            U_k = bump 4 U0 (k Δ).
```

On an active pair, a positive amplitude scaling exists if and only if both multipliers are positive (`positive_step_scale_iff`). For a positive heat step and flip-paired rates this gives `r > 1` and `Δ > 0`. The strict sampled condition `r^k < A0` gives the finite upper/mirror correspondence; `iterate_flip_readout` also checks agreement between heat after the initial flip and flipping after heat. Algebraic identities use Lean's totalized division; the finite-pair statements specify the regular domain.

The concrete four-dot example uses the flat and alternating modes with coefficients `2` and `−1`. Its initial heights are `8` and `8/3`, and its continuous pole time is `log(2)/4`. An actual heat step `τ = 1/16` has `r = 4/3`, `Δ = log(4/3)/4`, and heights `12` and `12/5`.

This map retains signed amplitudes and depends on the chosen mode normalization. Its toy gap and discrete factor differ from the earlier cost/size two-wave map, which remains unchanged. The classification covers this construction and the stated linear class; it does not claim that these exhaust all possible nonlinear maps.

## Same-sign obstruction for global amplitude readouts

`TwoWaveReadoutObstruction.lean` proves that global heat covariance and antisymmetry force every real-valued amplitude readout `W` to vanish on same-sign pairs when the real rates `l` and `m` differ. The two identities are:

```
∀ a b t, W (a * exp(-l*t)) (b * exp(-m*t)) = exp(-g*t) * W a b
∀ a b,   W b a = -W a b.
```

The conclusion is `W a b = 0` whenever `a*b > 0`, covering both strictly positive and strictly negative pairs. No continuity, smoothness, measurability, linearity, or positivity of the rates is assumed. The motion hypothesis quantifies over every real time and every real pair of coefficients.

At `t* = log(b/a)/(m-l)`, the two evolved coefficients agree. Antisymmetry forces `W` to vanish on that diagonal; the nonzero exponential motion factor then forces its original value to vanish. This proves that same-sign collapse is forced throughout the stated global class, beyond the particular oriented-product map. It does not classify arbitrary readouts defined only on restricted time or state domains. The equal-rate example `W(a,b) = a-b`, with `l=m=g`, shows why unequal rates are essential.

All seven theorems, including the meeting-time identity, both sign cases, and the equal-rate counterexample, are included in `CheckAxioms.lean`.

### Credits for the two-wave work

- **Codex:** mathematical proof and Lean verification.
- **Claude:** the claim that the same-sign collapse is forced, and the theorem statement.
- **NousVolition:** project direction and connecting the two conversations, carrying the question, claim, statement, and proofs between them.

## Hypercube isoperimetric inequality

**Theorem `HypercubeIso.edges_le`.** For every vertex set `s` of the `n`-cube,

```
dir s * log 2 ≤ size s * log (size s)
```

Here `size s` is the number of vertices in `s`, and `dir s` counts the ordered adjacent pairs inside `s`, which is twice the number of edges `s` spans.

The original note is kept, wording unchanged, at [docs/hypercube-isoperimetric.md](docs/hypercube-isoperimetric.md), and is included below.

This is the edge form: it counts the edges a set of corners spans. The vertex form (Harper's theorem), which counts the corners next to a set, is proved in this repo by squashing; see [Vertex-isoperimetric inequality on the hypercube (Harper's theorem)](#vertex-isoperimetric-inequality-on-the-hypercube-harpers-theorem). Its main result is `HarperVertex.harper_cube`, and its ball form is `HarperVertex.harper_ball_choose`.

## Ring decay: settling to the mean at the Wirtinger rate

**Theorem (`RingDecay.energy_iterate_le`).** For `u : ZMod n → ℝ`, one heat step with step size `t` is

```
heatStep t u j = u j + t * (u (j + 1) - 2 * u j + u (j - 1))
```

For `0 ≤ t ≤ 1/4`, the step keeps the mean (`mean_heatStep`), and after `k` steps

```
∑ j, (u_k j - mean u)^2  ≤  ((1 - t * gap n)^2)^k * ∑ j, (u j - mean u)^2
```

where `gap n = 2 - 2 cos (2π/n) = 4 sin²(π/n)` is the Wirtinger constant (`gap_eq_four_sin_sq`). For `n ≥ 2` and `0 < t ≤ 1/4`, every value goes to the mean (`iterate_tendsto_mean`). The wave `cos (2π j/n)` meets the bound with equality (`energy_heatStep_wave`), so the rate is the best possible.

**Proof.** One step multiplies the `k`-th Fourier coefficient by `1 - t (2 - 2 cos (2π k/n))` (`fourier_heatStep`). For `k ≠ 0` the Wirtinger bound puts this number between `0` and `1 - t * gap n`, and Parseval's identity turns that into the energy bound. The proof imports `Wirtinger.lean` unchanged.

**File.** `RingDecay.lean` (namespace `RingDecay`).

## Vertex-isoperimetric inequality on the hypercube (Harper's theorem)

**Theorem (`HarperVertex.harper_cube`).** Order the subsets of `Fin n` by the simplicial order: smaller sets first, and sets of the same size by the least element on which they differ. Among all families of subsets with a given number of sets, the initial segment of that size has the smallest neighborhood:

```
(nbhd univ (initSeg univ 𝒜.card)).card ≤ (nbhd univ 𝒜).card
```

The neighborhood of a family is the family together with every set that differs from one of its members in exactly one element. The ball form (`harper_ball_choose`): if `|𝒜| ≥ C(n,0) + … + C(n,r)`, then `|N(𝒜)| ≥ C(n,0) + … + C(n,r+1)`.

**Proof.** By squashing, by induction on the size of the ground set.

1. The squash in direction `i` replaces each half of the family, split by whether its sets contain `i`, by the initial segment of the same size. It keeps the size and never makes the neighborhood bigger (`card_nbhd_squash_le`).
2. The neighborhood of an initial segment is again an initial segment (`isInit_nbhd`).
3. A family squashed in every direction is an initial segment or one exceptional half-cube family, and in both cases the bound holds (`squashedAll_classify`, `card_nbhd_le_of_squashedAll`).
4. Each squash that changes the family lowers the sum of the positions of its sets (`weight_squash_lt`), so squashing stops, and Stage 3 finishes the proof (`harperAt`).

**Files.** `HarperSquash.lean` and `HarperSquash/` (`Basic`, `NbhdInit`, `Squash`, `Classify`, `Harper`; namespace `HarperVertex`).

Reference: L. H. Harper, *Optimal numberings and isoperimetric problems on graphs*, J. Combin. Theory 1 (1966).

## Polygon isoperimetric inequality

**Theorem (`PolygonIso.polygon_isoperimetric`).** A closed polygon with `n ≥ 3` vertices is a map `z : ZMod n → ℂ`. Write `area2 z` for twice the signed area, and `sides z` for the sum of the squared side lengths. Then

```
2 * tan (π/n) * area2 z  ≤  sides z
```

Equivalently, `4 tan (π/n) · area ≤ ∑ side²`. The regular polygon `z j = exp (2π i j / n)` gives equality (`polygon_sharp`).

**Proof.** This is Hurwitz's Fourier proof of the isoperimetric inequality (1901), in discrete form. It uses the same finite Fourier transform as `Wirtinger.lean`. Plancherel turns both sides into sums over frequencies, and each frequency is compared separately by the bound `tan (π/n) · sin (2π m/n) ≤ 1 − cos (2π m/n)` (`tan_bound`).

**File.** `Polygon.lean` (namespace `PolygonIso`).

## The cube's gap and Cheeger's inequality

**Theorem (`CubeCheeger.gap`).** Vertices of the `n`-cube are `Fin n → Bool`. For `f` on the cube, `energy f` sums `(f x − f y)²` over adjacent pairs (each edge counted twice), and `spread f` sums the same over all ordered pairs. Then

```
2 * spread f  ≤  2^n * energy f
```

Rewritten with the mean, this reads `∑_edges (f x − f y)² ≥ 2 · ∑ (f − mean)²`: the cube's spectral gap is `2`. The proof is by induction on `n`, cutting along the first coordinate.

**Cheeger's easy direction (`cheeger`).** Apply the gap to the indicator of a set `S`. If `|S| ≤ 2^{n−1}`, then at least `|S|` edges leave `S`, so the cut per corner is at least `gap / 2 = 1`.

**Exactness (`half_exact`).** The half-cube `{x | x 0 = true}` has `2^n` corners and exactly `2^n` edges leaving it. So the bound from the gap and the cheapest cut are equal on the cube.

**File.** `CubeCheeger.lean` (namespace `CubeCheeger`).

## Bridges between the cycle, the polygon and the cube

`Bridges.lean` ties the cycle, the polygon and the cube together.

| Result | Statement |
|---|---|
| `cycle_gap_two` | `2 − 2 cos(2π/2) = 4`: the cycle gap at length 2 |
| `cube_poincare` | for mean-zero `f` on the n-cube, `(2 − 2 cos(2π/2)) · ∑ f² ≤ energy f` |
| `cfourier_ofReal` | on real data, `PolygonIso.cfourier` is `CycleWirtinger.fourier` |
| `parseval_real_of_plancherel` | the Wirtinger Parseval identity, derived from the polygon package's Plancherel |

**What `cube_poincare` says.** The cube is a product of n single edges, and a single edge is a cycle of length 2. The cube's gap equals that edge's gap, so taking a product does not lower it. `(−1)^(x 0)` gives equality.

**Proof.** It is `CubeCheeger.gap` combined with `spread f = 2 · 2ⁿ · ∑ f²` for mean-zero `f` (`spread_of_mean_zero`).

Numerical check (outside Lean): `cycle_gap_two` is 4; `cube_poincare` held on random mean-zero functions for `n ≤ 6`, with equality at `(−1)^(x 0)`; Parseval held for `n ≤ 11`.

**File.** `Bridges.lean` (namespace `Bridges`).

## Cartesian graph products and periodic grids

`CartesianGraphProduct.boxPi_gap_sharp` proves that the sharp Poincaré gap of a nonempty finite family of finite simple graphs is the minimum of the sharp factor gaps. Each undirected edge counts once. When all factor vertex sets are nonempty, a constant works on the product exactly when it works on every factor. The empty product has one vertex and admits every real bound.

The weighted theorem `CartesianGraphProduct.pi_gap_sharp` allows nonnegative weights and edge multiplicities. Applied to rings of periods at least two, it gives the sharp gap of a periodic grid in any finite positive dimension (`RingGrid.torus_gap_sharp`).

`Torus.lean` proves the gap of the flat grid `ZMod m × ZMod n`. The grid is two rings laid across each other: each point `(i, j)` has a neighbor one step along the first ring, `(i + 1, j)`, and one step along the second ring, `(i, j + 1)`. The energy of `f` is the sum over all points of `(f(i+1, j) − f(i, j))² + (f(i, j+1) − f(i, j))²`. The ring gap is `gap k = 2 − 2 cos(2π/k) = 4 sin²(π/k)`, the same `RingDecay.gap` used in the ring decay proof.

| Result | Statement |
|---|---|
| `grid_gap` | for `f` with `∑ f = 0`, `min(gap m, gap n) · ∑ f² ≤ energy f` |
| `rowWave_sharp` | for `m ≥ 2`, `cos(2π i/m)` has sum zero and `energy = gap m · ∑ f²` |
| `colWave_sharp` | for `n ≥ 2`, `cos(2π j/n)` has sum zero and `energy = gap n · ∑ f²` |
| `grid_gap_sharp` | for `m, n ≥ 2`, some `f` with `∑ f = 0` and `f(0, 0) = 1` has `energy f = min(gap m, gap n) · ∑ f²` |

**What it says.** A flat pattern on the grid is made from waves along two lines. The grid settles no slower than its slower ring. The floor is hit by stripes: a wave along one ring, flat along the other (`rowWave`, `colWave`). A wave in each direction multiplied together settles faster than the floor; on a 7-by-4 grid, for example, one such pattern scores 2.75 against a floor of 0.75. This is the same idea as `cube_poincare` in `Bridges.lean`: the cube is made from single edges, and putting them together does not lower the gap.

**The last tab of the video ("1D to 2D Waves").** That tab draws a wave in each direction multiplied together, so it does not show the case that hits the floor. Setting one of the two waves to flat gives the exact case. The tab also pins its edges, while the grid in the proof wraps around like a ring.

**Proof.** Split `f` into its row means `c(i)` and the rest `g = f − c`. Each row of `g` has sum zero, so the cross terms vanish: `∑ f² = n ∑ c² + ∑ g²`. Steps along the second ring see only `g`, and the cycle Wirtinger inequality on each row gives at least `gap n · ∑ g²`. Steps along the first ring give at least `n ∑ (c(i+1) − c(i))²`, and the cycle Wirtinger inequality for `c` gives at least `gap m · n ∑ c²`. The equality for the waves uses `RingDecay.heatStep_wave`.

Numerical check (outside Lean): the inequality held on random mean-zero functions for several sizes from `2 × 2` to `5 × 7`, and the wave `cos(2π i/m)` gave equality with `gap m`.

### The heat flow on the grid

Write `lap f` for `4 f` minus the four neighbors (with wrap). One heat step is `f ↦ f − τ · lap f`. This route needs no two-direction wave split: it is the grid floor plus one Cauchy–Schwarz line.

| Result | Statement |
|---|---|
| `sum_heatStep` | one step keeps the sum, so the average (`mean_heatStep`) |
| `sum_mul_lap` | `∑ f · lap f = energy f` |
| `sum_sq_heatStep` | `∑ next² = ∑ f² − 2τ · energy f + τ² · ∑ (lap f)²` |
| `sum_lap_sq_le` | each point has 4 neighbors, so by Cauchy–Schwarz `∑ (lap f)² ≤ 8 · energy f` |
| `sum_sq_heatStep_le` | `∑ next² ≤ ∑ f² − 2τ(1 − 4τ) · energy f` |
| `heatStep_decay` | for `0 ≤ τ ≤ 1/4` and `∑ f = 0`, `∑ next² ≤ (1 − 2τ(1 − 4τ) · min(gap m, gap n)) · ∑ f²` |
| `heatStep_decay_eighth` | at `τ = 1/8`, each step shrinks the squared size by a factor of at least `1 − min(gap m, gap n)/8` |
| `heatStep_decay_mean` | for any data, the uneven part `f − mean f` shrinks by the same factor |
| `iterate_decay` | after `k` steps, the factor to the power `k` |
| `energy_tendsto_zero`, `iterate_tendsto_mean` | for `m, n ≥ 2` and `0 < τ < 1/4`, the uneven part goes to zero and every value settles to the mean |

The proof shows that each step shrinks the squared size by at least this factor.

**File.** `Torus.lean` (namespaces `CartesianGraphProduct` and `RingGrid`).


## The wall, the push, and the balance

`WallPush.lean` (namespace `HugWallPush`) is the wall, the push, the balance, and the clay wall.

| Result | Statement |
|---|---|
| `wall_total_zero`, `count_closes` | a wall of any thickness never changes the total of the grid; what it takes is exactly the heat it makes |
| `push_changes_total`, `balanced_push_keeps_total` | a one-way push changes the total, whatever the wall's thickness; only a push whose total is zero leaves the total alone |
| `average_fixed`, `difference_fades`, `thicker_balances_faster` | two sides joined by a wall of thickness `k`: the average never moves, the difference fades as `exp(-(2k) t)`, and a thicker wall balances faster |
| `dip_floor`, `total_viscosity_never_negative` | the response `q (1 + tanh (q/ε)) / 2` never goes below `-ε / (2e)`, so a base viscosity of at least `σ ε / (2e)` keeps the total viscosity from ever going negative |
| `freeze_keeps_total`, `freeze_gives_off` | the freeze keeps the total and gives off the difference |
| `clay_energy`, `clay_brakes_box`, `integrity_stays` | the clay's drag `−K g χ u` takes exactly `K g χ u²` as heat and brakes the whole box; the integrity step stays between 0 and 1 |

Heat here is just heat: the energy given off.

**File.** `WallPush.lean` (namespace `HugWallPush`).

## Harper stage 1: the squash lemma

`Harper.lean` is stage 1 of Harper's vertex-isoperimetric theorem on the Boolean cube `Fin n → Bool`. It is a separate formalization from the proof in `HarperSquash.lean` (namespace `HarperVertex`). This file uses namespace `Harper` so both can live in one project.

**The order.** Vertices with fewer `true`s come first. Among vertices with the same number, the one with `true` at the first coordinate where they differ comes first (`key`). `seg n m` is the first `m` vertices. They are nested (`seg_mono`) and have `min m (2 ^ n)` elements (`card_seg`).

**Squashing along coordinate `i`.** Cut the cube into its two halves `x i = true` and `x i = false`. Replace each half of `A` by the starting segment of the same size in the remaining coordinates (`squash`). Squashing keeps the size (`card_squash`).

**The squash lemma (`squash_nbhd_le`).** A squash never makes the neighbourhood bigger. It takes two hypotheses about the cube one dimension down: the neighbourhood of a starting segment is a starting segment, and the theorem itself (the induction hypothesis).

**File.** `Harper.lean` (namespace `Harper`). 18 results.

## One floor, three pushes

`Unify.lean` proves two general lemmas and restates three earlier results as uses of them.

**Lemma 1 (`mode_compare`).** If every mode `k` pays at least `c` times what it contributes and the weights are nonnegative, then the total pays at least `c` times the total.

* A wave (`wirtinger_by_modes`): on the ring, mode `k ≠ 0` costs `|e(k) − 1|²`, at least the floor `2 − 2 cos (2π/n)`. This is the Wirtinger inequality.
* A shape (`polygon_by_modes`): for a closed polygon, mode `k` costs `|e(−k) − 1|²` in squared sides and carries `Im e(−k)` of area; the cost per unit of area is at least `2 tan (π/n)`. This is the polygon isoperimetric inequality.

**Lemma 2 (`patch_from_gap`).** On any finite graph with symmetric weights, if `λ · spread f ≤ |V| · energy f` for every `f`, then every patch `S` satisfies `λ · |S| · (|V| − |S|) ≤ |V| · boundary S`.

* The cube (`cube_cheeger_by_gap`): with floor `2`, any set of at most half the corners has at least as many edges leaving it as it has corners. This is `CubeCheeger.cheeger`, now a one-step use of the general lemma.
* The ring (`ring_gap`, `ring_patch`): the ring's floor `2 − 2 cos (2π/n)` gives a border bound for every patch of the ring.

**File.** `Unify.lean` (namespace `Unify`). 16 results.

## The extended binary Golay code

`GolayMatrixDistance.lean` proves the classical parameters of the extended binary Golay code of length 24, dimension 12 and minimum distance 8. The generator is `G = [I₁₂ | B]`, where the 12×12 parity block `B` is built from the quadratic residues modulo 11. Mathlib has no Golay code.

| Result | Statement |
|---|---|
| `golay_self_orthogonal` | every pair of generator rows has even overlap, so the code is self-dual |
| `golay_doubly_even_and_d_min_8` | every codeword is doubly even, and every nonzero codeword has weight at least 8 |
| `golay_sharp_weight_8` | the bound 8 is met (the second generator row has weight 8) |
| `golay_min_distance_bound` | every nonzero message encodes to a word of weight at least 8 |
| `golay_weight_distribution` | the weight distribution is 1 / 759 / 2576 / 759 / 1 (weights 0, 8, 12, 16, 24) |

The exhaustive checks run over all 4,096 codewords and use `decide +kernel`.

**File.** `GolayMatrixDistance.lean` (namespace `GolayMatrixDistance`). 5 results.

## The Golay-to-Leech counting bridge

`GolayLeechBridge.lean` checks the arithmetic behind the standard count of the 196,560 shortest vectors of the 24-dimensional Leech lattice. The Golay weight counts 1 / 759 / 2576 / 759 / 1 are written out as a table so the arithmetic stays quick, and `golayWeightCount_eq_code` proves the table agrees with the weight distribution proved from the generator matrix in `GolayMatrixDistance.lean`. This file proves the counting formula. [LeechKissing.lean](LeechKissing.lean) now connects that formula to all the shortest vectors of the lattice defined in `LeechLattice.lean`, through a classification and bijections for the three families.

| Result | Statement |
|---|---|
| `golay_total_codewords` | the weight table adds up to 2¹² = 4,096 |
| `golay_octad_count` | the table lists 759 octads (weight-8 codewords) |
| `leech_shape3_eq` | the `(±4)² 0²²` shell has 276 × 4 = 1,104 vectors |
| `leech_shape1_eq` | the octad shell `(±2)⁸ 0¹⁶` has 759 × 2⁷ = 97,152 vectors |
| `leech_shape2_eq` | the `(∓3)(±1)²³` shell has 4,096 × 24 = 98,304 vectors |
| `leech_kissing_decomposition` | the three shells add up to 196,560 |
| `E8_and_Leech_summary` | the E₈ root count 28 × 4 + 128 = 240, stated next to the 196,560 count |
| `golayWeightCount_eq_code` | the weight table equals the proved weight distribution of the code in `GolayMatrixDistance.lean` |
| `leech_kissing_from_code` | the three shells add up to 196,560 using the proved code counts directly |

The proofs use `decide` or `rfl`; the two links to the code rewrite with `golay_weight_distribution` first.

**File.** `GolayLeechBridge.lean` (namespace `GolayLeechBridge`). 9 results.

## The Leech lattice and its smallest length

`LeechLattice.lean` builds the 24-dimensional Leech lattice from the Golay code proved in `GolayMatrixDistance.lean`, and proves that its shortest nonzero vectors have squared length 32. Coordinates are whole numbers, scaled up by `√8` as usual.

**The code.** A word on 24 positions is a Golay codeword (`IsGolayWord`) when it is the bits of `encodeNat m` for some message `m < 4096`, read with the same bit test that `popcount24` uses. So it is the same code, not a new one. Encoding respects adding messages bit by bit (`encodeNat_xor`), which makes the code closed under adding words. The weight facts come straight from the existing theorems `golay_doubly_even_and_d_min_8` and `golay_min_distance_bound`.

**The lattice.** The definition follows Conway and Sloane, *Sphere Packings, Lattices and Groups*, chapter 4, section 11. A vector `x` of 24 whole numbers is in the lattice when, for `m = 0` or `m = 1`, every entry leaves remainder `m` on division by 2, the total leaves remainder `4m` on division by 8, and for every remainder `k` on division by 4 the positions with `x i ≡ k (mod 4)` form a Golay codeword (`InLeech`). In the even case only the positions with `x i ≡ 2 (mod 4)` need checking, and in the odd case only those with `x i ≡ 3 (mod 4)` (`inLeech_iff`).

**The smallest length.** There are three cases. If every entry is odd, they cannot all be `±1`: the `-1` entries would sit on a codeword, so there would be a multiple of 4 of them, and the total would leave remainder 0 on division by 8 instead of 4. So some entry is at least 3 in size, and the squares add up to at least `9 + 23 = 32`. If every entry is even and some entry is `2 (mod 4)`, those entries sit on a nonzero codeword, so there are at least 8 of them, each with square at least 4. If every entry is a multiple of 4, a single nonzero entry would have to be a multiple of 8 (from the total), and otherwise there are two entries with square at least 16.

| Result | Statement |
|---|---|
| `encodeNat_xor` | encoding the bitwise sum of two messages gives the bitwise sum of their codewords |
| `isGolayWord_xor` | the sum of two codewords is a codeword |
| `isGolayWord_not` | flipping every bit of a codeword gives a codeword |
| `golay_weight_mod_four` | every codeword has a multiple of 4 ones (from `golay_doubly_even_and_d_min_8`) |
| `golay_weight_ge_eight` | every nonzero codeword has at least 8 ones (from `golay_min_distance_bound`) |
| `inLeech_iff` | the full Conway–Sloane condition is the same as the short even-or-odd test |
| `leechLattice` | the lattice as an additive subgroup of `ℤ²⁴`: it contains `0` and is closed under adding and negating |
| `oddLeech_norm_ge` | a lattice vector with all odd entries has squared length at least 32 |
| `evenLeech_norm_ge_of_two` | an even lattice vector with some entry `2 (mod 4)` has squared length at least 32 |
| `evenLeech_norm_ge_of_four` | a nonzero lattice vector with all entries multiples of 4 has squared length at least 32 |
| `leech_norm_ge_32` | every nonzero lattice vector has squared length at least 32 |
| `vecFourFour_mem`, `vecOctad_mem`, `vecThree_mem` | `(4, 4, 0, …)`, `2` on an octad, and `(-3, 1, …, 1)` are in the lattice, each with squared length 32 |
| `vecFour_not_mem`, `vecOnes_not_mem` | `(4, 0, …)` and `(1, …, 1)` are not in the lattice |
| `leech_min_norm` | 32 is the least squared length of a nonzero lattice vector |

The proofs are ordinary Lean proofs plus small `decide` checks on single vectors and on the all-one codeword; nothing reruns the 4,096-codeword checks.

**The next two steps are proved.** [The shortest-vector proof](docs/leech-shortest-vectors.md) sorts every vector of squared length 32 into the three shapes `(±4)² 0²²`, `(±2)⁸ 0¹⁶` and `(∓3)(±1)²³`, proves the converse membership rules, and counts the distinct vectors: 1,104 + 97,152 + 98,304 = 196,560. `card_shortest_vectors` states the result for shortest nonzero vectors of `InLeech`.

**The playground generator now matches.** [PlaygroundGolay.lean](PlaygroundGolay.lean) proves that the modulo-23 recipe gives the same code after a specified coordinate permutation. [PlaygroundLeech.lean](PlaygroundLeech.lean) transfers membership, minimum length, classification and the 196,560 count from the existing proofs. [Evidence and reproduction instructions](docs/playground-golay.md) distinguish the Lean model from the separately checked JavaScript.

**Symmetry.** The [full order theorem](ConwayOrder.lean#L29) counts all origin-fixing isometries of this lattice. Browser execution, projection and animation remain outside Lean.

**File.** `LeechLattice.lean` (namespace `LeechLattice`). 42 theorems and the lattice construction are audited. The eight new modules ending in `LeechKissing.lean` add 50 public theorems.

## A basis of the Leech lattice and unimodularity

`LeechBasis.lean` gives 24 explicit vectors that span the Leech lattice of `LeechLattice.lean` (coordinates scaled by `√8`), and proves the lattice is unimodular. Mathlib has no notion of the volume of a lattice, so unimodularity is stated through the basis and its Gram matrix (the table of all dot products of basis vectors).

**The basis.** Row 0 is `(1, 1, …, 1, -3)`. Rows 1 to 11 are twice the Golay generator rows 1 to 11 from `GolayMatrixDistance.lean`. Rows 12 to 22 are `4 eᵢ + 4 e₂₃`, and row 23 is `8 e₂₃`. Each row starts in its own column, so the matrix is upper triangular, with diagonal 1, then 2 eleven times, then 4 eleven times, then 8. Its determinant is `2³⁶ = 8¹²`, which is exactly the volume a unimodular lattice has after scaling by `√8`.

**Why the basis spans.** Take any lattice vector. If its entries are odd, subtract row 0 to make them even. Then subtract twice the Golay rows picked out by its first 12 entries. What is left still lies in the lattice and has entries that are multiples of 4 in the first 12 places, so its Golay codeword is zero on its first 12 positions, and a codeword like that is zero (checked over all 4,096 messages). So every entry is a multiple of 4 and the total is a multiple of 8, and such a vector is a combination of `4 eₖ - 4 e₂₃` and `8 e₂₃`. The building blocks are written as explicit whole-number combinations of the basis (found by back substitution) and checked with `decide +kernel`.

| Result | Statement |
|---|---|
| `leechBasis_mem` | every basis vector is in the lattice |
| `closure_leechBasis` | the whole-number combinations of the basis are exactly the lattice |
| `golay_eq_false_of_first12` | a Golay codeword that is zero on its first 12 positions is zero |
| `mem_span_of_four` | a vector with every entry a multiple of 4 and total a multiple of 8 is in the span |
| `basisMatrix_det` | the basis matrix has determinant `8¹²` |
| `leechBasis_linearIndependent` | the 24 basis vectors are linearly independent |
| `leech_unimodular` | every Gram entry is divisible by 8, the Gram matrix divided by 8 has determinant 1, and every diagonal Gram entry is divisible by 16 |
| `leech_inner_dvd_eight` | the dot product of any two lattice vectors is divisible by 8 |
| `leech_norm_dvd_sixteen` | every lattice vector has squared length divisible by 16 |

After dividing the coordinates by `√8`, `leech_unimodular` says the lattice is unimodular (determinant 1), and the last two results say it is integral and even, for every vector and not only the basis. The proofs use `decide +kernel` for the finite checks; nothing uses `native_decide`.

**Symmetry.** The [generator theorem](ConwayGenerators.lean#L21) and [group order](ConwayOrder.lean#L29) build on this basis. A comparison with other published bases remains open.

**File.** `LeechBasis.lean` (namespace `LeechBasis`). 29 theorems.

## Edge-optimal sets of the hypercube

`EdgeOptimal.lean` proves the sharp edge-isoperimetric theorem on the cube `Fin n → Bool`: it picks out which sets hold the most edges. Among all sets of `m` corners, the first `m` corners in binary order span the most edges. It uses `size`, `dir` and the first-coordinate split from `Isoperimetric.lean`.

**The order.** A corner `x` is read as the binary number `val x`, where coordinate `i` is the bit of weight `2 ^ i` (`val_eq_sum`). `bin n m` is the set of corners with `val x < m`.

**The count.** `ones k` is the number of `1` bits of `k`, and `h m = ∑_{k<m} ones k`.

| Result | Statement |
|---|---|
| `binary_sum` | `h a + h b + min a b ≤ h (a + b)` for all `a`, `b` |
| `dir_bin` | for `m ≤ 2 ^ n`, `dir (bin n m) = 2 * h m`, so `bin n m` spans exactly `h m` edges |
| `dir_le_two_mul_h` | every set `s` has `dir s ≤ 2 * h (size s)` |
| `dir_le_dir_bin` | if `size s = m`, then `dir s ≤ dir (bin n m)` |
| `max_dir_eq` | for `m ≤ 2 ^ n`, `bin n m` has `m` corners and `2 * h m` ordered adjacent pairs, and no set of `m` corners has more |

**Proof outline.** `h (2x) = 2 h x + x` and `h (2x + 1) = h x + h (x + 1) + x`. The binary-sum inequality follows by strong induction on `a + b`, one case for each parity of `a` and `b`. For the cube, split on the first coordinate: the halves hold `a` and `b` corners, and the edges across are at most `min a b` (`common_le_true`, `common_le_false`), so induction on `n` gives `dir s ≤ 2 * h (size s)`. Splitting `bin (n + 1) m` the same way gives `bin n (m / 2)` and `bin n ((m + 1) / 2)` with `m / 2` edges across (`bin_true`, `bin_false`, `common_bin`), and `h m = h (m / 2) + h ((m + 1) / 2) + m / 2` (`h_split`), so `bin` meets the bound.

**Numerical check.** For `n ≤ 4`, every vertex set was checked against the maximum, and `dir (bin n m) = 2 h m` held for every `m`. For `n = 5, 6`, 20,000 random sets each stayed at or below `dir (bin n m)`. The binary-sum inequality held for all `a, b < 300`.

**File.** `EdgeOptimal.lean` (namespace `HypercubeEdgeOptimal`). 25 results.

## The E₈ plumbing matrix

`E8PlumbingBridge.lean` records the A₄ and E₈ plumbing intersection matrices, checks that they are symmetric, and computes their determinants and the E₈ trace. It also counts even-parity vertices of the 8-cube and pairs of coordinates, which add to 240. These are matrix and count checks; they do not prove that the counted vectors are the roots of the lattice defined by `E8_matrix`.

| Result | Statement |
|---|---|
| `A4_isSymm` | the A₄ plumbing matrix is symmetric |
| `A4_det` | the determinant of the A₄ plumbing matrix is 5 |
| `E8_isSymm` | the E₈ plumbing matrix is symmetric |
| `E8_det` | the determinant of the E₈ plumbing matrix is 1 |
| `E8_trace` | the trace of the E₈ plumbing matrix is −16 |
| `card_spinor_roots` | the 8-cube has 128 even-parity vertices |
| `card_integer_roots` | 4 times the number of unordered pairs of distinct coordinates in `Fin 8` is 112 |
| `total_E8_roots` | those two counts add to 240 |

**File.** `E8PlumbingBridge.lean` (namespace `E8PlumbingBridge`). 8 results.

## The E₈ cost mirror

The cost uses the negative of the E₈ plumbing matrix. Flipping the values on one side of the tree preserves each node’s own contribution and reverses the contribution from each edge. For every assignment of real values to the eight nodes, `E8CostMirror.cost_pair` proves

$$Q(x) + Q(\mathrm{flip}(x)) = 4 \sum_{i=0}^{7} x_i^2.$$

## Build

```sh
lake exe cache get
lake build
lake env lean CheckAxioms.lean > axioms.txt
python3 .github/check_axioms.py CheckAxioms.lean axioms.txt
```

## Discrete Poincaré–Wirtinger inequality on a path

A self-contained Lean 4 / Mathlib proof of a spectral-gap inequality for the path graph, with an explicit constant, and a proof that the mean-zero condition is necessary.

**Statement.** For `f : ℕ → ℝ` and a path of `n` points with `∑_{i<n} f i = 0`,

```
2 * ∑_{i<n} f(i)^2  ≤  n (n-1) * ∑_{k<n-1} (f(k+1) - f(k))^2
```

Equivalently, the Dirichlet form of the path Laplacian is at least `2 / (n(n-1))` times the squared norm on mean-zero data.

**Necessity of the mean condition (`mean_has_no_gap`).** For every `n ≥ 1` and every constant `C`, the inequality `∑ f² ≤ C · Dirichlet(f)` fails for some `f` (the constants): the mean mode has no gap.

### Contents

| Theorem | Statement |
|---|---|
| `telescope` | `f j - f i = ∑_{k ∈ [i, j)} (f(k+1) - f(k))` |
| `step_bound` | for `i ≤ j < n`: `(f j - f i)^2 ≤ (n-1) · Dirichlet(f)` |
| `pair_sum` | `∑_i ∑_j (f i - f j)^2 = 2n ∑ f^2 - 2(∑ f)^2` |
| `poincare` | the inequality above |
| `mean_has_no_gap` | the mean-zero hypothesis cannot be dropped |

No `sorry`; `CheckAxioms.lean` prints the axioms of each theorem, which must be only `propext`, `Classical.choice` and `Quot.sound`.

### Scope and limits

- **Not sharp.** The sharp constant is `1/λ₁` with `λ₁ = 4 sin²(π/(2n))`, about `n²/π²`. The proved constant `n(n-1)/2` is larger by roughly a factor `π²/2 ≈ 4.9` for large `n` (n = 64: 2016 versus 415). The proof is elementary: telescoping, Cauchy–Schwarz, and the pair identity. A sharp version needs the discrete Fourier transform.
- **Path, not cycle.** Free (Neumann) ends; the periodic version is not included.
- **Use.** The inequality is the step that turns the energy identity of a discrete diffusion `u' = ν Δ_h u` into exponential decay of the mean-zero part, while the mean is conserved and does not decay.

Numerical check (outside Lean): random mean-zero vectors for `n = 2 … 39` satisfy the identity and the inequality; the largest observed ratio of the two sides is 0.5.

### Build

Lean `v4.34.0-rc2`, Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`. Built with Lean `v4.34.0-rc2` and Mathlib `85e3a25`, and the axiom check passed.

```sh
lake exe cache get
lake build
```

## The sharp discrete Wirtinger inequality on a cycle

A Lean 4 / Mathlib proof of the sharp spectral-gap inequality for the cycle `ZMod n`, by the discrete Fourier transform, with the equality case.

**Theorem (`wirtinger`).** For `f : ZMod n → ℝ` with `∑ j, f j = 0`,

```
(2 - 2 cos (2π/n)) * ∑ j, f j ^ 2  ≤  ∑ j, (f (j + 1) - f j) ^ 2
```

**Sharpness (`wirtinger_sharp`).** For `n ≥ 3`, `f j = cos (2π j / n)` has mean zero and gives equality, so `2 - 2 cos (2π/n) = 4 sin²(π/n)` is the best constant: the smallest nonzero eigenvalue of the cycle Laplacian. (For `n = 2` every mean-zero `f` gives equality.)

This is the classical discrete Wirtinger inequality (Fan, Taussky and Todd, 1955), here with a machine-checkable proof.

### Proof outline

| Lemma | Content |
|---|---|
| `ortho` | `∑ₖ e(k m) = n` if `m = 0`, else `0` (from `AddChar.sum_mulShift` and `ZMod.isPrimitive_stdAddChar`) |
| `conj_e`, `fourier_neg` | `conj e(x) = e(-x)`; for real data `F(-k) = conj F(k)` |
| `parseval`, `parseval_real` | `∑ₖ |F k|² = n ∑ⱼ f j ²` |
| `fourier_step` | the step `j ↦ f(j+1) - f(j)` multiplies `F k` by `e(-k) - 1` |
| `normSq_e_sub_one`, `normSq_e_neg_sub_one` | `|e(±k) - 1|² = 2 - 2 cos(2π k/n)` |
| `cos_step`, `cos_le` | for `k ≠ 0`, `cos(2π k/n) ≤ cos(2π/n)` |
| `re_sq`, `sum_re_sq` | `∑ⱼ (Re (e(j) w))² = n |w|²/2` when `2 ≠ 0` in `ZMod n` (used for the equality case) |

Here `e = ZMod.stdAddChar`, `e(j) = exp(2πi j/n)`, and `F k = ∑ⱼ f j · e(j k)`.

No `sorry`. `CheckAxioms.lean` prints the axioms of all 15 statements; each must list only `propext`, `Classical.choice` and `Quot.sound`.

### Status

Built with Lean `v4.34.0-rc2` and Mathlib `85e3a25`, and the axiom check passed. Numerical check outside Lean: the inequality holds on random mean-zero data for `n = 1 … 59`, the cosine attains equality for `n ≥ 3`, and Parseval holds.

Lean `v4.34.0-rc2`, Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`.

```sh
lake exe cache get
lake build
```

### Related

`Poincare.lean` proves an elementary, non-sharp inequality for the path (free ends) with constant `n(n-1)/2`. The sharp path constant `1/(4 sin²(π/(2n)))` needs the cosine transform and is not included.

**Later addition:** [PathSix.lean](PathSix.lean) proves the sharp six-point case directly by sums of squares. The preceding note's exclusion still applies to a proof of the general sharp formula for arbitrary path length.

## The gap: what holds the past finite

Fourteen results about stores that hold the past, and the gap that keeps them finite. Every proof is checked: no `sorry`, and only Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Same Lean (`v4.34.0-rc2`) and Mathlib (`85e3a25e…`) as the other packages.

**Build status:** built with Lean `v4.34.0-rc2` and Mathlib `85e3a25`, and the axiom check passed. Build with:

```sh
lake exe cache get
lake build
```

`CheckAxioms` prints the axioms of each theorem.

### The theorem

**`finite_iff_gap`:** a store that adds up a steady positive input stays finite for all time exactly when it lets go at a rate above zero.

- **No way out (`keep`).** It changes at the input rate (`keep_deriv`) and passes every bound (`keep_unbounded`).
- **A gap (`breathe`, rate `r > 0`).** It changes at the input rate minus `r` times what it holds (`breathe_deriv`), never moves further from `u/r` than it started (`breathe_levels`), and stays finite (`breathe_bounded`).

### Each store without a way out adds one power of time

**`chain_store_deriv`:** in a row of stores that each add up the one before, with no way out, the `(k+1)`-th holds `c t^(k+1)/(k+1)!`. That is why the runs grew like powers of time when nothing let go.

### A gap beats every power; a power does not

- **`gap_beats_every_power`:** with a gap, `exp(−r t)` falls faster than `(1+t)^(−K)` for every `K`. This is the kind of decay the official forced Navier–Stokes problem asks of its force (`|f| ≤ C(1+t)^(−K)` for any `K`), and the kind of fall-off a Yang–Mills mass gap gives correlations (clustering, `exp(−C|x−y|)`).
- **`power_decay_fails_rule`:** fading only like `(1+t)^(−p)` fails that test at power `p+1`.

### Input ended, input continuing

- **`input_ended`:** with the input ended, a store with a gap fades like `exp(−r t)`.
- **`steady_input_stays`:** with a steady input it sits at `u/r` and does not fade.

### The breath out

- **`breath_keeps_four_fifths`:** letting go at rate `log(5/4)` for one breath of length 1 keeps exactly `4/5`.
- **`breath_out_is_a_gap`:** that rate is above zero.

### The six rows from the runs

These numbers come from the runs of the Hug v3 solver, not from Lean. Lean proves the rule behind each row.

| Store | Rate it is held back at | Gap? |
|---|---|---|
| Ripples in the flow (lowest on the unit box) | viscosity × (2π)² ≈ 0.59 | yes |
| The whole-box average (the box speed) | viscosity gives 0 | no |
| The box speed, with the clay | KΣgχ/N = 60 × 122 / 4096 ≈ 1.8 | yes |
| A, frozen-start rule | 0 | no |
| A, with the breath out | log(5/4) ≈ 0.22 per breath | yes |
| C, the material strain, b | 0 | no |

Two pairs close (box average with the clay, A with the breath out). The third, the record, is still open.

### Scope

These are statements about single stores and rows of stores. They show the shape both prize problems share, decay faster than any power, and they do not prove either problem. By the official Yang–Mills text, the mass gap is not visible in the classical theory; it belongs to the quantum one.

**AI-generated; dictated and directed by NousVolition.**

## Edge-isoperimetric inequality on the hypercube (Lean 4 / Mathlib)

### Statement

Vertices of the `n`-cube are `Fin n → Bool`. Two vertices are adjacent when their Hamming distance is 1.

**Theorem `HypercubeIso.edges_le`.** For every vertex set `s` of the `n`-cube,

```
dir s * log 2 ≤ size s * log (size s)
```

Here `size s` is the number of vertices in `s`, and `dir s` counts the ordered adjacent pairs inside `s`, which is twice the number of edges `s` spans.

In the usual form, a set of `m` vertices spans at most `(m/2)·log₂ m` edges. Every vertex has degree `n`, so at least `m·(n − log₂ m)` edges leave the set. Subcubes give equality, so the bound is sharp.

The result is classical: Harper (1964), Bernstein (1967), Hart (1976). A search of the pinned Mathlib revision did not find it.

### Proof outline

1. **Split on the first coordinate** (`sum_cube_succ`, `size_succ`, `dir_succ`). The cube is two copies of the `(n−1)`-cube. The edges of `s` are the edges inside each half plus the edges across. Each cross edge joins `(true, u)` to `(false, u)`.
2. **Cross edges ≤ the smaller half** (`common_le_true`, `common_le_false`).
3. **One real inequality** (`key`). For `0 ≤ b ≤ a`:

   `a log a + b log b + 2b log 2 ≤ (a+b) log (a+b)`

   Write `t = b/(a+b) ≤ 1/2`. Then the inequality reads `2t·log 2 ≤ H(t)`, where `H` is binary entropy. This follows from the concavity of `H` between `H(0) = 0` and `H(1/2) = log 2`, using Mathlib's `Real.strictConcave_binEntropy`.
4. **Induction on `n`** (`edges_le`). The base case is the 0-cube, which has one vertex and no edges (`dir_zero`).

### Files

| File | Contents |
|---|---|
| `Isoperimetric.lean` | definitions, 12 lemmas, the theorem |
| `CheckAxioms.lean` | `#print axioms` for every lemma and the theorem |
| `lakefile.toml`, `lean-toolchain` | Lean `v4.34.0-rc2`, Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0` |

### Build

```
lake exe cache get
lake build
```

Passing means:

- Both libraries build.
- The file contains no `sorry`.
- Every `#print axioms` line lists only `propext`, `Classical.choice` and `Quot.sound`. Some lines list fewer.

### Status

- **Built.** Built with Lean `v4.34.0-rc2` and Mathlib `85e3a25`, and the axiom check passed.
- **Numerical check.** The inequality held on:
  - 400 random vertex sets for each cube dimension `n ≤ 7`;
  - every subcube, with equality each time;
  - 20,000 random pairs for `key`.

  The largest ratio of `dir·log 2` to `m log m` was 1.0, reached by subcubes.

### Scope

- This proves the edge-count bound for every set size.
- Harper's stronger result, that initial segments of the binary order are optimal, is proved in [`EdgeOptimal.lean`](EdgeOptimal.lean); see [Edge-optimal sets of the hypercube](#edge-optimal-sets-of-the-hypercube).
- This file does not prove the vertex-isoperimetric inequality. That is proved in this repo, by squashing, in [`HarperSquash.lean`](HarperSquash.lean) and [`HarperSquash/`](HarperSquash); see [Vertex-isoperimetric inequality on the hypercube (Harper's theorem)](#vertex-isoperimetric-inequality-on-the-hypercube-harpers-theorem).

