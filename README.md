# Discrete gap inequalities

These results belong to one problem: the gap. A gap is a floor on smoothing, and a floor on how much a store holds. The four original packages, the ring decay proof, the vertex-isoperimetric proof, the polygon isoperimetric inequality, the cube's gap with Cheeger's inequality, the short bridges that tie the cycle, the polygon and the cube together, the gap of the grid made of two rings, the wall and the push, Harper stage 1 (the squash lemma), the one-floor reading that restates the wave, the patch and the shape, and the extended binary Golay code are collected here as one Lean project. They share Lean `v4.34.0-rc2` and Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`. `CheckAxioms.lean` prints the axioms of all 236 statements.

Author: NousVolition.

## Discrete Poincaré

**Statement.** For `f : ℕ → ℝ` and a path of `n` points with `∑_{i<n} f i = 0`,

```
2 * ∑_{i<n} f(i)^2  ≤  n (n-1) * ∑_{k<n-1} (f(k+1) - f(k))^2
```

Equivalently, the Dirichlet form of the path Laplacian is at least `2 / (n(n-1))` times the squared norm on mean-zero data.

The original note is kept, wording unchanged, at [docs/discrete-poincare.md](docs/discrete-poincare.md), and is included below.

## Cycle Wirtinger

**Theorem (`wirtinger`).** For `f : ZMod n → ℝ` with `∑ j, f j = 0`,

```
(2 - 2 cos (2π/n)) * ∑ j, f j ^ 2  ≤  ∑ j, (f (j + 1) - f j) ^ 2
```

The original note is kept, wording unchanged, at [docs/cycle-wirtinger.md](docs/cycle-wirtinger.md), and is included below.

## The Hug gap

**`finite_iff_gap`:** a store that adds up a steady positive input stays finite for all time exactly when it lets go at a rate above zero.

The original note is kept, wording unchanged, at [docs/hug-gap.md](docs/hug-gap.md), and is included below.

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

## The grid made of two rings

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

**File.** `Torus.lean` (namespace `RingGrid`).


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

`Harper.lean` is stage 1 of Harper's vertex-isoperimetric theorem on the Boolean cube `Fin n → Bool`. It is a separate formalization from the complete proof in `HarperSquash.lean` (namespace `HarperVertex`). This file uses namespace `Harper` so both can live in one project.

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

## The gap: what holds the past finite

Fourteen results about stores that hold the past, and the gap that keeps them finite. Every proof is complete: no `sorry`, and only Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Same Lean (`v4.34.0-rc2`) and Mathlib (`85e3a25e…`) as the other packages.

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
- It does not prove Harper's stronger result, which picks out *which* sets are optimal (initial segments of the binary order).
- This file does not prove the vertex-isoperimetric inequality. That is proved in this repo, by squashing, in [`HarperSquash.lean`](HarperSquash.lean) and [`HarperSquash/`](HarperSquash); see [Vertex-isoperimetric inequality on the hypercube (Harper's theorem)](#vertex-isoperimetric-inequality-on-the-hypercube-harpers-theorem).
