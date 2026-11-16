# Discrete gap inequalities

These six results belong to one problem: the gap. A gap is a floor on smoothing, and a floor on how much a store holds. The four original packages, the ring decay proof and the vertex-isoperimetric proof are collected here as one Lean project. They share Lean `v4.34.0-rc2` and Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`. `CheckAxioms.lean` prints the axioms of all 82 statements.

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

`discrete-poincare-lean` proves an elementary, non-sharp inequality for the path (free ends) with constant `n(n-1)/2`. The sharp path constant `1/(4 sin²(π/(2n)))` needs the cosine transform and is not included.

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
