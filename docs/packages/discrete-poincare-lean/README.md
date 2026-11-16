# Discrete Poincaré–Wirtinger inequality on a path

A self-contained Lean 4 / Mathlib proof of a spectral-gap inequality for the path graph, with an explicit constant, and a proof that the mean-zero condition is necessary.

**Statement.** For `f : ℕ → ℝ` and a path of `n` points with `∑_{i<n} f i = 0`,

```
2 * ∑_{i<n} f(i)^2  ≤  n (n-1) * ∑_{k<n-1} (f(k+1) - f(k))^2
```

Equivalently, the Dirichlet form of the path Laplacian is at least `2 / (n(n-1))` times the squared norm on mean-zero data.

**Necessity of the mean condition (`mean_has_no_gap`).** For every `n ≥ 1` and every constant `C`, the inequality `∑ f² ≤ C · Dirichlet(f)` fails for some `f` (the constants): the mean mode has no gap.

## Contents

| Theorem | Statement |
|---|---|
| `telescope` | `f j - f i = ∑_{k ∈ [i, j)} (f(k+1) - f(k))` |
| `step_bound` | for `i ≤ j < n`: `(f j - f i)^2 ≤ (n-1) · Dirichlet(f)` |
| `pair_sum` | `∑_i ∑_j (f i - f j)^2 = 2n ∑ f^2 - 2(∑ f)^2` |
| `poincare` | the inequality above |
| `mean_has_no_gap` | the mean-zero hypothesis cannot be dropped |

No `sorry`; `CheckAxioms.lean` prints the axioms of each theorem, which must be only `propext`, `Classical.choice` and `Quot.sound`.

## Scope and limits

- **Not sharp.** The sharp constant is `1/λ₁` with `λ₁ = 4 sin²(π/(2n))`, about `n²/π²`. The proved constant `n(n-1)/2` is larger by roughly a factor `π²/2 ≈ 4.9` for large `n` (n = 64: 2016 versus 415). The proof is elementary: telescoping, Cauchy–Schwarz, and the pair identity. A sharp version needs the discrete Fourier transform.
- **Path, not cycle.** Free (Neumann) ends; the periodic version is not included.
- **Use.** The inequality is the step that turns the energy identity of a discrete diffusion `u' = ν Δ_h u` into exponential decay of the mean-zero part, while the mean is conserved and does not decay.

Numerical check (outside Lean): random mean-zero vectors for `n = 2 … 39` satisfy the identity and the inequality; the largest observed ratio of the two sides is 0.5.

## Build

Lean `v4.34.0-rc2`, Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`. Built with Lean `v4.34.0-rc2` and Mathlib `85e3a25`, and the axiom check passed.

```sh
lake exe cache get
lake build
```
