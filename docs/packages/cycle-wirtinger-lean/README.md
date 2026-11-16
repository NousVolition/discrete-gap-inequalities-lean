# The sharp discrete Wirtinger inequality on a cycle

A Lean 4 / Mathlib proof of the sharp spectral-gap inequality for the cycle `ZMod n`, by the discrete Fourier transform, with the equality case.

**Theorem (`wirtinger`).** For `f : ZMod n → ℝ` with `∑ j, f j = 0`,

```
(2 - 2 cos (2π/n)) * ∑ j, f j ^ 2  ≤  ∑ j, (f (j + 1) - f j) ^ 2
```

**Sharpness (`wirtinger_sharp`).** For `n ≥ 3`, `f j = cos (2π j / n)` has mean zero and gives equality, so `2 - 2 cos (2π/n) = 4 sin²(π/n)` is the best constant: the smallest nonzero eigenvalue of the cycle Laplacian. (For `n = 2` every mean-zero `f` gives equality.)

This is the classical discrete Wirtinger inequality (Fan, Taussky and Todd, 1955), here with a machine-checkable proof.

## Proof outline

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

## Status

Built with Lean `v4.34.0-rc2` and Mathlib `85e3a25`, and the axiom check passed. Numerical check outside Lean: the inequality holds on random mean-zero data for `n = 1 … 59`, the cosine attains equality for `n ≥ 3`, and Parseval holds.

Lean `v4.34.0-rc2`, Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`.

```sh
lake exe cache get
lake build
```

## Related

`discrete-poincare-lean` proves an elementary, non-sharp inequality for the path (free ends) with constant `n(n-1)/2`. The sharp path constant `1/(4 sin²(π/(2n)))` needs the cosine transform and is not included.
