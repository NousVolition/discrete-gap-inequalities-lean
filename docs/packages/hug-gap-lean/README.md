# The gap: what holds the past finite

Fourteen results about stores that hold the past, and the gap that keeps them finite. Every proof is complete: no `sorry`, and only Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Same Lean (`v4.34.0-rc2`) and Mathlib (`85e3a25e…`) as the other packages.

**Build status:** built with Lean `v4.34.0-rc2` and Mathlib `85e3a25`, and the axiom check passed. Build with:

```sh
lake exe cache get
lake build
```

`CheckAxioms` prints the axioms of each theorem.

## The theorem

**`finite_iff_gap`:** a store that adds up a steady positive input stays finite for all time exactly when it lets go at a rate above zero.

- **No way out (`keep`).** It changes at the input rate (`keep_deriv`) and passes every bound (`keep_unbounded`).
- **A gap (`breathe`, rate `r > 0`).** It changes at the input rate minus `r` times what it holds (`breathe_deriv`), never moves further from `u/r` than it started (`breathe_levels`), and stays finite (`breathe_bounded`).

## Each store without a way out adds one power of time

**`chain_store_deriv`:** in a row of stores that each add up the one before, with no way out, the `(k+1)`-th holds `c t^(k+1)/(k+1)!`. That is why the runs grew like powers of time when nothing let go.

## A gap beats every power; a power does not

- **`gap_beats_every_power`:** with a gap, `exp(−r t)` falls faster than `(1+t)^(−K)` for every `K`. This is the kind of decay the official forced Navier–Stokes problem asks of its force (`|f| ≤ C(1+t)^(−K)` for any `K`), and the kind of fall-off a Yang–Mills mass gap gives correlations (clustering, `exp(−C|x−y|)`).
- **`power_decay_fails_rule`:** fading only like `(1+t)^(−p)` fails that test at power `p+1`.

## Input ended, input continuing

- **`input_ended`:** with the input ended, a store with a gap fades like `exp(−r t)`.
- **`steady_input_stays`:** with a steady input it sits at `u/r` and does not fade.

## The breath out

- **`breath_keeps_four_fifths`:** letting go at rate `log(5/4)` for one breath of length 1 keeps exactly `4/5`.
- **`breath_out_is_a_gap`:** that rate is above zero.

## The six rows from the runs

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

## Scope

These are statements about single stores and rows of stores. They show the shape both prize problems share, decay faster than any power, and they do not prove either problem. By the official Yang–Mills text, the mass gap is not visible in the classical theory; it belongs to the quantum one.

**AI-generated; dictated and directed by NousVolition.**
