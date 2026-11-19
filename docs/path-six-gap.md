# The six-point path gap

[PathSix.lean](../PathSix.lean) proves that the six-point path gap is

$$\lambda = 2-\sqrt{3}.$$

This rounds to `0.268`, the value shown in Trilogy.

For every six real values with $f_0+\cdots+f_5=0$,

$$
(2-\sqrt{3})\sum_{i=0}^{5}f_i^2
\;\le\;\sum_{i=0}^{4}(f_{i+1}-f_i)^2.
$$

The energy is the existing `DiscretePoincare.dirichlet f 6`: five edges, unit weights, and free endpoints. There is no edge from the last point back to the first. Lean proves the inequality for every choice of six real values whose sum is zero.

## Why the coefficient is sharp

The explicit vector

$$
(1,\sqrt3-1,2-\sqrt3,\sqrt3-2,1-\sqrt3,-1)
$$

has zero sum, positive squared norm, and energy equal to $(2-\sqrt3)$ times that norm. The theorems `mode_mean_zero`, `mode_mass_pos` and `mode_equality` check those facts. `sharp` proves that no larger coefficient works for every mean-zero input; `valid_bound_iff` says a coefficient works if and only if it is at most `2-√3`.

## What the display means

Lean proves

```text
0.2679491924 < 2 − √3 < 0.2679491925.
```

It also places the gap strictly between `0.2675` and `0.2685`, which justifies rounding to `0.268` at three decimal places. The decimal is slightly larger than `2−√3`: `rounded_value_not_valid_bound` proves that using literal `0.268` as the coefficient in the universal inequality would be false.

These results justify the displayed value. JavaScript arithmetic, rendering and the browser's time evolution are outside this proof.

## How the proof works

Split the values into their sums and differences under reversal:

```text
(a,b,c) = (f₀+f₅, f₁+f₄, f₂+f₃)
(x,y,z) = (f₀−f₅, f₁−f₄, f₂−f₃).
```

The mean-zero assumption gives `a+b+c=0`. The symmetric energy satisfies
`(b−a)²+(c−b)² − (a²+b²+c²) = 3b²`, so its gap is at least 1.

For the antisymmetric part, put `s=√3` and `λ=2−s`. Lean checks the identity

```text
4[(y−x)²+(z−y)²+2z² − λ(x²+y²+z²)]
  = (s−1)[2x−(s+1)y]² + 2(s−1)[y−(s+1)z]².
```

Both terms on the right are nonnegative because `s>1`. Combining the two parts proves the bound. The equality vector shows that the coefficient cannot be increased. Every bound in the argument is checked in Lean.

## Verification and reproduction

The module uses Lean `v4.34.0-rc2` and Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`, matching the rest of the project. All **16 new statements** passed local Lean compilation and the [axiom audit](path-six-axioms.txt): only `propext`, `Classical.choice` and `Quot.sound` occur. No `sorry`, added axiom or native decision shortcut is used.

The subsequent complete local check compiled all **32 project modules** and audited **551 statements**, with **0 nonstandard axioms and 0 missing reports**. The [verification record](path-six-verification.json) records the compiler, Mathlib revision and normalized source hashes. This record covers local verification. The [GitHub workflow](https://github.com/NousVolition/discrete-gap-inequalities-lean/actions/workflows/lean.yml) also runs the build and axiom audit on every push.

`PathSix` is included in the Lake build targets and [CheckAxioms.lean](../CheckAxioms.lean). The inventory is **551 statements**: the previous 535, including the E₈ addition, plus these 16. To reproduce the build and complete audit:

```sh
lake exe cache get
lake build
lake env lean CheckAxioms.lean > axioms.txt
python3 .github/check_axioms.py CheckAxioms.lean axioms.txt
```

The source/computation report in [playground-connections.md](playground-connections.md) and its saved JSON retain their original pinned playground revision. They remain historical numerical evidence; this module supplies the new formal proof.
