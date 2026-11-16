# Edge-isoperimetric inequality on the hypercube (Lean 4 / Mathlib)

## Statement

Vertices of the `n`-cube are `Fin n → Bool`. Two vertices are adjacent when their Hamming distance is 1.

**Theorem `HypercubeIso.edges_le`.** For every vertex set `s` of the `n`-cube,

```
dir s * log 2 ≤ size s * log (size s)
```

Here `size s` is the number of vertices in `s`, and `dir s` counts the ordered adjacent pairs inside `s`, which is twice the number of edges `s` spans.

In the usual form, a set of `m` vertices spans at most `(m/2)·log₂ m` edges. Every vertex has degree `n`, so at least `m·(n − log₂ m)` edges leave the set. Subcubes give equality, so the bound is sharp.

The result is classical: Harper (1964), Bernstein (1967), Hart (1976). A search of the pinned Mathlib revision did not find it.

## Proof outline

1. **Split on the first coordinate** (`sum_cube_succ`, `size_succ`, `dir_succ`). The cube is two copies of the `(n−1)`-cube. The edges of `s` are the edges inside each half plus the edges across. Each cross edge joins `(true, u)` to `(false, u)`.
2. **Cross edges ≤ the smaller half** (`common_le_true`, `common_le_false`).
3. **One real inequality** (`key`). For `0 ≤ b ≤ a`:

   `a log a + b log b + 2b log 2 ≤ (a+b) log (a+b)`

   Write `t = b/(a+b) ≤ 1/2`. Then the inequality reads `2t·log 2 ≤ H(t)`, where `H` is binary entropy. This follows from the concavity of `H` between `H(0) = 0` and `H(1/2) = log 2`, using Mathlib's `Real.strictConcave_binEntropy`.
4. **Induction on `n`** (`edges_le`). The base case is the 0-cube, which has one vertex and no edges (`dir_zero`).

## Files

| File | Contents |
|---|---|
| `Isoperimetric.lean` | definitions, 12 lemmas, the theorem |
| `CheckAxioms.lean` | `#print axioms` for every lemma and the theorem |
| `lakefile.toml`, `lean-toolchain` | Lean `v4.34.0-rc2`, Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0` |

## Build

```
lake exe cache get
lake build
```

Passing means:

- Both libraries build.
- The file contains no `sorry`.
- Every `#print axioms` line lists only `propext`, `Classical.choice` and `Quot.sound`. Some lines list fewer.

## Status

- **Built.** Built with Lean `v4.34.0-rc2` and Mathlib `85e3a25`, and the axiom check passed.
- **Numerical check.** The inequality held on:
  - 400 random vertex sets for each cube dimension `n ≤ 7`;
  - every subcube, with equality each time;
  - 20,000 random pairs for `key`.

  The largest ratio of `dir·log 2` to `m log m` was 1.0, reached by subcubes.

## Scope

- This proves the edge-count bound for every set size.
- It does not prove Harper's stronger result, which picks out *which* sets are optimal (initial segments of the binary order).
- It does not prove the vertex-isoperimetric inequality.
