import Mathlib

/-!
# The E₈ plumbing matrix, sphere boundaries, and root counts

Lean proves that the A₄ and E₈ matrices are symmetric, that their determinants are 5
and 1 respectively, and that the E₈ trace is −16. The last three theorems count
parameters for the two E₈ root families and give their sum, `112 + 128 = 240`.

## How the plumbing graphs identify the boundaries

The boundary identifications below come from classical plumbing theory. For these
four-dimensional plumbings of disk bundles over S², the diagonal entries are the Euler
numbers −2, and an edge contributes +1. The homology exact sequence of the plumbing
and its boundary presents the boundary's first integral homology by this matrix.

* **The A₄ chain.** The determinant 5 gives a group of prime order, hence ℤ/5ℤ.
  The four weights −2 also give the negative continued fraction
  `2 − 1/(2 − 1/(2 − 1/2)) = 5/4`. With `L(p,q)` defined by −p/q surgery on
  the unknot, the boundary is the lens space `L(5,4)`, the orientation reverse
  of `L(5,1)`. [Aceto, McCoy and Park, §1](https://arxiv.org/pdf/2208.02586#page=1)
* **The E₈ tree in dimension four.** The determinant 1 gives trivial first homology.
  The negative-definite E₈ plumbing has boundary the Poincaré homology sphere
  `Σ(2,3,5)`. Its fundamental group, the binary icosahedral group of order 120,
  distinguishes it from S³. [Etnyre and Ozbagci, Example 5.1](https://etnyre.math.gatech.edu/preprints/papers/plumbing.pdf#page=10)
* **The E₈ tree in dimension eight.** Plumbing eight tangent disk bundles of S⁴ along
  the same tree gives the positive E₈ form, represented by `-E8_matrix` after choosing
  signs for the basis. Here the cokernel gives the boundary's third homology. The
  boundary of this particular plumbing is an exotic 7-sphere, homeomorphic to S⁷
  with a different smooth structure. Its oriented class generates `Θ₇ ≅ ℤ/28ℤ`.
  [Ding and Geiges, §2](https://arxiv.org/pdf/math/0403358#page=3) and
  [Kervaire and Milnor](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/kervmiln.pdf)

The determinant proofs use `simp` and `norm_det`. A direct expansion would have
24 permutation terms for A₄ and 40,320 for E₈.
-/

open Matrix

namespace E8PlumbingBridge

/-! ## 1. The A₄ chain plumbing matrix -/

/-- Intersection matrix of the `A₄` linear plumbing chain (with `-2` self-intersections). -/
def A4_matrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![-2,  1,  0,  0;
      1, -2,  1,  0;
      0,  1, -2,  1;
      0,  0,  1, -2]

/-- `A₄` is symmetric. -/
theorem A4_isSymm : A4_matrix.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The determinant of the displayed A₄ plumbing matrix is 5. -/
theorem A4_det : A4_matrix.det = 5 := by
  simp [A4_matrix, norm_det]

/-! ## 2. The E₈ plumbing matrix -/

/-- Intersection matrix of the `E₈` plumbing tree (with `-2` self-intersections and a
trivalent branch at node `4` connected to nodes `3`, `5`, and `7`; arms of length 4, 2, 1). -/
def E8_matrix : Matrix (Fin 8) (Fin 8) ℤ :=
  !![-2,  1,  0,  0,  0,  0,  0,  0;
      1, -2,  1,  0,  0,  0,  0,  0;
      0,  1, -2,  1,  0,  0,  0,  0;
      0,  0,  1, -2,  1,  0,  0,  0;
      0,  0,  0,  1, -2,  1,  0,  1;
      0,  0,  0,  0,  1, -2,  1,  0;
      0,  0,  0,  0,  0,  1, -2,  0;
      0,  0,  0,  0,  1,  0,  0, -2]

/-- `E₈` is symmetric. -/
theorem E8_isSymm : E8_matrix.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The E₈ plumbing matrix has determinant 1 and hence is unimodular over ℤ. -/
theorem E8_det : E8_matrix.det = 1 := by
  simp [E8_matrix, norm_det]

/-- The trace of `E₈_matrix` is `-16` (`8` spheres each of self-intersection `-2`). -/
theorem E8_trace : Matrix.trace E8_matrix = -16 := by
  simp [E8_matrix, Matrix.trace]
  decide

/-! ## 3. Why the two parameter counts describe the 240 roots of E₈

The Lean statements below count coordinate pairs with signs and even-parity vertices of
the 8-cube. The following coordinate argument explains the root terminology.

Write `D₈` for the integer vectors in eight coordinates with even sum, and put
`h = (1/2, …, 1/2)`. The standard coordinate model of E₈ is `D₈ ∪ (h + D₈)`.
Its roots are the vectors of squared length 2. [Moorhouse, E₈ coordinates](https://ericmoorhouse.org/e8/)

* In `D₈`, squared length 2 forces exactly two nonzero coordinates, both ±1.
  Every such choice has even sum. Reading the positions in increasing order gives
  28 choices of support and four independent sign combinations, hence 112 roots.
* In `h + D₈`, every coordinate contributes at least 1/4 to the squared length.
  Equality at total 2 forces all eight coordinates to be ±1/2. With `k` minus
  signs their sum is `4 − k`, so precisely the 128 even sign patterns occur.

To see why this model realizes the displayed matrix, divide each row of
`LeechThreeE8.e8Root` by four. The listed rows then belong to the coordinate
model, and `LeechThreeE8.e8_gram` gives their Gram matrix as `-E8_matrix`.
Its determinant is 1 by `E8_det`, so their integer span has covolume 1.
The coordinate model also has covolume 1, since `D₈` has index two both in ℤ⁸
and in the model. The inclusion of the row lattice therefore has index one.
Thus the two families exhaust the vectors of square −2 for the plumbing form.
This lattice identification is a mathematical argument in the comments.
-/

/-- The 8-dimensional hypercube (`Fin 8 → Bool`), matching `HypercubeIso.Cube 8`. -/
abbrev Cube8 := Fin 8 → Bool

/-- Even-parity predicate on `Cube8` (even number of `true` coordinates). -/
def isEvenParity (x : Cube8) : Bool :=
  (Finset.univ.filter (fun i => x i = true)).card % 2 == 0

/-- Flip the coordinate at index `0`. This changes the number of `true` coordinates by one,
so it swaps even-parity vertices with odd-parity vertices. -/
private def flipZero (x : Cube8) : Cube8 :=
  fun i => if i = 0 then !x i else x i

private lemma flipZero_involutive (x : Cube8) : flipZero (flipZero x) = x := by
  ext i
  simp only [flipZero]
  split_ifs <;> simp

private lemma flipZero_injective : Function.Injective flipZero := by
  intro x y h
  simpa [flipZero_involutive] using congrArg flipZero h

private lemma support_flipZero (x : Cube8) :
    Finset.univ.filter (fun i => flipZero x i = true) =
      if x 0 = true then
        (Finset.univ.filter (fun i => x i = true)).erase 0
      else
        insert 0 (Finset.univ.filter (fun i => x i = true)) := by
  ext i
  by_cases hx0 : x 0 = true <;> by_cases hi : i = 0 <;> simp [flipZero, hx0, hi]

private lemma even_add_one_mod (n : ℕ) :
    ((n + 1) % 2 == 0) = !(n % 2 == 0) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · simp [Nat.add_mod, h]
  · simp [Nat.add_mod, h]

private lemma even_sub_one_mod {n : ℕ} (hn : 0 < n) :
    ((n - 1) % 2 == 0) = !(n % 2 == 0) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have : (n - 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (n - 1) % 2 = 0 := by omega
    simp [h, this]

private lemma isEvenParity_flipZero (x : Cube8) :
    isEvenParity (flipZero x) = ! isEvenParity x := by
  simp only [isEvenParity]
  cases hx : x 0
  · have hnot : 0 ∉ Finset.univ.filter (fun i => x i = true) := by
      simp [hx]
    simp [support_flipZero, hx, Finset.card_insert_of_notMem hnot, even_add_one_mod]
  · have hmem : 0 ∈ Finset.univ.filter (fun i => x i = true) := by
      simp [hx]
    have hpos : 0 < (Finset.univ.filter (fun i => x i = true)).card :=
      Finset.card_pos.mpr ⟨0, hmem⟩
    simp [support_flipZero, hx, Finset.card_erase_of_mem hmem, even_sub_one_mod hpos]

private lemma map_flipZero_even_eq_odd :
    (Finset.univ.filter (fun x : Cube8 => isEvenParity x = true)).map
      ⟨flipZero, flipZero_injective⟩ =
    Finset.univ.filter (fun x : Cube8 => isEvenParity x = false) := by
  ext y
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp [isEvenParity_flipZero, hx]
  · intro hy
    refine ⟨flipZero y, ?_, flipZero_involutive y⟩
    simp [isEvenParity_flipZero, hy]

private lemma card_cube8 : (Finset.univ : Finset Cube8).card = 256 := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  norm_num

/-- The 8-cube has 128 even-parity sign patterns. For a half-integer root,
`true` selects −1/2 and `false` selects +1/2. -/
theorem card_spinor_roots :
    (Finset.univ.filter (fun x : Cube8 => isEvenParity x = true)).card = 128 := by
  set evenSet := Finset.univ.filter (fun x : Cube8 => isEvenParity x = true)
  set oddSet := Finset.univ.filter (fun x : Cube8 => isEvenParity x = false)
  have hpart : evenSet.card + oddSet.card = 256 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset Cube8)) (fun x => isEvenParity x = true)
    simp only [Bool.not_eq_true, card_cube8] at h
    exact h
  have hsame : evenSet.card = oddSet.card := by
    simpa [evenSet, oddSet, Finset.card_map] using
      congrArg Finset.card map_flipZero_even_eq_odd
  omega

/-- Four sign choices for each increasing pair of coordinate indices give
`4 × 28 = 112` parameter choices for the integral roots. -/
theorem card_integer_roots :
    4 * (Finset.univ.filter (fun p : Fin 8 × Fin 8 => p.1 < p.2)).card = 112 := by
  decide

/-- The signed coordinate-pair count and the even-parity sign count add to 240. -/
theorem total_E8_roots :
    4 * (Finset.univ.filter (fun p : Fin 8 × Fin 8 => p.1 < p.2)).card +
    (Finset.univ.filter (fun x : Cube8 => isEvenParity x = true)).card = 240 := by
  have h₁ := card_integer_roots
  have h₂ := card_spinor_roots
  omega

end E8PlumbingBridge
