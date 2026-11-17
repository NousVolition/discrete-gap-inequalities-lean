import RingDecay

/-!
# The gap of the grid made of two rings

The flat grid `ZMod m × ZMod n` is two rings laid across each other: each point `(i, j)` has a
neighbor one step along the first ring, `(i + 1, j)`, and one step along the second, `(i, j + 1)`.
Its energy is

  `energy f = ∑ (i, j), ((f (i + 1, j) - f (i, j)) ^ 2 + (f (i, j + 1) - f (i, j)) ^ 2)`.

For `f` with `∑ f = 0`,

  `min (gap m) (gap n) * ∑ f ^ 2 ≤ energy f`   (`grid_gap`),

where `gap k = 2 - 2 cos (2π/k) = 4 sin² (π/k)` is the ring gap from `RingDecay.lean`. For
`m, n ≥ 2` the waves `cos (2π i/m)` along the first ring and `cos (2π j/n)` along the second have
mean zero and meet their own ring gap with equality (`rowWave_sharp`, `colWave_sharp`), so the
constant `min (gap m) (gap n)` is attained (`grid_gap_sharp`): the grid settles no slower than its
slower ring, and no faster.

The proof splits `f` into its row means `c i = (∑ j, f (i, j)) / n` and the rest
`g (i, j) = f (i, j) - c i`. Each row of `g` has sum zero, so the cross terms vanish
(`sum_sq_add_of_sum_zero`):

* `∑ f ^ 2 = n ∑ c ^ 2 + ∑ g ^ 2` (`sum_sq_split`);
* steps along the first ring: `≥ n ∑ (c (i + 1) - c i) ^ 2 ≥ n · gap m · ∑ c ^ 2`
  (`first_steps_split`, then the cycle Wirtinger inequality for `c`);
* steps along the second ring: `≥ gap n · ∑ g ^ 2` (the cycle Wirtinger inequality on each row).
-/

open Finset
open scoped Real

namespace RingGrid

open RingDecay (gap)

variable {m n : ℕ} [NeZero m] [NeZero n]

/-- The energy of `f` on the grid of two rings: squared steps along both rings. -/
noncomputable def energy (f : ZMod m × ZMod n → ℝ) : ℝ :=
  ∑ p : ZMod m × ZMod n, ((f (p.1 + 1, p.2) - f p) ^ 2 + (f (p.1, p.2 + 1) - f p) ^ 2)

/-- The mean of row `i`. -/
noncomputable def rowMean (f : ZMod m × ZMod n → ℝ) (i : ZMod m) : ℝ := (∑ j, f (i, j)) / n

omit [NeZero m] in
/-- A constant plus a sum-zero row: `∑ⱼ (a + x j)² = n a² + ∑ⱼ x j²`. -/
lemma sum_sq_add_of_sum_zero (a : ℝ) (x : ZMod n → ℝ) (hx : ∑ j, x j = 0) :
    ∑ j, (a + x j) ^ 2 = n * a ^ 2 + ∑ j, x j ^ 2 := by
  have h : ∀ j, (a + x j) ^ 2 = a ^ 2 + 2 * a * x j + x j ^ 2 := fun j => by ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, hx, Finset.sum_const,
    Finset.card_univ, ZMod.card, nsmul_eq_mul]
  ring

omit [NeZero m] in
/-- Each row minus its mean has sum zero. -/
lemma row_sub_mean (f : ZMod m × ZMod n → ℝ) (i : ZMod m) :
    ∑ j, (f (i, j) - rowMean f i) = 0 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    rowMean]
  field_simp
  ring

/-- If `f` has sum zero, so do its row means. -/
lemma sum_rowMean (f : ZMod m × ZMod n → ℝ) (hf : ∑ p, f p = 0) : ∑ i, rowMean f i = 0 := by
  rw [Fintype.sum_prod_type] at hf
  simp only [rowMean, ← Finset.sum_div, hf, zero_div]

/-- `∑ f² = n ∑ c² + ∑ g²`, with `c` the row means and `g = f - c`. -/
lemma sum_sq_split (f : ZMod m × ZMod n → ℝ) :
    ∑ p, f p ^ 2 = n * ∑ i, rowMean f i ^ 2 + ∑ p, (f p - rowMean f p.1) ^ 2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h := sum_sq_add_of_sum_zero (rowMean f i) (fun j => f (i, j) - rowMean f i)
    (row_sub_mean f i)
  simp only [add_sub_cancel] at h
  exact h

/-- Steps along the first ring split the same way: `n ∑ (c (i+1) - c i)²` plus the steps of `g`. -/
lemma first_steps_split (f : ZMod m × ZMod n → ℝ) :
    ∑ p : ZMod m × ZMod n, (f (p.1 + 1, p.2) - f p) ^ 2
      = n * ∑ i, (rowMean f (i + 1) - rowMean f i) ^ 2
        + ∑ p : ZMod m × ZMod n,
          ((f (p.1 + 1, p.2) - rowMean f (p.1 + 1)) - (f p - rowMean f p.1)) ^ 2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hx : ∑ j, ((f (i + 1, j) - rowMean f (i + 1)) - (f (i, j) - rowMean f i)) = 0 := by
    rw [Finset.sum_sub_distrib, row_sub_mean, row_sub_mean, sub_zero]
  have h := sum_sq_add_of_sum_zero (rowMean f (i + 1) - rowMean f i) _ hx
  rw [← h]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- Steps along the second ring, row by row, by the cycle Wirtinger inequality. -/
lemma second_steps_ge (f : ZMod m × ZMod n → ℝ) :
    gap n * ∑ p, (f p - rowMean f p.1) ^ 2
      ≤ ∑ p : ZMod m × ZMod n, (f (p.1, p.2 + 1) - f p) ^ 2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h := CycleWirtinger.wirtinger (fun j => f (i, j) - rowMean f i) (row_sub_mean f i)
  simp only [sub_sub_sub_cancel_right] at h
  exact h

/-- **The grid of two rings has gap at least the smaller ring gap.** For `f` with sum zero,
`min (gap m) (gap n) * ∑ f² ≤ energy f`. -/
theorem grid_gap (f : ZMod m × ZMod n → ℝ) (hf : ∑ p, f p = 0) :
    min (gap m) (gap n) * ∑ p, f p ^ 2 ≤ energy f := by
  have hE : energy f = ∑ p : ZMod m × ZMod n, (f (p.1 + 1, p.2) - f p) ^ 2
      + ∑ p : ZMod m × ZMod n, (f (p.1, p.2 + 1) - f p) ^ 2 := by
    rw [energy, Finset.sum_add_distrib]
  have hc := CycleWirtinger.wirtinger (rowMean f) (sum_rowMean f hf)
  have hV := second_steps_ge f
  have hH := first_steps_split f
  have hS := sum_sq_split f
  have hrest : 0 ≤ ∑ p : ZMod m × ZMod n,
      ((f (p.1 + 1, p.2) - rowMean f (p.1 + 1)) - (f p - rowMean f p.1)) ^ 2 :=
    Finset.sum_nonneg (fun p _ => sq_nonneg _)
  have hC : 0 ≤ ∑ i, rowMean f i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hG : 0 ≤ ∑ p, (f p - rowMean f p.1) ^ 2 := Finset.sum_nonneg (fun p _ => sq_nonneg _)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : min (gap m) (gap n) ≤ gap m := min_le_left _ _
  have h2 : min (gap m) (gap n) ≤ gap n := min_le_right _ _
  have hcm : gap m * ∑ i, rowMean f i ^ 2 ≤ ∑ i, (rowMean f (i + 1) - rowMean f i) ^ 2 := hc
  rw [hE, hH, hS]
  nlinarith [mul_le_mul_of_nonneg_right h1 (mul_nonneg hn hC),
    mul_le_mul_of_nonneg_right h2 hG, mul_le_mul_of_nonneg_left hcm hn]

/-! ## The constant is attained -/

omit [NeZero m] in
/-- For `n ≥ 2`, the wave `w j = cos (2π j/n)` on one ring has mean zero and meets the ring gap
with equality: `∑ (w (j+1) - w j)² = gap n * ∑ w²`. -/
lemma ring_wave (hn : 2 ≤ n) :
    ∑ j : ZMod n, Real.cos (2 * π * j.val / n) = 0 ∧
    ∑ j : ZMod n, (Real.cos (2 * π * (j + 1).val / n) - Real.cos (2 * π * j.val / n)) ^ 2
      = gap n * ∑ j : ZMod n, Real.cos (2 * π * j.val / n) ^ 2 := by
  have : Fact (1 < n) := ⟨by omega⟩
  set w : ZMod n → ℝ := fun j => Real.cos (2 * π * j.val / n) with hw
  have hre : ∀ j : ZMod n, w j = (ZMod.stdAddChar j).re := by
    intro j
    rw [hw]
    simp only
    rw [CycleWirtinger.e_eq_exp, Complex.exp_ofReal_mul_I_re]
  constructor
  · change ∑ j, w j = 0
    simp only [hre]
    rw [← Complex.re_sum]
    have h1 := CycleWirtinger.ortho (n := n) 1
    simp only [one_ne_zero, ↓reduceIte, mul_one] at h1
    rw [h1, Complex.zero_re]
  · change ∑ j, (w (j + 1) - w j) ^ 2 = gap n * ∑ j, w j ^ 2
    have hstep := congrFun (RingDecay.heatStep_wave hn 1)
    have hnb : ∀ j, w (j + 1) + w (j - 1) = (2 - gap n) * w j := by
      intro j
      have := hstep j
      simp only [RingDecay.heatStep, one_mul] at this
      change w j + (w (j + 1) - 2 * w j + w (j - 1)) = (1 - gap n) * w j at this
      linarith
    have hshift1 : ∑ j, w (j + 1) ^ 2 = ∑ j, w j ^ 2 :=
      RingDecay.sum_shift_add (fun j => w j ^ 2) 1
    have hshift2 : ∑ j, w j * w (j - 1) = ∑ j, w (j + 1) * w j := by
      have := RingDecay.sum_shift_add (fun j => w j * w (j - 1)) 1
      simp only [add_sub_cancel_right] at this
      exact this.symm
    have hsum : ∑ j, w j * (w (j + 1) + w (j - 1)) = (2 - gap n) * ∑ j, w j ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [hnb j]; ring)
    have hsplit : ∑ j, w j * (w (j + 1) + w (j - 1))
        = ∑ j, w (j + 1) * w j + ∑ j, w j * w (j - 1) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hexp : ∑ j, (w (j + 1) - w j) ^ 2
        = ∑ j, w (j + 1) ^ 2 + ∑ j, w j ^ 2 - 2 * ∑ j, w (j + 1) * w j := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hexp, hshift1]
    rw [hsplit, hshift2] at hsum
    linarith

/-- The wave along the first ring: `cos (2π i/m)`, the same on every row. -/
noncomputable def rowWave (p : ZMod m × ZMod n) : ℝ := Real.cos (2 * π * p.1.val / m)

/-- The wave along the second ring: `cos (2π j/n)`, the same on every column. -/
noncomputable def colWave (p : ZMod m × ZMod n) : ℝ := Real.cos (2 * π * p.2.val / n)

/-- **The wave along the first ring is sharp.** For `m ≥ 2` it has sum zero and
`energy = gap m * ∑ rowWave²`. -/
theorem rowWave_sharp (hm : 2 ≤ m) :
    ∑ p, (rowWave : ZMod m × ZMod n → ℝ) p = 0 ∧
    energy (rowWave : ZMod m × ZMod n → ℝ) = gap m * ∑ p, (rowWave : ZMod m × ZMod n → ℝ) p ^ 2 := by
  obtain ⟨h0, h1⟩ := ring_wave (n := m) hm
  constructor
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [rowWave, h0, Finset.sum_const_zero]
  · rw [energy, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm,
      Finset.sum_comm (f := fun x y => (rowWave (x, y) : ℝ) ^ 2), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [rowWave, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero]
    exact h1

/-- **The wave along the second ring is sharp.** For `n ≥ 2` it has sum zero and
`energy = gap n * ∑ colWave²`. -/
theorem colWave_sharp (hn : 2 ≤ n) :
    ∑ p, (colWave : ZMod m × ZMod n → ℝ) p = 0 ∧
    energy (colWave : ZMod m × ZMod n → ℝ) = gap n * ∑ p, (colWave : ZMod m × ZMod n → ℝ) p ^ 2 := by
  obtain ⟨h0, h1⟩ := ring_wave (n := n) hn
  constructor
  · rw [Fintype.sum_prod_type]
    simp only [colWave, h0, Finset.sum_const_zero]
  · rw [energy, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [colWave, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_add]
    exact h1

/-- **The constant `min (gap m) (gap n)` cannot be improved.** For `m, n ≥ 2` there is a
nonzero `f` with sum zero and `energy f = min (gap m) (gap n) * ∑ f²`: the wave along the slower
ring. -/
theorem grid_gap_sharp (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ f : ZMod m × ZMod n → ℝ, ∑ p, f p = 0 ∧ f (0, 0) = 1 ∧
      energy f = min (gap m) (gap n) * ∑ p, f p ^ 2 := by
  rcases le_total (gap m) (gap n) with h | h
  · refine ⟨rowWave, (rowWave_sharp hm).1, by simp [rowWave], ?_⟩
    rw [min_eq_left h]
    exact (rowWave_sharp hm).2
  · refine ⟨colWave, (colWave_sharp hn).1, by simp [colWave], ?_⟩
    rw [min_eq_right h]
    exact (colWave_sharp hn).2

end RingGrid
