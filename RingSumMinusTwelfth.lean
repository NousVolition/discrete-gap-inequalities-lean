import RingDecay

/-!
# Ring sum and the value −1/12

Results behind the "Ring Sum & −1/12 Spectral Explorer" tab.

* `bar_sum_eq_two_cot`: for `n ≥ 1`, the bars `2 sin(πk/n)`, `k = 1, …, n − 1`, add up to
  exactly `2 cot(π/(2n))`.
* `cot_sub_inv_div_tendsto`: `(cot x − 1/x)/x → −1/3` as `x → 0⁺`.
* `ring_leftover_tendsto`: `(2 cot(π/(2n)) − 4n/π) · n/(4π) → −1/12` as `n → ∞`.
* `staircase_hasSum`, `staircase_tsum`: `∑ n e^{−εn} = e^{−ε}/(1 − e^{−ε})²` for `ε > 0`.
* `staircase_leftover_tendsto`: that sum minus `1/ε²` tends to `−1/12` as `ε → 0⁺`.
* `two_cot_pi_div_48_bounds`: `30.51405 < 2 cot(π/48) < 30.51415`, the bar total at `n = 24`.
* Link to `RingDecay`: each bar squared is a ring Laplacian eigenvalue, `(2 sin(πk/n))² = μ_k`,
  and the first bar squared is the spectral gap.
-/

open Real Filter Topology Finset

namespace RingSumMinusTwelfth

/-! ## Exact bar total -/

/-- One step of the telescoping sum. -/
lemma two_sin_mul_sin_step (b : ℝ) (m : ℕ) :
    2 * sin (2 * ((m : ℝ) + 1) * b) * sin b =
      cos ((2 * (m : ℝ) + 1) * b) - cos ((2 * ((m : ℝ) + 1) + 1) * b) := by
  have h1 : (2 * (m : ℝ) + 1) * b = 2 * ((m : ℝ) + 1) * b - b := by ring
  have h2 : (2 * ((m : ℝ) + 1) + 1) * b = 2 * ((m : ℝ) + 1) * b + b := by ring
  rw [h1, h2, cos_sub, cos_add]
  ring

/-- Telescoping: `(∑_{k<m} 2 sin(2(k+1)b)) · sin b = cos b − cos((2m+1)b)`. -/
lemma sum_two_sin_mul_sin (b : ℝ) (m : ℕ) :
    (∑ k ∈ range m, 2 * sin (2 * ((k : ℝ) + 1) * b)) * sin b =
      cos b - cos ((2 * (m : ℝ) + 1) * b) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, add_mul, ih, two_sin_mul_sin_step]
    push_cast
    ring

/-- The bars `2 sin(πk/n)` for `k = 1, …, n − 1` add up to exactly `2 cot(π/(2n))`. -/
theorem bar_sum_eq_two_cot (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Ico 1 n, 2 * sin (π * k / n) = 2 * cot (π / (2 * n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set b : ℝ := π / (2 * n) with hb
  have hb0 : 0 < b := by positivity
  have hbpi : b < π := by
    rw [hb, div_lt_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [pi_pos]
  have hsin : 0 < sin b := sin_pos_of_pos_of_lt_pi hb0 hbpi
  have hterm : ∀ k ∈ range (n - 1),
      2 * sin (π * ((1 + k : ℕ) : ℝ) / n) = 2 * sin (2 * ((k : ℝ) + 1) * b) := by
    intro k _
    congr 2
    rw [hb]; push_cast
    field_simp
    ring
  rw [sum_Ico_eq_sum_range, sum_congr rfl hterm]
  have htel := sum_two_sin_mul_sin b (n - 1)
  have hlast : (2 * ((n - 1 : ℕ) : ℝ) + 1) * b = π - b := by
    rw [Nat.cast_sub hn, hb]; push_cast
    field_simp
    ring
  rw [hlast, cos_pi_sub] at htel
  rw [cot_eq_cos_div_sin, ← mul_div_assoc, eq_div_iff hsin.ne']
  linarith


/-! ## Cotangent near zero -/

/-- `cos x ≤ 1 − x²/2 + x⁴/24` for `0 ≤ x ≤ 1`. -/
lemma cos_le_quartic {x : ℝ} (hx0 : 0 ≤ x) :
    cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have hh : x = 2 * (x / 2) := by ring
  have hs := sin_ge_sub_cube (show 0 ≤ x / 2 by positivity)
  have hc : cos x = 1 - 2 * sin (x / 2) ^ 2 := by
    rw [hh, cos_two_mul]
    have := sin_sq_add_cos_sq (x / 2)
    rw [show 2 * (x / 2) / 2 = x / 2 by ring]
    linarith
  rw [hc]
  by_cases hsmall : 0 ≤ x / 2 - (x / 2) ^ 3 / 6
  · have := mul_le_mul hs hs hsmall (le_trans hsmall hs)
    nlinarith [pow_nonneg hx0 6]
  · -- large `x`: the right side is at least `1/2 − 1 + …`; use `sin² ≥ 0` and the quartic
    push Not at hsmall
    have hx2 : 12 < x ^ 2 := by nlinarith
    nlinarith [sq_nonneg (sin (x / 2)), sin_sq_le_one (x / 2), sq_nonneg (x ^ 2 - 6)]

/-- Upper bound: `cot x ≤ 1/x − x/3` for `0 < x ≤ 1`. -/
lemma cot_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : cot x ≤ 1 / x - x / 3 := by
  have hs : 0 < sin x := sin_pos_of_pos_of_lt_pi hx (by linarith [pi_gt_three])
  have hsl := sin_ge_sub_cube hx.le
  have hcu := cos_le_quartic hx.le
  have h3 : 0 ≤ 3 - x ^ 2 := by nlinarith
  have key : 3 * x * cos x ≤ (3 - x ^ 2) * sin x := by
    have a := mul_le_mul_of_nonneg_left hcu (show 0 ≤ 3 * x by positivity)
    have b := mul_le_mul_of_nonneg_left hsl h3
    nlinarith [pow_pos hx 5]
  rw [cot_eq_cos_div_sin, div_le_iff₀ hs,
    show (1 / x - x / 3) * sin x = (3 - x ^ 2) * sin x / (3 * x) by field_simp,
    le_div_iff₀ (by positivity)]
  linarith

/-- Lower bound: `1/x − x/3 − x³/12 ≤ cot x` for `0 < x ≤ 1`. -/
lemma le_cot {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : 1 / x - x / 3 - x ^ 3 / 12 ≤ cot x := by
  have hs : 0 < sin x := sin_pos_of_pos_of_lt_pi hx (by linarith [pi_gt_three])
  have hsu : sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 100 := by
    have := Real.sin_bound (show |x| ≤ 1 by rw [abs_of_pos hx]; exact hx1)
    rw [abs_of_pos hx] at this
    linarith [le_abs_self (sin x - (x - x ^ 3 / 6))]
  have hcl : 1 - x ^ 2 / 2 ≤ cos x := one_sub_sq_div_two_le_cos
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  set Q : ℝ := 1 - x ^ 2 / 3 - x ^ 4 / 12 with hQ
  have hQ0 : 0 ≤ Q := by nlinarith [pow_le_one₀ hx.le hx1 (n := 4)]
  have h1 := mul_le_mul_of_nonneg_left hsu hQ0
  have h2 := mul_le_mul_of_nonneg_left hcl hx.le
  have hp : 0 ≤ x ^ 5 * (4 / 225 - 19 * x ^ 2 / 1800 + x ^ 4 / 1200) :=
    mul_nonneg (pow_pos hx 5).le (by nlinarith [pow_nonneg hx.le 4])
  have key : Q * sin x ≤ x * cos x := by
    rw [hQ] at h1 ⊢
    nlinarith
  rw [cot_eq_cos_div_sin, le_div_iff₀ hs,
    show (1 / x - x / 3 - x ^ 3 / 12) * sin x = Q * sin x / x by rw [hQ]; field_simp,
    div_le_iff₀ hx]
  linarith

/-- For `0 < x ≤ 1`, `(cot x − 1/x)/x` lies in `[−1/3 − x²/12, −1/3]`. -/
lemma cot_sub_inv_div_bounds {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    -1 / 3 - x ^ 2 / 12 ≤ (cot x - 1 / x) / x ∧ (cot x - 1 / x) / x ≤ -1 / 3 := by
  have hu := cot_le hx hx1
  have hl := le_cot hx hx1
  constructor
  · rw [le_div_iff₀ hx]; nlinarith
  · rw [div_le_iff₀ hx]; nlinarith

/-- A function within `C t²` of `L` on `(0, 1]` tends to `L` as `t → 0⁺`. -/
lemma tendsto_of_sq_bound {g : ℝ → ℝ} {L C : ℝ}
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → |g t - L| ≤ C * t ^ 2) :
    Tendsto g (𝓝[>] 0) (𝓝 L) := by
  have h0 : Tendsto (fun t : ℝ => C * t ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => C * t ^ 2) (𝓝 0) (𝓝 (C * 0 ^ 2)) :=
      ((continuous_const.mul (continuous_pow 2)).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with t ht
  rw [Real.norm_eq_abs]
  exact h t ht.1 ht.2.le

/-- `(cot x − 1/x)/x → −1/3` as `x → 0⁺`. -/
theorem cot_sub_inv_div_tendsto :
    Tendsto (fun x : ℝ => (cot x - 1 / x) / x) (𝓝[>] 0) (𝓝 (-1 / 3)) := by
  refine tendsto_of_sq_bound (C := 1 / 12) fun x hx hx1 => ?_
  obtain ⟨h1, h2⟩ := cot_sub_inv_div_bounds hx hx1
  rw [abs_le]; constructor <;> linarith

/-! ## Ring leftover -/

/-- The scaled leftover shown on the page: `(bar total − 4n/π) · n/(4π)`,
with the bar total written as `2 cot(π/(2n))`. -/
noncomputable def ringLeftover (n : ℕ) : ℝ :=
  (2 * cot (π / (2 * n)) - 4 * n / π) * n / (4 * π)

/-- The ring leftover is a quarter of `(cot x − 1/x)/x` at `x = π/(2n)`. -/
lemma ringLeftover_eq (n : ℕ) (hn : 1 ≤ n) :
    ringLeftover n = (cot (π / (2 * n)) - 1 / (π / (2 * n))) / (π / (2 * n)) / 4 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hpi : π ≠ 0 := pi_ne_zero
  unfold ringLeftover
  field_simp
  ring

/-- For `n ≥ 2` the ring leftover lies in `[−1/12 − (π/(2n))²/48, −1/12]`,
so it approaches `−1/12` from below. -/
theorem ringLeftover_bounds (n : ℕ) (hn : 2 ≤ n) :
    -1 / 12 - (π / (2 * n)) ^ 2 / 48 ≤ ringLeftover n ∧ ringLeftover n ≤ -1 / 12 := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hx : 0 < π / (2 * n) := by positivity
  have hx1 : π / (2 * n) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [pi_lt_four]
  obtain ⟨h1, h2⟩ := cot_sub_inv_div_bounds hx hx1
  rw [ringLeftover_eq n (by omega)]
  constructor <;> linarith

/-- The ring leftover tends to `−1/12` as `n → ∞`. -/
theorem ring_leftover_tendsto : Tendsto ringLeftover atTop (𝓝 (-1 / 12)) := by
  have hx : Tendsto (fun n : ℕ => (π / 2 / n) ^ 2 / 48) atTop (𝓝 0) := by
    simpa using ((tendsto_const_div_atTop_nhds_zero_nat (π / 2)).pow 2).div_const 48
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hx
  filter_upwards [eventually_ge_atTop 2] with n hn
  obtain ⟨h1, h2⟩ := ringLeftover_bounds n hn
  rw [Real.norm_eq_abs, abs_le, div_div]
  constructor <;> linarith

/-! ## Numeric check at `n = 24` -/

/-- The bar total at `n = 24` is `2 cot(π/48)`, and `30.51405 < 2 cot(π/48) < 30.51415`;
to four decimals it is `30.5141`. -/
theorem two_cot_pi_div_48_bounds :
    30.51405 < 2 * cot (π / 48) ∧ 2 * cot (π / 48) < 30.51415 := by
  have hx : 0 < π / 48 := by positivity
  have hx1 : π / 48 ≤ 1 := by linarith [pi_lt_four]
  have hu := cot_le hx hx1
  have hl := le_cot hx hx1
  have hp1 := pi_gt_d6
  have hp2 := pi_lt_d6
  have hpos := pi_pos
  constructor
  · have : (30.51405 : ℝ) < 2 * (1 / (π / 48) - π / 48 / 3 - (π / 48) ^ 3 / 12) := by
      rw [show 2 * (1 / (π / 48) - π / 48 / 3 - (π / 48) ^ 3 / 12)
          = (96 - π ^ 2 / 72 - π ^ 4 / 663552) / π by field_simp; ring, lt_div_iff₀ hpos]
      nlinarith [mul_pos hpos hpos, pow_pos hpos 3]
    linarith
  · have : 2 * (1 / (π / 48) - π / 48 / 3) < (30.51415 : ℝ) := by
      rw [show 2 * (1 / (π / 48) - π / 48 / 3) = (96 - π ^ 2 / 72) / π by field_simp; ring,
        div_lt_iff₀ hpos]
      nlinarith [mul_pos hpos hpos]
    linarith

/-- With `n = 24`, the exact bar total is `2 cot(π/48)`. -/
theorem bar_sum_24 :
    ∑ k ∈ Ico (1 : ℕ) 24, 2 * sin (π * (k : ℝ) / 24) = 2 * cot (π / 48) := by
  have h := bar_sum_eq_two_cot 24 (by norm_num)
  push_cast at h
  rw [h]
  norm_num

/-! ## Staircase -/

/-- `∑ n e^{−εn} = e^{−ε}/(1 − e^{−ε})²` for `ε > 0`. -/
theorem staircase_hasSum {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun n : ℕ => (n : ℝ) * exp (-(ε * n))) (exp (-ε) / (1 - exp (-ε)) ^ 2) := by
  have hr : ‖exp (-ε)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have e : (fun n : ℕ => (n : ℝ) * exp (-(ε * n))) = fun n : ℕ => (n : ℝ) * exp (-ε) ^ n := by
    funext n
    rw [← Real.exp_nat_mul]
    ring_nf
  rw [e]
  exact hasSum_coe_mul_geometric_of_norm_lt_one hr

/-- The same value as a `tsum`. -/
theorem staircase_tsum {ε : ℝ} (hε : 0 < ε) :
    ∑' n : ℕ, (n : ℝ) * exp (-(ε * n)) = exp (-ε) / (1 - exp (-ε)) ^ 2 :=
  (staircase_hasSum hε).tsum_eq

/-- The staircase leftover: the smooth sum minus its growth term `1/ε²`. -/
noncomputable def staircaseLeftover (ε : ℝ) : ℝ :=
  exp (-ε) / (1 - exp (-ε)) ^ 2 - 1 / ε ^ 2

/-- The algebra behind the staircase bound, with `q = e^t`. -/
lemma leftover_alg {q t : ℝ} (hq : 0 < q) (hq1 : 0 < q - 1) (ht : 0 < t) :
    q⁻¹ / (1 - q⁻¹) ^ 2 - 1 / t ^ 2 - (-1 / 12) =
      (12 * (q * t ^ 2 - (q - 1) ^ 2) + t ^ 2 * (q - 1) ^ 2) / (12 * t ^ 2 * (q - 1) ^ 2) := by
  have h1 : 1 - q⁻¹ = (q - 1) / q := by field_simp
  have h2 : q⁻¹ / (1 - q⁻¹) ^ 2 = q / (q - 1) ^ 2 := by
    rw [h1, div_pow, div_div_eq_mul_div]
    field_simp
  rw [h2, eq_div_iff (by positivity)]
  field_simp
  ring

/-- The polynomial bound behind the staircase estimate: if `|r| ≤ t⁵/100` and `0 < t ≤ 1`,
then `12(qt² − (q−1)²) + t²(q−1)² ≤ t⁶` in absolute value, where
`q = 1 + t + t²/2 + t³/6 + t⁴/24 + r`. -/
lemma staircase_poly_bound {t r : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hrb : |r| ≤ t ^ 5 / 100) :
    |12 * ((1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + r) * t ^ 2
        - (1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + r - 1) ^ 2)
      + t ^ 2 * (1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + r - 1) ^ 2| ≤ t ^ 6 := by
  have hp : ∀ k : ℕ, 6 ≤ k → t ^ k ≤ t ^ 6 := fun k hk =>
    pow_le_pow_of_le_one ht.le ht1 hk
  have hp1 : ∀ k : ℕ, 1 ≤ k → t ^ k ≤ t := fun k hk => by
    simpa using pow_le_pow_of_le_one ht.le ht1 hk
  have hMexp : 12 * ((1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + r) * t ^ 2
        - (1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + r - 1) ^ 2)
      + t ^ 2 * (1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + r - 1) ^ 2
      = r ^ 2 * (t ^ 2 - 12) + r * (t ^ 6 / 12 + t ^ 5 / 3 - 2 * t ^ 3 - 24 * t)
      + (t ^ 10 / 576 + t ^ 9 / 72 + 7 * t ^ 8 / 144 + t ^ 7 / 12 + t ^ 6 / 4) := by
    ring
  have hr2 : r ^ 2 ≤ t ^ 6 / 10000 := by
    have h1 : r ^ 2 ≤ (t ^ 5 / 100) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg r) hrb 2
    have h2 := hp 10 (by norm_num)
    have h3 : (t ^ 5 / 100) ^ 2 = t ^ 10 / 10000 := by ring
    linarith
  have hA : |r ^ 2 * (t ^ 2 - 12)| ≤ 12 * (t ^ 6 / 10000) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg r)]
    have h2 := hp1 2 (by norm_num)
    have : |t ^ 2 - 12| ≤ 12 := by
      rw [abs_le]; constructor <;> linarith [sq_nonneg t]
    calc r ^ 2 * |t ^ 2 - 12| ≤ (t ^ 6 / 10000) * 12 :=
          mul_le_mul hr2 this (abs_nonneg _) (by positivity)
      _ = 12 * (t ^ 6 / 10000) := by ring
  have hB : |r * (t ^ 6 / 12 + t ^ 5 / 3 - 2 * t ^ 3 - 24 * t)| ≤ t ^ 5 / 100 * (27 * t) := by
    rw [abs_mul]
    have : |t ^ 6 / 12 + t ^ 5 / 3 - 2 * t ^ 3 - 24 * t| ≤ 27 * t := by
      have := hp1 6 (by norm_num); have := hp1 5 (by norm_num); have := hp1 3 (by norm_num)
      rw [abs_le]; constructor <;> linarith [pow_pos ht 6, pow_pos ht 5, pow_pos ht 3]
    exact mul_le_mul hrb this (abs_nonneg _) (by positivity)
  have hC : |t ^ 10 / 576 + t ^ 9 / 72 + 7 * t ^ 8 / 144 + t ^ 7 / 12 + t ^ 6 / 4|
      ≤ t ^ 6 / 2 := by
    have := hp 10 (by norm_num); have := hp 9 (by norm_num)
    have := hp 8 (by norm_num); have := hp 7 (by norm_num)
    rw [abs_of_nonneg (by positivity)]
    linarith [pow_pos ht 6]
  rw [hMexp]
  have h6 : t ^ 5 / 100 * (27 * t) = 27 / 100 * t ^ 6 := by ring
  calc _ ≤ |r ^ 2 * (t ^ 2 - 12)| + |r * (t ^ 6 / 12 + t ^ 5 / 3 - 2 * t ^ 3 - 24 * t)|
        + |t ^ 10 / 576 + t ^ 9 / 72 + 7 * t ^ 8 / 144 + t ^ 7 / 12 + t ^ 6 / 4| :=
        abs_add_three _ _ _
    _ ≤ t ^ 6 := by linarith [pow_pos ht 6]

/-- `|e^t − (1 + t + t²/2 + t³/6 + t⁴/24)| ≤ t⁵/100` for `0 < t ≤ 1`. -/
lemma exp_quartic_bound {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |exp t - (1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24)| ≤ t ^ 5 / 100 := by
  have := Real.exp_bound (show |t| ≤ 1 by rw [abs_of_pos ht]; exact ht1) (n := 5) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at this
  rw [abs_of_pos ht] at this
  convert this using 2 <;> norm_num
  ring

/-- For `0 < t ≤ 1`, `|staircaseLeftover t + 1/12| ≤ t²/12`. -/
lemma staircaseLeftover_bound {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |staircaseLeftover t - (-1 / 12)| ≤ 1 / 12 * t ^ 2 := by
  have hq1 : t + 1 ≤ exp t := add_one_le_exp t
  have hMb := staircase_poly_bound ht ht1 (exp_quartic_bound ht ht1)
  generalize hr : exp t - (1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24) = r at hMb
  have hqr : exp t = 1 + t + t ^ 2 / 2 + t ^ 3 / 6 + t ^ 4 / 24 + r := by linarith
  rw [← hqr] at hMb
  have hident : staircaseLeftover t - (-1 / 12) =
      (12 * (exp t * t ^ 2 - (exp t - 1) ^ 2) + t ^ 2 * (exp t - 1) ^ 2)
        / (12 * t ^ 2 * (exp t - 1) ^ 2) := by
    unfold staircaseLeftover
    rw [exp_neg]
    exact leftover_alg (exp_pos t) (by linarith) ht
  generalize exp t = q at hMb hident hq1
  have hqt : t ≤ q - 1 := by linarith
  have hqm : 0 < q - 1 := by linarith
  have hden : (0 : ℝ) < 12 * t ^ 2 * (q - 1) ^ 2 := by positivity
  rw [hident, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have hsq : t ^ 2 ≤ (q - 1) ^ 2 := pow_le_pow_left₀ ht.le hqt 2
  have h4 : t ^ 6 ≤ t ^ 4 * (q - 1) ^ 2 :=
    calc t ^ 6 = t ^ 4 * t ^ 2 := by ring
      _ ≤ t ^ 4 * (q - 1) ^ 2 := mul_le_mul_of_nonneg_left hsq (pow_pos ht 4).le
  have e : 1 / 12 * t ^ 2 * (12 * t ^ 2 * (q - 1) ^ 2) = t ^ 4 * (q - 1) ^ 2 := by ring
  rw [e]
  linarith

/-- The staircase leftover tends to `−1/12` as `ε → 0⁺`. -/
theorem staircase_leftover_tendsto :
    Tendsto staircaseLeftover (𝓝[>] 0) (𝓝 (-1 / 12)) :=
  tendsto_of_sq_bound fun _ ht ht1 => staircaseLeftover_bound ht ht1

/-! ## Link to `RingDecay`

`RingDecay` studies the heat step on the ring `ZMod n`, whose Fourier modes decay with
`μ_k = 2 − 2 cos(2πk/n)`; its spectral gap is `gap n = μ_1`. Each bar on this tab is the
square root of one of these eigenvalues: `2 sin(πk/n) = √μ_k`. So the bar total is the sum of
the square roots of the ring Laplacian eigenvalues, and the first bar squared is the gap. -/

/-- The spectral gap of `RingDecay` is the square of the first bar, `(2 sin(π/n))²`. -/
theorem gap_eq_first_bar_sq (n : ℕ) :
    RingDecay.gap n = (2 * sin (π * ((1 : ℕ) : ℝ) / n)) ^ 2 := by
  rw [RingDecay.gap_eq_four_sin_sq]
  push_cast
  rw [mul_one]
  ring

/-- Each ring Laplacian eigenvalue is the square of a bar: `μ_k = (2 sin(πk/n))²`. -/
theorem mu_eq_bar_sq {n : ℕ} [NeZero n] (k : ZMod n) :
    RingDecay.mu k = (2 * sin (π * k.val / n)) ^ 2 := by
  unfold RingDecay.mu
  rw [show 2 * π * (k.val : ℝ) / n = 2 * (π * k.val / n) by ring, cos_two_mul]
  linear_combination (-4) * sin_sq_add_cos_sq (π * k.val / n)

/-- Each bar is the square root of a ring Laplacian eigenvalue: `2 sin(πk/n) = √μ_k`. -/
theorem bar_eq_sqrt_mu {n : ℕ} [NeZero n] (k : ZMod n) :
    2 * sin (π * k.val / n) = √(RingDecay.mu k) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hk : (k.val : ℝ) ≤ n := by exact_mod_cast (ZMod.val_lt k).le
  have hs : 0 ≤ sin (π * k.val / n) := by
    apply sin_nonneg_of_nonneg_of_le_pi (by positivity)
    rw [div_le_iff₀ hn]
    nlinarith [pi_pos]
  rw [mu_eq_bar_sq, Real.sqrt_sq (by linarith)]

/-- The bar total is the sum of the square roots of all ring Laplacian eigenvalues
(the `k = 0` term is zero): `∑_k √μ_k = 2 cot(π/(2n))`. -/
theorem sum_sqrt_mu_eq_two_cot (n : ℕ) [NeZero n] :
    ∑ k : ZMod n, √(RingDecay.mu k) = 2 * cot (π / (2 * n)) := by
  have hn : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [← bar_sum_eq_two_cot n hn]
  simp_rw [← bar_eq_sqrt_mu]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show (∑ k : ZMod (m + 1), 2 * sin (π * (k.val : ℝ) / ((m + 1 : ℕ) : ℝ)))
      = ∑ k : Fin (m + 1), 2 * sin (π * ((k : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)) from rfl,
    Fin.sum_univ_eq_sum_range (fun k : ℕ => 2 * sin (π * (k : ℝ) / ((m + 1 : ℕ) : ℝ))),
    sum_range_succ', sum_Ico_eq_sum_range]
  simp [add_comm]

end RingSumMinusTwelfth
