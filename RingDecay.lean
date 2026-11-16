import Wirtinger

/-!
# The heat flow on a ring settles to its mean

One step of the discrete heat flow on `ZMod n` with step size `t` is

  `heatStep t u j = u j + t * (u (j + 1) - 2 * u j + u (j - 1))`.

For `0 ≤ t ≤ 1/4` it keeps the mean (`mean_heatStep`), and the uneven part `u - mean u` loses
energy by at least the factor `(1 - t * gap n) ^ 2` each step (`energy_heatStep_le_mean`), where
`gap n = 2 - 2 cos (2π/n) = 4 sin² (π/n)` is the Wirtinger constant from `Wirtinger.lean`.
After `k` steps the factor is `((1 - t * gap n) ^ 2) ^ k` (`energy_iterate_le`), so for `n ≥ 2` and
`t > 0` every value goes to the mean (`iterate_tendsto_mean`). The wave `cos (2π j/n)` meets the
bound with equality (`energy_heatStep_wave`), so the rate is the best possible.

The proof works one Fourier coefficient at a time: the step multiplies the `k`-th coefficient by
`1 - t (2 - 2 cos (2π k/n))` (`fourier_heatStep`), and for `k ≠ 0` that number lies between
`0` and `1 - t * gap n`.
-/

open Finset ComplexConjugate
open scoped Real

namespace RingDecay

open CycleWirtinger hiding fourier

variable {n : ℕ} [NeZero n]

/-- One step of the discrete heat flow on the ring `ZMod n` with step size `t`. -/
noncomputable def heatStep (t : ℝ) (u : ZMod n → ℝ) (j : ZMod n) : ℝ :=
  u j + t * (u (j + 1) - 2 * u j + u (j - 1))

/-- The gap constant `2 - 2 cos (2π/n)`. -/
noncomputable def gap (n : ℕ) : ℝ := 2 - 2 * Real.cos (2 * π / n)

/-- Frequency `k` is damped by `2 - 2 cos (2π k/n)`. -/
noncomputable def mu (k : ZMod n) : ℝ := 2 - 2 * Real.cos (2 * π * k.val / n)

lemma gap_eq_four_sin_sq (n : ℕ) : gap n = 4 * Real.sin (π / n) ^ 2 := by
  have h := Real.cos_two_mul (π / n)
  have h2 : 2 * (π / n) = 2 * π / n := by ring
  rw [h2] at h
  have := Real.sin_sq_add_cos_sq (π / n)
  unfold gap
  nlinarith [h, this]

omit [NeZero n] in
lemma gap_pos (hn : 2 ≤ n) : 0 < gap n := by
  rw [gap_eq_four_sin_sq]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 : 0 < π / n := div_pos Real.pi_pos hnpos
  have h2 : π / n < π := by
    rw [div_lt_iff₀ hnpos]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  have := Real.sin_pos_of_pos_of_lt_pi h1 h2
  positivity

lemma gap_le_mu (k : ZMod n) (hk : k ≠ 0) : gap n ≤ mu k := by
  unfold gap mu
  have := cos_le k hk
  linarith

omit [NeZero n] in
lemma mu_le_four (k : ZMod n) : mu k ≤ 4 := by
  unfold mu
  have := Real.neg_one_le_cos (2 * π * k.val / n)
  linarith

lemma gap_le_four (n : ℕ) : gap n ≤ 4 := by
  unfold gap
  have := Real.neg_one_le_cos (2 * π / n)
  linarith

/-! ## Fourier side -/

lemma fourier_add_smul (a b : ZMod n → ℝ) (t : ℝ) (k : ZMod n) :
    CycleWirtinger.fourier (fun j => a j + t * b j) k = CycleWirtinger.fourier a k + (t : ℂ) * CycleWirtinger.fourier b k := by
  simp only [CycleWirtinger.fourier, Complex.ofReal_add, Complex.ofReal_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

lemma fourier_sub (a b : ZMod n → ℝ) (k : ZMod n) :
    CycleWirtinger.fourier (fun j => a j - b j) k = CycleWirtinger.fourier a k - CycleWirtinger.fourier b k := by
  simp only [CycleWirtinger.fourier, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]

lemma fourier_shift_back (g : ZMod n → ℝ) (k : ZMod n) :
    CycleWirtinger.fourier (fun j => g (j - 1)) k = ZMod.stdAddChar k * CycleWirtinger.fourier g k := by
  rw [CycleWirtinger.fourier, CycleWirtinger.fourier, Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun j => by
    simp only [Equiv.subRight_apply]
    rw [show j * k = k + (j - 1) * k by ring, AddChar.map_add_eq_mul]
    ring)

lemma e_mul_conj_sub (k : ZMod n) :
    (1 - ZMod.stdAddChar k) * (ZMod.stdAddChar (-k) - 1)
      = -((Complex.normSq (ZMod.stdAddChar k - 1) : ℝ) : ℂ) := by
  rw [← Complex.mul_conj, ← conj_e, map_sub, map_one]
  ring

/-- The heat step multiplies the `k`-th coefficient by `1 - t (2 - 2 cos (2π k/n))`. -/
lemma fourier_heatStep (t : ℝ) (u : ZMod n → ℝ) (k : ZMod n) :
    CycleWirtinger.fourier (heatStep t u) k = ((1 - t * mu k : ℝ) : ℂ) * CycleWirtinger.fourier u k := by
  set d : ZMod n → ℝ := fun j => u (j + 1) - u j with hd
  have hlap : (fun j => u (j + 1) - 2 * u j + u (j - 1)) = fun j => d j - d (j - 1) := by
    funext j
    simp only [hd, sub_add_cancel]
    ring
  have hfun : heatStep t u = fun j => u j + t * (d j - d (j - 1)) := by
    funext j
    rw [heatStep, ← congrFun hlap j]
  have hFd : CycleWirtinger.fourier d k = (ZMod.stdAddChar (-k) - 1) * CycleWirtinger.fourier u k := fourier_step u k
  rw [hfun, fourier_add_smul, fourier_sub d (fun j => d (j - 1)), fourier_shift_back, hFd]
  have he := e_mul_conj_sub k
  rw [normSq_e_sub_one] at he
  have : ((1 - t * mu k : ℝ) : ℂ) = 1 + (t : ℂ) * ((1 - ZMod.stdAddChar k) *
      (ZMod.stdAddChar (-k) - 1)) := by
    rw [he, mu]
    push_cast
    ring
  rw [this]
  ring

/-! ## Mean and constants -/

lemma sum_shift_add (u : ZMod n → ℝ) (a : ZMod n) : ∑ j, u (j + a) = ∑ j, u j :=
  Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)

lemma sum_shift_sub (u : ZMod n → ℝ) (a : ZMod n) : ∑ j, u (j - a) = ∑ j, u j :=
  Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)

/-- **The heat step keeps the total (hence the mean) unchanged.** -/
theorem sum_heatStep (t : ℝ) (u : ZMod n → ℝ) : ∑ j, heatStep t u j = ∑ j, u j := by
  simp only [heatStep, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [sum_shift_add, sum_shift_sub]
  ring

/-- The mean of `u`. -/
noncomputable def mean (u : ZMod n → ℝ) : ℝ := (∑ j, u j) / n

theorem mean_heatStep (t : ℝ) (u : ZMod n → ℝ) : mean (heatStep t u) = mean u := by
  rw [mean, mean, sum_heatStep]

omit [NeZero n] in
lemma heatStep_sub_const (t c : ℝ) (u : ZMod n → ℝ) (j : ZMod n) :
    heatStep t (fun i => u i - c) j = heatStep t u j - c := by
  simp only [heatStep]
  ring

lemma sum_sub_mean (u : ZMod n → ℝ) : ∑ j, (u j - mean u) = 0 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mean]
  field_simp
  ring

/-! ## One step -/

/-- **One step, mean zero.** For `0 ≤ t ≤ 1/4`, the energy shrinks by at least `(1 - t·gap)²`. -/
theorem energy_heatStep_le (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) (u : ZMod n → ℝ)
    (hmean : ∑ j, u j = 0) :
    ∑ j, heatStep t u j ^ 2 ≤ (1 - t * gap n) ^ 2 * ∑ j, u j ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hF0 : CycleWirtinger.fourier u 0 = 0 := by
    simp only [CycleWirtinger.fourier, mul_zero, AddChar.map_zero_eq_one, mul_one]
    exact_mod_cast hmean
  have hg := parseval_real (heatStep t u)
  have hf := parseval_real u
  have hterm : ∀ k, Complex.normSq (CycleWirtinger.fourier (heatStep t u) k)
      ≤ (1 - t * gap n) ^ 2 * Complex.normSq (CycleWirtinger.fourier u k) := by
    intro k
    rw [fourier_heatStep, Complex.normSq_mul, Complex.normSq_ofReal]
    by_cases hk : k = 0
    · simp [hk, hF0]
    · apply mul_le_mul_of_nonneg_right _ (Complex.normSq_nonneg _)
      have h1 := gap_le_mu k hk
      have h2 := mu_le_four k
      have ha : 0 ≤ 1 - t * mu k := by nlinarith
      have hb : 1 - t * mu k ≤ 1 - t * gap n := by nlinarith
      nlinarith
  have hsum : ∑ k, Complex.normSq (CycleWirtinger.fourier (heatStep t u) k)
      ≤ (1 - t * gap n) ^ 2 * ∑ k, Complex.normSq (CycleWirtinger.fourier u k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => hterm k)
  rw [hf, hg] at hsum
  have : (n : ℝ) * ∑ j, heatStep t u j ^ 2 ≤ (n : ℝ) * ((1 - t * gap n) ^ 2 * ∑ j, u j ^ 2) := by
    linarith
  exact le_of_mul_le_mul_left this hnpos

/-- **One step, any data.** The uneven part `u - mean u` shrinks by at least `(1 - t·gap)²`. -/
theorem energy_heatStep_le_mean (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) (u : ZMod n → ℝ) :
    ∑ j, (heatStep t u j - mean (heatStep t u)) ^ 2
      ≤ (1 - t * gap n) ^ 2 * ∑ j, (u j - mean u) ^ 2 := by
  have h := energy_heatStep_le t ht0 ht (fun i => u i - mean u) (sum_sub_mean u)
  simp only [heatStep_sub_const] at h
  rw [mean_heatStep]
  exact h

/-! ## Many steps -/

theorem mean_iterate (t : ℝ) (u : ZMod n → ℝ) (k : ℕ) :
    mean ((heatStep t)^[k] u) = mean u := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', mean_heatStep, ih]

/-- **After `k` steps** the uneven part is at most `((1 - t·gap)²)^k` times its start. -/
theorem energy_iterate_le (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) (u : ZMod n → ℝ) (k : ℕ) :
    ∑ j, ((heatStep t)^[k] u j - mean u) ^ 2
      ≤ ((1 - t * gap n) ^ 2) ^ k * ∑ j, (u j - mean u) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := energy_heatStep_le_mean t ht0 ht ((heatStep t)^[k] u)
    rw [mean_heatStep, mean_iterate] at h
    calc ∑ j, (heatStep t ((heatStep t)^[k] u) j - mean u) ^ 2
        ≤ (1 - t * gap n) ^ 2 * ∑ j, ((heatStep t)^[k] u j - mean u) ^ 2 := h
      _ ≤ (1 - t * gap n) ^ 2 * (((1 - t * gap n) ^ 2) ^ k * ∑ j, (u j - mean u) ^ 2) :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = ((1 - t * gap n) ^ 2) ^ (k + 1) * ∑ j, (u j - mean u) ^ 2 := by ring

omit [NeZero n] in
/-- The factor is strictly below one when `n ≥ 2` and `0 < t ≤ 1/4`. -/
lemma factor_lt_one (hn : 2 ≤ n) (t : ℝ) (ht0 : 0 < t) (ht : t ≤ 1 / 4) :
    0 ≤ (1 - t * gap n) ^ 2 ∧ (1 - t * gap n) ^ 2 < 1 := by
  have hg := gap_pos (n := n) hn
  have hg4 := gap_le_four n
  have ha : 0 ≤ 1 - t * gap n := by nlinarith
  have hb : 1 - t * gap n < 1 := by nlinarith
  exact ⟨sq_nonneg _, by nlinarith⟩

/-- **The uneven part goes to zero.** -/
theorem energy_tendsto_zero (hn : 2 ≤ n) (t : ℝ) (ht0 : 0 < t) (ht : t ≤ 1 / 4)
    (u : ZMod n → ℝ) :
    Filter.Tendsto (fun k => ∑ j, ((heatStep t)^[k] u j - mean u) ^ 2)
      Filter.atTop (nhds 0) := by
  obtain ⟨h0, h1⟩ := factor_lt_one hn t ht0 ht
  have hlim : Filter.Tendsto (fun k : ℕ => ((1 - t * gap n) ^ 2) ^ k * ∑ j, (u j - mean u) ^ 2)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const
      (∑ j, (u j - mean u) ^ 2)
  refine squeeze_zero (fun k => ?_) (fun k => energy_iterate_le t ht0.le ht u k) hlim
  exact Finset.sum_nonneg (fun j _ => sq_nonneg _)

/-- **Every value settles to the mean.** -/
theorem iterate_tendsto_mean (hn : 2 ≤ n) (t : ℝ) (ht0 : 0 < t) (ht : t ≤ 1 / 4)
    (u : ZMod n → ℝ) (j : ZMod n) :
    Filter.Tendsto (fun k => (heatStep t)^[k] u j) Filter.atTop (nhds (mean u)) := by
  have hE := energy_tendsto_zero hn t ht0 ht u
  have hsq : Filter.Tendsto (fun k => ((heatStep t)^[k] u j - mean u) ^ 2)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun k => sq_nonneg _) (fun k => ?_) hE
    exact Finset.single_le_sum (f := fun i => ((heatStep t)^[k] u i - mean u) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  have habs : Filter.Tendsto (fun k => |(heatStep t)^[k] u j - mean u|)
      Filter.atTop (nhds 0) := by
    have := hsq.sqrt
    simpa [Real.sqrt_sq_eq_abs] using this
  have hd : Filter.Tendsto (fun k => (heatStep t)^[k] u j - mean u) Filter.atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  simpa using hd.add_const (mean u)

/-! ## The rate cannot be improved -/

/-- **The slowest wave.** For `n ≥ 2`, the wave `cos (2π j/n)` is only scaled by the heat step,
by exactly `1 - t·gap`. -/
theorem heatStep_wave (hn : 2 ≤ n) (t : ℝ) :
    heatStep t (fun j : ZMod n => Real.cos (2 * π * j.val / n))
      = fun j => (1 - t * gap n) * Real.cos (2 * π * j.val / n) := by
  have : Fact (1 < n) := ⟨by omega⟩
  have hre : ∀ j : ZMod n, Real.cos (2 * π * j.val / n) = (ZMod.stdAddChar j).re := by
    intro j
    rw [e_eq_exp, Complex.exp_ofReal_mul_I_re]
  have h1 : (ZMod.stdAddChar (1 : ZMod n)).re = Real.cos (2 * π / n) := by
    rw [← hre, ZMod.val_one, Nat.cast_one, mul_one]
  funext j
  simp only [heatStep, hre]
  rw [sub_eq_add_neg j 1, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, ← conj_e,
    Complex.mul_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, h1, gap]
  ring

/-- For the slowest wave the one-step bound is an equality, so `(1 - t·gap)²` is the true rate. -/
theorem energy_heatStep_wave (hn : 2 ≤ n) (t : ℝ) :
    ∑ j : ZMod n, heatStep t (fun i : ZMod n => Real.cos (2 * π * i.val / n)) j ^ 2
      = (1 - t * gap n) ^ 2 * ∑ j : ZMod n, Real.cos (2 * π * j.val / n) ^ 2 := by
  rw [heatStep_wave hn t, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

end RingDecay
