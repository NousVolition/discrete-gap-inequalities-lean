import Mathlib

/-!
# The gap: what holds the past finite

A store adds up an input `u` over time. It either keeps everything (no way out) or lets go at a
rate `r > 0` (a gap). The results:

* **No gap, finite only if nothing comes in.** A store with no way out and a steady input grows
  without bound (`keep_unbounded`).
* **Gap, always finite.** With `r > 0` it never moves further from `u / r` than it started
  (`breathe_levels`, `breathe_bounded`).
* **Exactly one of the two.** With a steady input, a store stays finite exactly when it has a gap
  (`finite_iff_gap`).
* **Each store without a way out adds one power of time.** A row of `k + 1` such stores fed a
  constant `c` holds `c t^(k+1)/(k+1)!` at the end (`chain_store_deriv`).
* **A gap beats every power.** `exp(-r t)` falls faster than `(1 + t)^(-K)` for every `K`
  (`gap_beats_every_power`), which is the shape of the decay the forced Navier-Stokes problem asks
  of its force, and of the clustering a Yang-Mills mass gap gives. Fading only like a power fails
  that test (`power_decay_fails_rule`).
* **Input ended versus input continuing.** With the input ended the store fades like `exp(-r t)`
  (`input_ended`); with a steady input it sits at `u / r` and does not fade (`steady_input_stays`).
* **The breath out.** Letting go at rate `log (5/4)` keeps exactly `4/5` per breath of length 1,
  and that rate is a gap (`breath_keeps_four_fifths`, `breath_out_is_a_gap`).
-/

noncomputable section

namespace HugGap

/-- The derivative of `s ↦ c * s`. -/
theorem lin_deriv (c t : ℝ) : HasDerivAt (fun s : ℝ => c * s) c t := by
  first
  | simpa using (hasDerivAt_id t).const_mul c
  | simpa using (hasDerivAt_id' (x := t)).const_mul c

/-! ## 1. A store with no way out -/

/-- A store that adds up a steady input `u` and keeps all of it. -/
def keep (u x0 t : ℝ) : ℝ := x0 + u * t

/-- It changes at exactly the input rate. -/
theorem keep_deriv (u x0 t : ℝ) : HasDerivAt (keep u x0) u t := by
  have h := (lin_deriv u t).const_add x0
  convert h using 1 <;> first | rfl | (funext s; simp only [keep])

/-- With any steady positive input, it passes every bound. -/
theorem keep_unbounded (u x0 : ℝ) (hu : 0 < u) (M : ℝ) :
    ∃ t, 0 ≤ t ∧ M < keep u x0 t := by
  refine ⟨|M - x0| / u + 1, add_nonneg (div_nonneg (abs_nonneg _) hu.le) zero_le_one, ?_⟩
  have h1 : u * (|M - x0| / u + 1) = |M - x0| + u := by
    rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hu), mul_one]
  have h2 : M - x0 ≤ |M - x0| := le_abs_self _
  show M < x0 + u * (|M - x0| / u + 1)
  rw [h1]
  linarith

/-! ## 2. A store with a gap -/

/-- A store that adds up `u` and lets go at rate `r`. -/
def breathe (r u x0 t : ℝ) : ℝ := u / r + (x0 - u / r) * Real.exp (-r * t)

/-- It changes at the input rate minus `r` times what it holds. -/
theorem breathe_deriv (r u x0 t : ℝ) (hr : r ≠ 0) :
    HasDerivAt (breathe r u x0) (u - r * breathe r u x0 t) t := by
  have h := (((lin_deriv (-r) t).exp).const_mul (x0 - u / r)).const_add (u / r)
  have h' : r * (u / r) = u := mul_div_cancel₀ u hr
  convert h using 1 <;> first | rfl | (simp only [breathe]; linear_combination (-1 : ℝ) * h')

/-- With a gap it never moves further from `u / r` than it started. -/
theorem breathe_levels (r u x0 t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    |breathe r u x0 t - u / r| ≤ |x0 - u / r| := by
  have e1 : breathe r u x0 t - u / r = (x0 - u / r) * Real.exp (-r * t) := by
    simp only [breathe]
    ring
  have h1 : Real.exp (-r * t) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hr ht])
  rw [e1, abs_mul, abs_of_pos (Real.exp_pos (-r * t))]
  exact mul_le_of_le_one_right (abs_nonneg _) h1

/-- With a gap it stays finite for all time. -/
theorem breathe_bounded (r u x0 : ℝ) (hr : 0 < r) :
    ∃ M, ∀ t, 0 ≤ t → |breathe r u x0 t| ≤ M := by
  refine ⟨|u / r| + |x0 - u / r|, fun t ht => ?_⟩
  have h := abs_le.mp (breathe_levels r u x0 t hr.le ht)
  have hq := abs_le.mp (le_refl |u / r|)
  rw [abs_le]
  constructor <;> linarith [h.1, h.2, hq.1, hq.2]

/-! ## 3. Finite exactly when there is a gap -/

/-- One store, with or without a way out. -/
def store (r u x0 t : ℝ) : ℝ := if r = 0 then keep u x0 t else breathe r u x0 t

/-- With a steady positive input, a store that holds the past stays finite exactly when it
has a gap. -/
theorem finite_iff_gap (r u x0 : ℝ) (hr : 0 ≤ r) (hu : 0 < u) :
    (∃ M, ∀ t, 0 ≤ t → |store r u x0 t| ≤ M) ↔ 0 < r := by
  constructor
  · rintro ⟨M, hM⟩
    by_contra h
    have h0 : r = 0 := le_antisymm (not_lt.mp h) hr
    obtain ⟨t, ht, hlt⟩ := keep_unbounded u x0 hu M
    have hb := hM t ht
    rw [store, if_pos h0] at hb
    have hs := le_abs_self (keep u x0 t)
    linarith
  · intro h
    obtain ⟨M, hM⟩ := breathe_bounded r u x0 h
    refine ⟨M, fun t ht => ?_⟩
    rw [store, if_neg h.ne']
    exact hM t ht

/-! ## 4. Each store without a way out adds one power of time -/

/-- The `(k+1)`-th store in a row, fed a constant `c`, holds `c t^(k+1)/(k+1)!`: it changes at
the rate the `k`-th one holds, `c t^k/k!`. -/
theorem chain_store_deriv (c t : ℝ) (k : ℕ) :
    HasDerivAt (fun s : ℝ => c * s ^ (k + 1) / ((k + 1).factorial : ℝ))
      (c * t ^ k / (k.factorial : ℝ)) t := by
  have h := ((hasDerivAt_pow (k + 1) t).const_mul c).div_const ((k + 1).factorial : ℝ)
  convert h using 1 <;> try rfl
  have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  rw [add_tsub_cancel_right, Nat.factorial_succ]
  push_cast
  rw [div_eq_div_iff hk (mul_ne_zero hk1 hk)]
  ring

/-! ## 5. A gap beats every power; a power does not -/

/-- With a gap `r > 0`, `exp(-r t)` falls faster than `(1+t)^(-K)` for every `K`. -/
theorem gap_beats_every_power (r : ℝ) (hr : 0 < r) (K : ℕ) :
    ∃ C, ∀ t : ℝ, 0 ≤ t → Real.exp (-r * t) * (1 + t) ^ K ≤ C := by
  refine ⟨Real.exp r * K.factorial / r ^ K, fun t ht => ?_⟩
  have hx : 0 ≤ r * (1 + t) := mul_nonneg hr.le (by linarith)
  have h1 := Real.pow_div_factorial_le_exp _ hx K
  have hK : (0 : ℝ) < K.factorial := by exact_mod_cast Nat.factorial_pos K
  have hrK : 0 < r ^ K := pow_pos hr K
  have he : Real.exp (r * (1 + t)) = Real.exp r * Real.exp (r * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hinv : Real.exp (-r * t) * Real.exp (r * t) = 1 := by
    rw [← Real.exp_add, show -r * t + r * t = 0 by ring, Real.exp_zero]
  rw [div_le_iff₀ hK, he] at h1
  rw [le_div_iff₀ hrK]
  have hpos : 0 < Real.exp (-r * t) := Real.exp_pos _
  calc Real.exp (-r * t) * (1 + t) ^ K * r ^ K
      = Real.exp (-r * t) * (r * (1 + t)) ^ K := by rw [mul_pow]; ring
    _ ≤ Real.exp (-r * t) * (Real.exp r * Real.exp (r * t) * K.factorial) :=
        mul_le_mul_of_nonneg_left h1 hpos.le
    _ = (Real.exp (-r * t) * Real.exp (r * t)) * (Real.exp r * K.factorial) := by ring
    _ = Real.exp r * K.factorial := by rw [hinv, one_mul]

/-- Fading only like `(1+t)^(-p)` fails the same test at power `p + 1`. -/
theorem power_decay_fails_rule (p : ℕ) :
    ¬ ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → (1 + t) ^ (p + 1) / (1 + t) ^ p ≤ C := by
  rintro ⟨C, hC⟩
  have ht : (0 : ℝ) ≤ |C| + 1 := by positivity
  have h := hC (|C| + 1) ht
  have hne : (1 + (|C| + 1)) ^ p ≠ 0 := pow_ne_zero _ (by positivity)
  rw [pow_succ, mul_div_cancel_left₀ _ hne] at h
  have hc := le_abs_self C
  linarith

/-! ## 6. Input ended, input continuing -/

/-- With the input ended, a store with a gap fades like `exp(-r t)`. -/
theorem input_ended (r x0 t : ℝ) : breathe r 0 x0 t = x0 * Real.exp (-r * t) := by
  simp [breathe]

/-- With a steady input, a store with a gap that has reached `u / r` stays there. -/
theorem steady_input_stays (r u t : ℝ) : breathe r u (u / r) t = u / r := by
  simp [breathe]

/-! ## 7. The breath out -/

/-- Letting go at rate `log (5/4)` for one breath of length 1 keeps exactly `4/5`. -/
theorem breath_keeps_four_fifths : Real.exp (-Real.log (5 / 4) * 1) = 4 / 5 := by
  rw [mul_one, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

/-- That rate is a gap. -/
theorem breath_out_is_a_gap : 0 < Real.log (5 / 4) := Real.log_pos (by norm_num)

end HugGap
