import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Continuous Wirtinger inequality with zero endpoint values

The proof completes a square with a tangent whose poles lie outside the
interval, then lets its frequency approach pi divided by interval length.
No statement about the Riemann hypothesis is assumed.
-/

open Real Set MeasureTheory Filter Topology

namespace ContinuousWirtinger

private theorem square_bound {a b c : ℝ} (hab : a < b)
    {f f' h : ℝ → ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : ContinuousOn f' (Icc a b))
    (hh : ∀ x ∈ Icc a b, HasDerivAt h (h x ^ 2 + c) x)
    (ha : f a = 0) (hb : f b = 0) :
    c * (∫ x in a..b, f x ^ 2) ≤ ∫ x in a..b, f' x ^ 2 := by
  have hfc : ContinuousOn f (Icc a b) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (Icc a b) :=
    fun x hx => (hh x hx).continuousAt.continuousWithinAt
  let d : ℝ → ℝ := fun x => (h x ^ 2 + c) * f x ^ 2 + 2 * h x * f x * f' x
  have hdc : ContinuousOn d (Icc a b) := by
    dsimp [d]
    fun_prop
  have hdi : IntervalIntegrable d volume a b := hdc.intervalIntegrable_of_Icc hab.le
  have hd : ∫ x in a..b, d x = 0 := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x => h x * f x ^ 2) (f' := d)
      (fun x hx => by
        rw [uIcc_of_le hab.le] at hx
        exact ((hh x hx).mul ((hf x hx).pow 2)).congr_deriv (by dsimp [d]; ring)) hdi
    simpa [ha, hb] using hftc
  have hfi : IntervalIntegrable (fun x => f x ^ 2) volume a b :=
    (hfc.pow 2).intervalIntegrable_of_Icc hab.le
  have hfpi : IntervalIntegrable (fun x => f' x ^ 2) volume a b :=
    (hf'.pow 2).intervalIntegrable_of_Icc hab.le
  have hineq := intervalIntegral.integral_mono_on hab.le (hfi.const_mul c)
    (hfpi.add hdi) (fun x hx => by
      dsimp [d]
      nlinarith [sq_nonneg (f' x + h x * f x)])
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hfpi hdi, hd, add_zero] at hineq
  exact hineq

private theorem frequency_bound {a b k : ℝ} (hab : a < b)
    (hk : 0 ≤ k) (hkl : k * (b - a) < π)
    {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : ContinuousOn f' (Icc a b))
    (ha : f a = 0) (hb : f b = 0) :
    k ^ 2 * (∫ x in a..b, f x ^ 2) ≤ ∫ x in a..b, f' x ^ 2 := by
  apply square_bound hab hf hf' (h := fun x => k * tan (k * (x - (a+b)/2))) ?_ ha hb
  intro x hx
  have harg : k * (x - (a+b)/2) ∈ Ioo (-(π/2)) (π/2) := by
    constructor <;> nlinarith [mul_nonneg hk (sub_nonneg.mpr hx.1),
      mul_nonneg hk (sub_nonneg.mpr hx.2)]
  have hc : cos (k * (x - (a+b)/2)) ≠ 0 := (cos_pos_of_mem_Ioo harg).ne'
  have ht := ((Real.hasDerivAt_tan hc).comp x
    (((hasDerivAt_id x).sub_const ((a+b)/2)).const_mul k)).const_mul k
  have hinv : 1 / cos (k * (x - (a+b)/2)) ^ 2 =
      1 + tan (k * (x - (a+b)/2)) ^ 2 := by
    apply (div_eq_iff (pow_ne_zero 2 hc)).2
    exact (Real.one_add_tan_sq_mul_cos_sq_eq_one hc).symm
  convert ht using 1 <;> (try rfl)
  rw [hinv]
  ring

/-- The endpoint-zero energy inequality on a nonempty real interval. -/
theorem dirichlet_energy {a b : ℝ} (hab : a < b) {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : ContinuousOn f' (Icc a b))
    (ha : f a = 0) (hb : f b = 0) :
    (π / (b-a)) ^ 2 * (∫ x in a..b, f x ^ 2) ≤ ∫ x in a..b, f' x ^ 2 := by
  have hL : 0 < b-a := sub_pos.mpr hab
  have hK : 0 < π / (b-a) := div_pos pi_pos hL
  have hc : Continuous (fun k : ℝ => k ^ 2 * (∫ x in a..b, f x ^ 2)) := by fun_prop
  apply le_of_tendsto (hc.continuousAt.tendsto.mono_left
    (show 𝓝[<] (π / (b-a)) ≤ 𝓝 (π / (b-a)) from nhdsWithin_le_nhds))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds hK).filter_mono nhdsWithin_le_nhds] with k hk hk0
  exact frequency_bound hab hk0.le ((lt_div_iff₀ hL).mp hk) hf hf' ha hb

/-- The usual continuous Wirtinger inequality with both endpoint values zero. -/
theorem wirtinger {a b : ℝ} (hab : a < b) {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : ContinuousOn f' (Icc a b))
    (ha : f a = 0) (hb : f b = 0) :
    (∫ x in a..b, f x ^ 2) ≤ ((b-a) / π) ^ 2 * (∫ x in a..b, f' x ^ 2) := by
  have h := dirichlet_energy hab hf hf' ha hb
  calc
    (∫ x in a..b, f x ^ 2) = ((b-a) / π) ^ 2 *
        ((π / (b-a)) ^ 2 * (∫ x in a..b, f x ^ 2)) := by
      field_simp [sub_ne_zero.mpr hab.ne', Real.pi_ne_zero]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (sq_nonneg _)

end ContinuousWirtinger
