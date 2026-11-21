import RingSumMinusTwelfth
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# The space retained by the damped Ramanujan shortcut

Proposed interpretation of Michele's direction: "the shortcut works because of the space".
Here the space is the signed difference between the damped discrete sum and the
integral of the same profile. This uses exponential damping and its specified smooth
reference. The ordinary sum of the positive integers is not assigned a finite total.

The exact identity compares epsilon with 2*epsilon. It cancels the divergent reference
area before taking a limit. Existence of the finite limit is supplied separately by
RingSumMinusTwelfth; the cancellation identity determines its value if it exists.
The final theorem connects this leftover to riemannZeta (-1), not to the location of
nontrivial zeros or to a proof of RiemannHypothesis.
-/

open Real Filter Topology MeasureTheory
open RingSumMinusTwelfth

namespace RamanujanGap

/-- The smooth reference is the area of the same damped profile. -/
theorem smooth_area {ε : ℝ} (hε : 0 < ε) :
    (∫ x : ℝ in Set.Ioi 0, x * exp (-(ε * x))) = 1 / ε ^ 2 := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hε
  norm_num [Real.rpow_two, Real.Gamma_nat_eq_factorial] at h
  simpa [div_pow] using h

/-- The closed-form leftover is exactly bars minus smooth area. -/
theorem bars_minus_area_eq_leftover {ε : ℝ} (hε : 0 < ε) :
    (∑' n : ℕ, (n : ℝ) * exp (-(ε * n))) -
      (∫ x : ℝ in Set.Ioi 0, x * exp (-(ε * x))) = staircaseLeftover ε := by
  rw [staircase_tsum hε, smooth_area hε]
  rfl

/-- The growing smooth areas cancel at these two damping scales. -/
theorem smooth_area_cancels {ε : ℝ} (hε : ε ≠ 0) :
    1 / ε ^ 2 - 4 * (1 / (2 * ε) ^ 2) = 0 := by
  field_simp
  ring

/-- The regulated counterpart of S - 4S: a finite identity for every positive epsilon. -/
theorem leftover_dyadic_identity {ε : ℝ} (hε : 0 < ε) :
    staircaseLeftover ε - 4 * staircaseLeftover (2 * ε) =
      exp (-ε) / (1 + exp (-ε)) ^ 2 := by
  let q := exp (-ε)
  have hq : 0 < q := exp_pos _
  have hq1 : q < 1 := exp_lt_one_iff.mpr (by linarith)
  have hn1 : 1 - q ≠ 0 := by linarith
  have hn2 : 1 - q ^ 2 ≠ 0 := by nlinarith
  have hp : 1 + q ≠ 0 := by positivity
  have he : exp (-(2 * ε)) = q ^ 2 := by
    rw [show -(2 * ε) = -ε + -ε by ring, exp_add]
    simp [q, pow_two]
  have halg : q / (1 - q) ^ 2 - 4 * (q ^ 2 / (1 - q ^ 2) ^ 2) =
      q / (1 + q) ^ 2 := by
    field_simp
    ring
  have hc := smooth_area_cancels hε.ne'
  unfold staircaseLeftover
  rw [he]
  change q / (1 - q) ^ 2 - 1 / ε ^ 2 -
    4 * (q ^ 2 / (1 - q ^ 2) ^ 2 - 1 / (2 * ε) ^ 2) = q / (1 + q) ^ 2
  linarith

/-- The right side is the convergent damped alternating sum, with n=0 contributing zero. -/
theorem alternating_hasSum {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun n : ℕ => -((n : ℝ) * (-exp (-ε)) ^ n))
      (exp (-ε) / (1 + exp (-ε)) ^ 2) := by
  have hnorm : ‖-exp (-ε)‖ < 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_lt_one_iff.mpr (by linarith)
  simpa only [sub_neg_eq_add, neg_div, neg_neg] using
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).neg

theorem alternating_limit :
    Tendsto (fun ε : ℝ => exp (-ε) / (1 + exp (-ε)) ^ 2)
      (𝓝[>] 0) (𝓝 (1 / 4)) := by
  have hc : ContinuousAt (fun ε : ℝ => exp (-ε) / (1 + exp (-ε)) ^ 2) 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    norm_num
  convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1
  norm_num

/-- Cancellation determines a finite leftover limit; it does not assume that limit exists. -/
theorem finite_leftover_limit_forced {L : ℝ}
    (hL : Tendsto staircaseLeftover (𝓝[>] 0) (𝓝 L)) : L = -1 / 12 := by
  have hdouble : Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun ε : ℝ => 2 * ε) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change 0 < 2 * ε
      exact mul_pos (by norm_num : (0 : ℝ) < 2) hε
  have hd := hL.sub ((hL.comp hdouble).const_mul 4)
  have hquarter : Tendsto (fun ε : ℝ => staircaseLeftover ε -
      4 * staircaseLeftover (2 * ε)) (𝓝[>] 0) (𝓝 (1 / 4)) := by
    apply alternating_limit.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (leftover_dyadic_identity hε).symm
  have heq := tendsto_nhds_unique hd hquarter
  linarith

theorem zeta_neg_one : riemannZeta (-1) = (-1 / 12 : ℂ) := by
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  norm_num at h
  convert h using 1
  ring

/-- The user's existing finite-part limit agrees with the value of Riemann's zeta at -1. -/
theorem leftover_limit_eq_zeta :
    Tendsto (fun ε : ℝ => (staircaseLeftover ε : ℂ)) (𝓝[>] 0)
      (𝓝 (riemannZeta (-1))) := by
  rw [zeta_neg_one]
  convert Complex.continuous_ofReal.continuousAt.tendsto.comp
    staircase_leftover_tendsto using 1 <;> norm_num [Function.comp_def]

end RamanujanGap
