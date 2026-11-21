import ContinuousWirtinger
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The sharp Wirtinger inequality for a loop

Two points half a period apart have the same value. Subtracting that value
pins both ends of each half, so the endpoint-zero inequality applies twice.
Centering at the mean minimizes the integral of the squared deviation.
The fundamental sine attains equality for every positive period.

Proposed credit for Michele's review.
NousVolition gave the direction “split the gap into two halves”. Claude matched
the classical textbook half-turn proof to that direction and supplied the
statement, proof plan and sharpness test. Codex formalized the proof in Lean.
-/

open Real Set MeasureTheory Filter Topology

private theorem periodic_derivative {L : ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hper : Function.Periodic f L) :
    Function.Periodic f' L := by
  intro x
  have hshift := (hf (x + L)).comp_add_const x L
  rw [show (fun t => f (t + L)) = f from funext hper] at hshift
  exact hshift.unique (hf x)

private theorem exists_equal_half_turn {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : Continuous f) (hper : Function.Periodic f L) :
    ∃ a ∈ Icc 0 (L / 2), f a = f (a + L / 2) := by
  let h (x : ℝ) := f x - f (x + L / 2)
  have hc : Continuous h := hf.sub (hf.comp (continuous_id.add continuous_const))
  have hturn (x : ℝ) : h (x + L / 2) = -h x := by
    dsimp [h]
    rw [show x + L / 2 + L / 2 = x + L by ring, hper x, neg_sub]
  have hend : h (L / 2) = -h 0 := by simpa only [zero_add] using hturn 0
  have hz : (0 : ℝ) ∈ h '' Icc 0 (L / 2) := by
    rcases le_total (h 0) 0 with hs | hs
    · exact intermediate_value_Icc (half_pos hL).le hc.continuousOn
        ⟨hs, hend ▸ neg_nonneg.mpr hs⟩
    · exact intermediate_value_Icc' (half_pos hL).le hc.continuousOn
        ⟨hend ▸ neg_nonpos.mpr hs, hs⟩
  obtain ⟨a, ha, hzero⟩ := hz
  exact ⟨a, ha, sub_eq_zero.mp hzero⟩

/-- Expanding about the mean leaves a zero cross term. -/
private theorem mean_minimizes {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : Continuous f) (c : ℝ) :
    (∫ x in (0 : ℝ)..L, (f x - (∫ y in (0 : ℝ)..L, f y) / L) ^ 2) ≤
      ∫ x in (0 : ℝ)..L, (f x - c) ^ 2 := by
  let m := (∫ y in (0 : ℝ)..L, f y) / L
  have hzero : (∫ x in (0 : ℝ)..L, f x - m) = 0 := by
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    dsimp [m]
    field_simp [hL.ne']
    ring
  have hcenter : Continuous (fun x => f x - m) := hf.sub continuous_const
  have hi : IntervalIntegrable (fun x => (f x - m) ^ 2) volume 0 L :=
    (hcenter.pow 2).intervalIntegrable 0 L
  have hj := (hcenter.intervalIntegrable (μ := volume) 0 L).const_mul (2 * (m - c))
  have hsplit : (∫ x in (0 : ℝ)..L, (f x - c) ^ 2) =
      (∫ x in (0 : ℝ)..L, (f x - m) ^ 2) + L * (m - c) ^ 2 := by
    calc
      _ = ∫ x in (0 : ℝ)..L,
            ((f x - m) ^ 2 + (2 * (m - c)) * (f x - m)) + (m - c) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hi.add hj) (intervalIntegrable_const (c := (m - c) ^ 2)),
          intervalIntegral.integral_add hi hj, intervalIntegral.integral_const_mul,
          hzero, intervalIntegral.integral_const]
        simp
  rw [hsplit]
  exact le_add_of_nonneg_right (mul_nonneg hL.le (sq_nonneg _))

/-- A periodic real function with continuous derivative satisfies the sharp
Wirtinger inequality after subtracting its average over one period. -/
theorem loop_wirtinger {L : ℝ} (hL : 0 < L) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (hper : Function.Periodic f L) :
    (∫ x in (0 : ℝ)..L, (f x - (∫ y in (0 : ℝ)..L, f y) / L) ^ 2) ≤
      (L / (2 * π)) ^ 2 * ∫ x in (0 : ℝ)..L, f' x ^ 2 := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  obtain ⟨a, _, hmid⟩ := exists_equal_half_turn hL hfc hper
  let b := a + L / 2
  let g (x : ℝ) := f x - f a
  have hg (x : ℝ) : HasDerivAt g (f' x) x := (hf x).sub_const (f a)
  have hga : g a = 0 := sub_self _
  have hgb : g b = 0 := sub_eq_zero.mpr hmid.symm
  have hgend : g (a + L) = 0 := sub_eq_zero.mpr (hper a)
  have half_bound {u v : ℝ} (hlen : v - u = L / 2) (hu : g u = 0) (hv : g v = 0) :
      (∫ x in u..v, g x ^ 2) ≤ (L / (2 * π)) ^ 2 * ∫ x in u..v, f' x ^ 2 := by
    have h := ContinuousWirtinger.wirtinger (by linarith : u < v)
      (fun x _ => hg x) hf'.continuousOn hu hv
    rwa [hlen, div_div] at h
  have hleft := half_bound (u := a) (v := b) (by dsimp [b]; ring) hga hgb
  have hright := half_bound (u := b) (v := a + L) (by dsimp [b]; ring) hgb hgend
  have hgi (u v : ℝ) : IntervalIntegrable (fun x => g x ^ 2) volume u v :=
    ((hfc.sub continuous_const).pow 2).intervalIntegrable u v
  have hdi (u v : ℝ) : IntervalIntegrable (fun x => f' x ^ 2) volume u v :=
    (hf'.pow 2).intervalIntegrable u v
  have hboth := add_le_add hleft hright
  rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals (hgi _ _) (hgi _ _),
    intervalIntegral.integral_add_adjacent_intervals (hdi _ _) (hdi _ _)] at hboth
  have hgp : Function.Periodic (fun x => g x ^ 2) L := fun x => by simp only [g, hper x]
  have hdp : Function.Periodic (fun x => f' x ^ 2) L :=
    fun x => congrArg (fun y : ℝ => y ^ 2) (periodic_derivative hf hper x)
  rw [hgp.intervalIntegral_add_eq a 0, hdp.intervalIntegral_add_eq a 0, zero_add] at hboth
  exact (mean_minimizes hL hfc (f a)).trans hboth

namespace LoopWirtinger

/-- The sine wave that makes one turn in a period of length `L`. -/
noncomputable def sine (L x : ℝ) : ℝ := sin (2 * π / L * x)

/-- The derivative of the fundamental sine wave. -/
noncomputable def sineDeriv (L x : ℝ) : ℝ := (2 * π / L) * cos (2 * π / L * x)

/-- The sharpness witness satisfies all three function hypotheses of `loop_wirtinger`. -/
theorem sine_admissible {L : ℝ} (hL : 0 < L) :
    (∀ x, HasDerivAt (sine L) (sineDeriv L x) x) ∧
      Continuous (sineDeriv L) ∧ Function.Periodic (sine L) L := by
  refine ⟨fun x => ?_, ?_, fun x => ?_⟩
  · exact (hasDerivAt_const_mul (x := x) (2 * π / L)).sin.congr_deriv (mul_comm _ _)
  · unfold sineDeriv
    fun_prop
  · simp only [sine, mul_add, div_mul_cancel₀ _ hL.ne', sin_add_two_pi]

private theorem sine_energies {L : ℝ} (hL : 0 < L) :
    (∫ x in (0 : ℝ)..L, (sine L x - (∫ y in (0 : ℝ)..L, sine L y) / L) ^ 2) = L / 2 ∧
    (∫ x in (0 : ℝ)..L, sineDeriv L x ^ 2) = (2 * π / L) ^ 2 * (L / 2) := by
  let k := 2 * π / L
  have hk : 0 < k := div_pos (by positivity) hL
  have hkL : k * L = 2 * π := div_mul_cancel₀ _ hL.ne'
  have rescale (p : ℝ → ℝ) :
      (∫ x in (0 : ℝ)..L, p (k * x)) = k⁻¹ * ∫ y in (0 : ℝ)..2 * π, p y := by
    rw [intervalIntegral.integral_comp_mul_left p hk.ne', mul_zero, hkL, smul_eq_mul]
  have hmean : (∫ y in (0 : ℝ)..L, sine L y) = 0 := by
    change (∫ y in (0 : ℝ)..L, sin (k * y)) = 0
    rw [rescale sin, integral_sin]
    simp
  have hs : (∫ y in (0 : ℝ)..2 * π, sin y ^ 2) = π := by rw [integral_sin_sq]; simp
  have hc : (∫ y in (0 : ℝ)..2 * π, cos y ^ 2) = π := by rw [integral_cos_sq]; simp
  have hscale : k⁻¹ * π = L / 2 := by
    dsimp [k]
    field_simp [Real.pi_ne_zero]
  constructor
  · simp only [hmean, zero_div, sub_zero]
    exact (rescale (fun y => sin y ^ 2)).trans (by rw [hs]; exact hscale)
  · change (∫ x in (0 : ℝ)..L, (k * cos (k * x)) ^ 2) = k ^ 2 * (L / 2)
    simp_rw [mul_pow]
    rw [intervalIntegral.integral_const_mul]
    exact congrArg (k ^ 2 * ·) ((rescale (fun y => cos y ^ 2)).trans (by rw [hc]; exact hscale))

/-- Equality for the fundamental sine, at every positive period. -/
theorem sine_equality {L : ℝ} (hL : 0 < L) :
    (∫ x in (0 : ℝ)..L, (sine L x - (∫ y in (0 : ℝ)..L, sine L y) / L) ^ 2) =
      (L / (2 * π)) ^ 2 * ∫ x in (0 : ℝ)..L, sineDeriv L x ^ 2 := by
  obtain ⟨hvar, henergy⟩ := sine_energies hL
  rw [hvar, henergy]
  field_simp [Real.pi_ne_zero, hL.ne']

/-- Every smaller coefficient fails on that same sine wave. -/
theorem sine_breaks_smaller_constant {L C : ℝ} (hL : 0 < L) (hC : C < (L / (2 * π)) ^ 2) :
    C * (∫ x in (0 : ℝ)..L, sineDeriv L x ^ 2) <
      ∫ x in (0 : ℝ)..L, (sine L x - (∫ y in (0 : ℝ)..L, sine L y) / L) ^ 2 := by
  rw [sine_equality hL]
  apply mul_lt_mul_of_pos_right hC
  rw [(sine_energies hL).2]
  positivity

/-- The rescaled spectral gap of the discrete ring tends to the gap of the loop of period one. -/
theorem ring_gap_tendsto :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * (2 - 2 * cos (2 * π / n))) atTop (𝓝 (4 * π ^ 2)) := by
  have hs : Tendsto (fun n : ℕ => sinc (π / n)) atTop (𝓝 1) := by
    simpa only [sinc_zero, Function.comp_def] using
      (continuous_sinc.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat π)
  have hlim : Tendsto (fun n : ℕ => (4 * π ^ 2) * sinc (π / n) ^ 2) atTop (𝓝 (4 * π ^ 2)) := by
    simpa using (hs.pow 2).const_mul (4 * π ^ 2)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [sinc_of_ne_zero (div_ne_zero pi_ne_zero hn'),
    show 2 * π / (n : ℝ) = 2 * (π / n) by ring, cos_two_mul_eq_one_sub]
  field_simp [pi_ne_zero, hn']
  ring

end LoopWirtinger

#print axioms loop_wirtinger
#print axioms LoopWirtinger.sine_admissible
#print axioms LoopWirtinger.sine_equality
#print axioms LoopWirtinger.sine_breaks_smaller_constant
#print axioms LoopWirtinger.ring_gap_tendsto
