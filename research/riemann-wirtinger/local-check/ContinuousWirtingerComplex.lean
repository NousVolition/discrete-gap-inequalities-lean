import ContinuousWirtinger
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Real Set MeasureTheory

namespace ContinuousWirtinger

/-- The complex-valued version, proved by adding the real and imaginary bounds. -/
theorem wirtinger_complex {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ}
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : ContinuousOn f' (Icc a b))
    (ha : f a = 0) (hb : f b = 0) :
    (∫ x in a..b, ‖f x‖ ^ 2) ≤ ((b-a) / π) ^ 2 * (∫ x in a..b, ‖f' x‖ ^ 2) := by
  have hfc : ContinuousOn f (Icc a b) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hre : ∀ x ∈ Icc a b, HasDerivAt (fun y => (f y).re) (f' x).re x := by
    intro x hx
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hf x hx)
  have him : ∀ x ∈ Icc a b, HasDerivAt (fun y => (f y).im) (f' x).im x := by
    intro x hx
    exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hf x hx)
  have hr := wirtinger hab hre (Complex.continuous_re.comp_continuousOn hf')
    (by simp [ha]) (by simp [hb])
  have hi := wirtinger hab him (Complex.continuous_im.comp_continuousOn hf')
    (by simp [ha]) (by simp [hb])
  have ire : IntervalIntegrable (fun x => (f x).re ^ 2) volume a b :=
    ((Complex.continuous_re.comp_continuousOn hfc).pow 2).intervalIntegrable_of_Icc hab.le
  have iim : IntervalIntegrable (fun x => (f x).im ^ 2) volume a b :=
    ((Complex.continuous_im.comp_continuousOn hfc).pow 2).intervalIntegrable_of_Icc hab.le
  have ipre : IntervalIntegrable (fun x => (f' x).re ^ 2) volume a b :=
    ((Complex.continuous_re.comp_continuousOn hf').pow 2).intervalIntegrable_of_Icc hab.le
  have ipim : IntervalIntegrable (fun x => (f' x).im ^ 2) volume a b :=
    ((Complex.continuous_im.comp_continuousOn hf').pow 2).intervalIntegrable_of_Icc hab.le
  simp_rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, ← pow_two]
  rw [intervalIntegral.integral_add ire iim, intervalIntegral.integral_add ipre ipim]
  nlinarith [hr, hi]

/-- The same estimate expressed as a lower bound on squared zero separation. -/
theorem zero_gap_sq_lower_bound {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ}
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : ContinuousOn f' (Icc a b))
    (ha : f a = 0) (hb : f b = 0)
    (hD : 0 < ∫ x in a..b, ‖f' x‖ ^ 2) :
    π ^ 2 * (∫ x in a..b, ‖f x‖ ^ 2) / (∫ x in a..b, ‖f' x‖ ^ 2) ≤ (b-a) ^ 2 := by
  have hw := wirtinger_complex hab hf hf' ha hb
  have hw' : (∫ x in a..b, ‖f x‖ ^ 2) ≤
      (b-a) ^ 2 * (∫ x in a..b, ‖f' x‖ ^ 2) / π ^ 2 := by
    simpa only [div_pow, div_mul_eq_mul_div] using hw
  have hmul := (le_div_iff₀ (sq_pos_of_pos pi_pos)).mp hw'
  apply (div_le_iff₀ hD).2
  nlinarith [hmul]

/-- On [0, pi], sine attains the energy bound with a positive integral. -/
theorem sine_attains_bound :
    (∫ x in (0 : ℝ)..π, sin x ^ 2) = π / 2 ∧
    (∫ x in (0 : ℝ)..π, cos x ^ 2) = π / 2 ∧ 0 < π / 2 := by
  simp only [integral_sin_sq, integral_cos_sq,
    sin_zero, cos_zero, sin_pi, cos_pi]
  constructor
  · ring
  constructor
  · ring
  · positivity

end ContinuousWirtinger
