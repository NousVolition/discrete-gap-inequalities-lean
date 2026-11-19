import Poincare

/-!
# The sharp gap of the six-point path

For the same unweighted path energy as `DiscretePoincare.dirichlet`, the best
mean-zero lower bound at six points is `2 - sqrt 3`. The proof splits the six
values into symmetric and antisymmetric parts and checks a sum-of-squares identity.
An explicit nonzero equality case proves sharpness. Rational bounds certify the
three-decimal display `0.268`; that rounded number is not itself a valid lower bound.
-/

open Finset

namespace PathSix

/-- The exact six-point path gap. -/
noncomputable def gap : ℝ := 2 - Real.sqrt 3

/-- Squared norm of the values on the six vertices. -/
def mass (f : ℕ → ℝ) : ℝ := ∑ i ∈ range 6, f i ^ 2

theorem sqrt_three_bounds : 1 < Real.sqrt 3 ∧ Real.sqrt 3 < 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  constructor <;> nlinarith

theorem gap_pos : 0 < gap := by
  unfold gap
  linarith [sqrt_three_bounds.2]

theorem mass_nonneg (f : ℕ → ℝ) : 0 ≤ mass f := by
  exact sum_nonneg (fun i _ => sq_nonneg (f i))

/-- The symmetric part has the stronger gap 1, hence also the gap `2 - sqrt 3`. -/
theorem symmetric_bound (a b c : ℝ) (hmean : a + b + c = 0) :
    gap * (a ^ 2 + b ^ 2 + c ^ 2) ≤ (b - a) ^ 2 + (c - b) ^ 2 := by
  have hz : b * (a + b + c) = 0 := by rw [hmean]; ring
  have hs : 0 ≤ Real.sqrt 3 - 1 := by linarith [sqrt_three_bounds.1]
  have hp := mul_nonneg hs (add_nonneg (add_nonneg (sq_nonneg a) (sq_nonneg b))
    (sq_nonneg c))
  unfold gap
  nlinarith only [hz, hp, sq_nonneg b]

/-- An exact sum of squares for the antisymmetric part. -/
theorem antisymmetric_identity (x y z : ℝ) :
    4 * ((y - x) ^ 2 + (z - y) ^ 2 + 2 * z ^ 2
      - gap * (x ^ 2 + y ^ 2 + z ^ 2)) =
      (Real.sqrt 3 - 1) * (2 * x - (Real.sqrt 3 + 1) * y) ^ 2
      + 2 * (Real.sqrt 3 - 1) * (y - (Real.sqrt 3 + 1) * z) ^ 2 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by
    calc (Real.sqrt 3) ^ 3 = (Real.sqrt 3) ^ 2 * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [hs]
  unfold gap
  ring_nf
  simp only [hs, hc]
  ring

theorem antisymmetric_bound (x y z : ℝ) :
    gap * (x ^ 2 + y ^ 2 + z ^ 2) ≤
      (y - x) ^ 2 + (z - y) ^ 2 + 2 * z ^ 2 := by
  have hs : 0 ≤ Real.sqrt 3 - 1 := by linarith [sqrt_three_bounds.1]
  have h1 := mul_nonneg hs (sq_nonneg (2 * x - (Real.sqrt 3 + 1) * y))
  have h2 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs)
    (sq_nonneg (y - (Real.sqrt 3 + 1) * z))
  linarith only [antisymmetric_identity x y z, h1, h2]

/-- **Sharp six-point Poincaré inequality**, for every real mean-zero input. -/
theorem poincare (f : ℕ → ℝ) (hmean : ∑ i ∈ range 6, f i = 0) :
    gap * mass f ≤ DiscretePoincare.dirichlet f 6 := by
  have hm : (f 0 + f 5) + (f 1 + f 4) + (f 2 + f 3) = 0 := by
    norm_num [sum_range_succ] at hmean
    linarith
  have he := symmetric_bound (f 0 + f 5) (f 1 + f 4) (f 2 + f 3) hm
  have ho := antisymmetric_bound (f 0 - f 5) (f 1 - f 4) (f 2 - f 3)
  norm_num [mass, DiscretePoincare.dirichlet, sum_range_succ]
  nlinarith only [he, ho]

/-- A nonzero equality mode, scaled so that its first value is 1. -/
noncomputable def mode : ℕ → ℝ
  | 0 => 1
  | 1 => Real.sqrt 3 - 1
  | 2 => 2 - Real.sqrt 3
  | 3 => Real.sqrt 3 - 2
  | 4 => 1 - Real.sqrt 3
  | _ => -1

theorem mode_mean_zero : ∑ i ∈ range 6, mode i = 0 := by
  norm_num [sum_range_succ, mode]

theorem mode_mass_pos : 0 < mass mode := by
  norm_num [mass, sum_range_succ, mode]
  positivity

theorem mode_equality : DiscretePoincare.dirichlet mode 6 = gap * mass mode := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by
    calc (Real.sqrt 3) ^ 3 = (Real.sqrt 3) ^ 2 * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [hs]
  norm_num [DiscretePoincare.dirichlet, mass, sum_range_succ, mode, gap]
  ring_nf
  simp only [hs, hc]
  ring

/-- No larger coefficient works for all mean-zero six-point inputs. -/
theorem sharp (C : ℝ)
    (hC : ∀ f : ℕ → ℝ, (∑ i ∈ range 6, f i = 0) →
      C * mass f ≤ DiscretePoincare.dirichlet f 6) : C ≤ gap := by
  have h := hC mode mode_mean_zero
  rw [mode_equality] at h
  nlinarith only [h, mode_mass_pos]

/-- A complete characterization of the valid lower-bound coefficients. -/
theorem valid_bound_iff (C : ℝ) :
    (∀ f : ℕ → ℝ, (∑ i ∈ range 6, f i = 0) →
      C * mass f ≤ DiscretePoincare.dirichlet f 6) ↔ C ≤ gap := by
  constructor
  · exact sharp C
  · intro hC f hmean
    exact (mul_le_mul_of_nonneg_right hC (mass_nonneg f)).trans (poincare f hmean)

/-- Rational enclosures, proved from the square-root identity inside Lean. -/
theorem gap_decimal_bounds :
    (2679491924 / 10000000000 : ℝ) < gap ∧ gap < 2679491925 / 10000000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  unfold gap
  constructor <;> nlinarith

/-- The exact gap lies strictly inside the nearest-three-decimal bin for 0.268. -/
theorem display_rounding_bin :
    (2675 / 10000 : ℝ) < gap ∧ gap < 2685 / 10000 := by
  constructor <;> linarith [gap_decimal_bounds.1, gap_decimal_bounds.2]

/-- The displayed number is an upward rounding, not the exact constant. -/
theorem display_exceeds_gap : gap < (268 / 1000 : ℝ) := by
  linarith [gap_decimal_bounds.2]

/-- Using literal 0.268 as a universal lower bound would make a false claim. -/
theorem rounded_value_not_valid_bound :
    ¬ ∀ f : ℕ → ℝ, (∑ i ∈ range 6, f i = 0) →
      (268 / 1000 : ℝ) * mass f ≤ DiscretePoincare.dirichlet f 6 := by
  intro h
  have hle := sharp (268 / 1000) h
  linarith [display_exceeds_gap]

end PathSix
