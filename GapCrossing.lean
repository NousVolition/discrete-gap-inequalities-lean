import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
# Reading both sides of a complex zero

At fixed height and fixed softening, the playground varies the real coordinate.
This module proves a conditional rule for any such complex-valued slice `f`.
It does not certify the numerical root or monotonicity of the playground's gap.
The real part is a signed component; the norm is the size of the whole value.
-/

namespace GapCrossing

/-- The size is zero exactly when the entire complex reading is zero. -/
theorem size_zero_iff (z : ℂ) : ‖z‖ = 0 ↔ z = 0 := norm_eq_zero

/-- The size cannot distinguish a reading from its opposite. -/
theorem size_of_opposite (z : ℂ) : ‖-z‖ = ‖z‖ := norm_neg z

/-- A nonzero signed component gives a lower bound on the whole size. -/
theorem component_le_size (z : ℂ) : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z

/-- Before an exact zero, a strictly increasing real component is negative,
and the whole reading has positive size. All positions lie in the same interval. -/
theorem before_zero (f : ℝ → ℂ) {a b c x : ℝ}
    (hmono : StrictMonoOn (fun r => (f r).re) (Set.Icc a b))
    (hc : c ∈ Set.Icc a b) (hz : f c = 0)
    (hx : x ∈ Set.Icc a b) (hxc : x < c) :
    (f x).re < 0 ∧ 0 < ‖f x‖ := by
  have hr : (f x).re < 0 := by simpa [hz] using hmono hx hc hxc
  refine ⟨hr, norm_pos_iff.mpr ?_⟩
  intro h
  simp [h] at hr

/-- Beyond the same exact zero, the real component and the size are positive. -/
theorem after_zero (f : ℝ → ℂ) {a b c y : ℝ}
    (hmono : StrictMonoOn (fun r => (f r).re) (Set.Icc a b))
    (hc : c ∈ Set.Icc a b) (hz : f c = 0)
    (hy : y ∈ Set.Icc a b) (hcy : c < y) :
    0 < (f y).re ∧ 0 < ‖f y‖ := by
  have hr : 0 < (f y).re := by simpa [hz] using hmono hc hy hcy
  refine ⟨hr, norm_pos_iff.mpr ?_⟩
  intro h
  simp [h] at hr

/-- A control: the real part changes sign between -1 and 1, but `x + i`
has no complex zero anywhere on the real axis. A sign change alone is insufficient. -/
theorem real_sign_change_without_zero :
    (((-1 : ℝ) : ℂ) + Complex.I).re < 0 ∧
    0 < (((1 : ℝ) : ℂ) + Complex.I).re ∧
    ∀ x : ℝ, (x : ℂ) + Complex.I ≠ 0 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro x h
  have hi := congrArg Complex.im h
  norm_num at hi

end GapCrossing
