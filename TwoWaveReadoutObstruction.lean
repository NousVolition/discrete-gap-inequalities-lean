import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# A same-sign obstruction for every globally covariant amplitude readout

This formalizes the user's proposed statement without a continuity, smoothness,
linearity, measurability, or positivity assumption on the readout or on the rates.
`W : ℝ → ℝ → ℝ` obeys the displayed motion identity for every real time and is
antisymmetric under exchanging its inputs. If `l ≠ m`, then `W a b = 0`
whenever `a*b > 0`, covering both strictly positive and strictly negative inputs.

The proof evolves the pair to the diagonal at `log(b/a)/(m-l)`. The time can
have either sign. This is an obstruction for the stated global amplitude laws;
it does not by itself classify readouts with only a restricted time/state domain.
The final theorem checks why the distinct-rate hypothesis is essential.
-/

open Real

namespace TwoWaveReadoutObstruction

theorem diagonal_zero (W : ℝ → ℝ → ℝ)
    (flip : ∀ a b : ℝ, W b a = -W a b) (x : ℝ) : W x x = 0 := by
  have h := flip x x
  linarith

/-- Same-sign nonzero coefficients meet at this exact real time. -/
theorem meeting_time (l m a b : ℝ) (hlm : l ≠ m) (ha : a ≠ 0) (hr : 0 < b / a) :
    a * exp (-l * (log (b / a) / (m - l))) =
      b * exp (-m * (log (b / a) / (m - l))) := by
  have hd : m - l ≠ 0 := sub_ne_zero.mpr hlm.symm
  have ht : (m - l) * (log (b / a) / (m - l)) = log (b / a) := by field_simp
  have he : exp ((m - l) * (log (b / a) / (m - l))) = b / a := by
    rw [ht, exp_log hr]
  have hsplit : exp (-l * (log (b / a) / (m - l))) =
      (b / a) * exp (-m * (log (b / a) / (m - l))) := by
    calc
      exp (-l * (log (b / a) / (m - l))) =
          exp ((m - l) * (log (b / a) / (m - l)) + -m * (log (b / a) / (m - l))) := by
        congr 1
        ring
      _ = exp ((m - l) * (log (b / a) / (m - l))) *
          exp (-m * (log (b / a) / (m - l))) := exp_add _ _
      _ = (b / a) * exp (-m * (log (b / a) / (m - l))) := by rw [he]
  have hab : a * (b / a) = b := by field_simp
  rw [hsplit, ← mul_assoc, hab]

/-- The main obstruction. The motion and flip hypotheses are exactly the user's laws. -/
theorem zero_of_same_sign (l m g : ℝ) (hlm : l ≠ m) (W : ℝ → ℝ → ℝ)
    (motion : ∀ a b t : ℝ,
      W (a * exp (-l * t)) (b * exp (-m * t)) = exp (-g * t) * W a b)
    (flip : ∀ a b : ℝ, W b a = -W a b)
    (a b : ℝ) (hab : 0 < a * b) : W a b = 0 := by
  have ha : a ≠ 0 := by
    intro h
    rw [h, zero_mul] at hab
    exact lt_irrefl 0 hab
  have hr : 0 < b / a := by
    rcases mul_pos_iff.mp hab with ⟨hap, hbp⟩ | ⟨han, hbn⟩
    · exact div_pos hbp hap
    · exact div_pos_of_neg_of_neg hbn han
  let t : ℝ := log (b / a) / (m - l)
  have he : a * exp (-l * t) = b * exp (-m * t) := meeting_time l m a b hlm ha hr
  have hm := motion a b t
  rw [he, diagonal_zero W flip] at hm
  exact (mul_eq_zero.mp hm.symm).resolve_left (exp_ne_zero _)

theorem zero_of_positive (l m g : ℝ) (hlm : l ≠ m) (W : ℝ → ℝ → ℝ)
    (motion : ∀ a b t : ℝ,
      W (a * exp (-l * t)) (b * exp (-m * t)) = exp (-g * t) * W a b)
    (flip : ∀ a b : ℝ, W b a = -W a b)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : W a b = 0 :=
  zero_of_same_sign l m g hlm W motion flip a b (mul_pos ha hb)

theorem zero_of_negative (l m g : ℝ) (hlm : l ≠ m) (W : ℝ → ℝ → ℝ)
    (motion : ∀ a b t : ℝ,
      W (a * exp (-l * t)) (b * exp (-m * t)) = exp (-g * t) * W a b)
    (flip : ∀ a b : ℝ, W b a = -W a b)
    (a b : ℝ) (ha : a < 0) (hb : b < 0) : W a b = 0 :=
  zero_of_same_sign l m g hlm W motion flip a b (mul_pos_of_neg_of_neg ha hb)

/-- The two conclusions in the form requested by the user. -/
theorem proposed_statement (l m g : ℝ) (hlm : l ≠ m) (W : ℝ → ℝ → ℝ)
    (motion : ∀ a b t : ℝ,
      W (a * exp (-l * t)) (b * exp (-m * t)) = exp (-g * t) * W a b)
    (flip : ∀ a b : ℝ, W b a = -W a b) :
    (∀ a b : ℝ, 0 < a → 0 < b → W a b = 0) ∧
    (∀ a b : ℝ, a < 0 → b < 0 → W a b = 0) := by
  exact ⟨fun a b ha hb => zero_of_positive l m g hlm W motion flip a b ha hb,
    fun a b ha hb => zero_of_negative l m g hlm W motion flip a b ha hb⟩

/-- When both rates equal g, W(a,b)=a-b obeys both laws and distinguishes same-sign pairs. -/
theorem equal_rates_counterexample (l : ℝ) :
    (∀ a b t : ℝ, a * exp (-l * t) - b * exp (-l * t) = exp (-l * t) * (a - b)) ∧
    (∀ a b : ℝ, b - a = -(a - b)) ∧
    (2 : ℝ) - 1 ≠ 0 ∧ (-1 : ℝ) - (-2) ≠ 0 := by
  refine ⟨?_, ?_, by norm_num, by norm_num⟩
  · intro a b t; ring
  · intro a b; ring

end TwoWaveReadoutObstruction

#print axioms TwoWaveReadoutObstruction.diagonal_zero
#print axioms TwoWaveReadoutObstruction.meeting_time
#print axioms TwoWaveReadoutObstruction.zero_of_same_sign
#print axioms TwoWaveReadoutObstruction.zero_of_positive
#print axioms TwoWaveReadoutObstruction.zero_of_negative
#print axioms TwoWaveReadoutObstruction.proposed_statement
#print axioms TwoWaveReadoutObstruction.equal_rates_counterexample
