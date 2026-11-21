import ContinuousWirtingerComplex
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# A zero-spacing tool within a Riemann-hypothesis investigation

The interval inequality is applied to zeta itself, including vertical lines
away from the critical line. It uses no assumption of the Riemann hypothesis.
The final conditional theorem records what RH would let us conclude about
arbitrary nontrivial zeros. It does not assert the converse implication.
-/

open Real Complex Set MeasureTheory

namespace RiemannZeroGaps

def linePoint (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I

noncomputable def zetaLine (σ t : ℝ) : ℂ := riemannZeta (linePoint σ t)

noncomputable def zetaSlope (σ t : ℝ) : ℂ := deriv riemannZeta (linePoint σ t) * I

theorem linePoint_ne_one {σ : ℝ} (hσ : σ ≠ 1) (t : ℝ) : linePoint σ t ≠ 1 := by
  intro h
  apply hσ
  have hr := congrArg Complex.re h
  simpa [linePoint] using hr

theorem hasDerivAt_zetaLine {σ : ℝ} (hσ : σ ≠ 1) (t : ℝ) :
    HasDerivAt (zetaLine σ) (zetaSlope σ t) t := by
  have hi : HasDerivAt (fun z : ℂ => (σ : ℂ) + z * I) I (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).mul_const I).const_add (σ : ℂ)
  have ho := (differentiableAt_riemannZeta (linePoint_ne_one hσ t)).hasDerivAt
  simpa only [zetaLine, zetaSlope, linePoint, Function.comp_def] using!
    (ho.comp (t : ℂ) hi).comp_ofReal

theorem continuous_zetaSlope {σ : ℝ} (hσ : σ ≠ 1) : Continuous (zetaSlope σ) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hz : AnalyticAt ℂ riemannZeta (linePoint σ t) :=
    analyticOn_riemannZeta _ (by simpa using linePoint_ne_one hσ t)
  have hp : ContinuousAt (linePoint σ) t := by unfold linePoint; fun_prop
  exact (hz.deriv.continuousAt.comp hp).mul continuousAt_const

/-- This bound applies on every vertical line other than the line through the pole. -/
theorem vertical_zero_interval {σ a b : ℝ} (hσ : σ ≠ 1) (hab : a < b)
    (ha : zetaLine σ a = 0) (hb : zetaLine σ b = 0) :
    (∫ t in a..b, ‖zetaLine σ t‖ ^ 2) ≤
      ((b-a) / π) ^ 2 * (∫ t in a..b, ‖zetaSlope σ t‖ ^ 2) := by
  exact ContinuousWirtinger.wirtinger_complex hab
    (fun t _ => hasDerivAt_zetaLine hσ t) (continuous_zetaSlope hσ).continuousOn ha hb

/-- A squared gap bound when the derivative integral is positive. -/
theorem vertical_zero_gap {σ a b : ℝ} (hσ : σ ≠ 1) (hab : a < b)
    (ha : zetaLine σ a = 0) (hb : zetaLine σ b = 0)
    (hD : 0 < ∫ t in a..b, ‖zetaSlope σ t‖ ^ 2) :
    π ^ 2 * (∫ t in a..b, ‖zetaLine σ t‖ ^ 2) /
      (∫ t in a..b, ‖zetaSlope σ t‖ ^ 2) ≤ (b-a) ^ 2 := by
  exact ContinuousWirtinger.zero_gap_sq_lower_bound hab
    (fun t _ => hasDerivAt_zetaLine hσ t) (continuous_zetaSlope hσ).continuousOn ha hb hD

/-- The critical-line application does not require the Riemann hypothesis. -/
theorem critical_zero_interval {a b : ℝ} (hab : a < b)
    (ha : zetaLine (1/2) a = 0) (hb : zetaLine (1/2) b = 0) :
    (∫ t in a..b, ‖zetaLine (1/2) t‖ ^ 2) ≤
      ((b-a) / π) ^ 2 * (∫ t in a..b, ‖zetaSlope (1/2) t‖ ^ 2) := by
  exact vertical_zero_interval (by norm_num) hab ha hb

def NontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1

theorem zero_on_line {s : ℂ} (hs : NontrivialZero s) (hline : s.re = 1/2) :
    zetaLine (1/2) s.im = 0 := by
  have hp : linePoint (1/2) s.im = s := by
    apply Complex.ext <;> simp [linePoint, hline]
  change riemannZeta (linePoint (1/2) s.im) = 0
  rw [hp]
  exact hs.1

/-- Under RH, the same interval bound applies between any two nontrivial zeros
with distinct imaginary parts. The unconditional interval tool above is reused. -/
theorem rh_implies_all_zero_interval (hRH : RiemannHypothesis)
    {s₁ s₂ : ℂ} (h₁ : NontrivialZero s₁) (h₂ : NontrivialZero s₂)
    (horder : s₁.im < s₂.im) :
    (∫ t in s₁.im..s₂.im, ‖zetaLine (1/2) t‖ ^ 2) ≤
      ((s₂.im-s₁.im) / π) ^ 2 * (∫ t in s₁.im..s₂.im, ‖zetaSlope (1/2) t‖ ^ 2) := by
  exact critical_zero_interval horder
    (zero_on_line h₁ (hRH s₁ h₁.1 h₁.2.1 h₁.2.2))
    (zero_on_line h₂ (hRH s₂ h₂.1 h₂.2.1 h₂.2.2))

/-- An off-line nontrivial zero would refute RH even though the vertical-line
Wirtinger bound remains available on that line. -/
theorem off_line_zero_refutes_rh {s : ℂ} (hs : NontrivialZero s) (hoff : s.re ≠ 1/2) :
    ¬ RiemannHypothesis := by
  intro hRH
  exact hoff (hRH s hs.1 hs.2.1 hs.2.2)

end RiemannZeroGaps
