-- Calculus companion to GapMirror.lean, checked with Lean v4.34.0-rc2 and
-- Mathlib 85e3a25e006c35636f0e53b0e9296caca2685bc0.
-- The supplied draft is preserved separately. This copy uses focused imports and a distinct
-- namespace so it can coexist with the rational file. Axiom reports are included below.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# The gap toy's mirror

A flat bump of height `u`, with no spreading, obeys `u' = u^2 - g * u`, where `g > 0` is the gap.
A bump that starts below the gap fades (`fades`), a bump that starts on the gap stays put (`edge`),
and a bump that starts above the gap blows up at the finite time `blowTime` (`blows_up`).

The mirror variable `z = 1 - g / u` turns the rule into `z' = g * z` (`z_grows`), so `z` only grows
like `exp (g * t)`. The edge `u = g` is `z = 0`, blow-up is `z = 1`, and half the edge `u = g / 2`
is `z = -1`. Flipping the sign of `z` pairs every bump above the edge with one below it
(`mirror`, `z_mirror`). The pair stays matched at every moment (`mirror_sum`):

  `g / (bump above) + g / (bump below) = 2`.

So the bump above blows up at exactly the time its mirror falls to half the edge (`mirror_time`).

`blowTime_pos` verifies that this time is in the future when `0 < g < A`. The blow-up theorem
is a left-hand limit: Lean's total division still assigns zero to the formula at the pole itself.
These statements concern the explicit scalar solution, with no spatial spreading.
-/

open Real Filter Topology

namespace GapMirrorCalculus

/-- The mirror variable. -/
noncomputable def z (g u : ℝ) : ℝ := 1 - g / u

/-- The mirror bump: the height on the other side of the edge with the opposite `z`. -/
noncomputable def mirror (g A : ℝ) : ℝ := g * A / (2 * A - g)

/-- The flat bump at time `t` that starts at height `A`. -/
noncomputable def bump (g A t : ℝ) : ℝ := g / (1 - z g A * exp (g * t))

/-- The blow-up time of a bump that starts at height `A` above the gap. -/
noncomputable def blowTime (g A : ℝ) : ℝ := log (A / (A - g)) / g

/-- The mirror variable only grows: if `u' = u^2 - g * u`, then `z = 1 - g / u` obeys `z' = g * z`. -/
theorem z_grows (g : ℝ) (u : ℝ → ℝ) (u' t : ℝ) (hu : HasDerivAt u u' t) (h0 : u t ≠ 0)
    (hode : u' = u t ^ 2 - g * u t) :
    HasDerivAt (fun s => z g (u s)) (g * z g (u t)) t := by
  have h1 : HasDerivAt (fun s => g / u s) ((0 * u t - g * u') / u t ^ 2) t :=
    (hasDerivAt_const t g).div hu h0
  have h2 : HasDerivAt (fun s => 1 - g / u s) (0 - (0 * u t - g * u') / u t ^ 2) t :=
    (hasDerivAt_const t (1 : ℝ)).sub h1
  have he : g * z g (u t) = 0 - (0 * u t - g * u') / u t ^ 2 := by
    rw [hode]
    unfold z
    field_simp
    ring
  rw [he]
  exact h2

/-- The mirror bump has the opposite `z`. -/
theorem z_mirror (g A : ℝ) (hg : g ≠ 0) (hA : A ≠ 0) (_h2 : 2 * A - g ≠ 0) :
    z g (mirror g A) = - z g A := by
  unfold z mirror
  field_simp [hg, hA]
  ring

/-- The bump starts at height `A`. -/
theorem bump_zero (g A : ℝ) (hg : g ≠ 0) (hA : A ≠ 0) : bump g A 0 = A := by
  unfold bump z
  simp
  field_simp

/-- The bump obeys the rule `u' = u^2 - g * u` for as long as it is finite. -/
theorem bump_solves (g A t : ℝ) (hd : 1 - z g A * exp (g * t) ≠ 0) :
    HasDerivAt (bump g A) (bump g A t ^ 2 - g * bump g A t) t := by
  have hE : HasDerivAt (fun s => exp (g * s)) (exp (g * t) * (g * 1)) t :=
    ((hasDerivAt_id t).const_mul g).exp
  have hden : HasDerivAt (fun s => 1 - z g A * exp (g * s))
      (0 - z g A * (exp (g * t) * (g * 1))) t :=
    (hasDerivAt_const t (1 : ℝ)).sub (hE.const_mul (z g A))
  have h := (hasDerivAt_const t g).div hden hd
  have he : bump g A t ^ 2 - g * bump g A t
      = (0 * (1 - z g A * exp (g * t)) - g * (0 - z g A * (exp (g * t) * (g * 1))))
        / (1 - z g A * exp (g * t)) ^ 2 := by
    unfold bump
    field_simp
    ring
  rw [he]
  exact h

/-- A bump that starts exactly on the gap stays there. -/
theorem edge (g t : ℝ) (hg : g ≠ 0) : bump g g t = g := by
  unfold bump z
  simp [div_self hg]

/-- Below the gap the bump fades to nothing. -/
theorem fades (g A : ℝ) (hg : 0 < g) (hA0 : 0 < A) (hA : A < g) :
    Tendsto (bump g A) atTop (𝓝 0) := by
  have hz : z g A < 0 := by
    unfold z
    have : 1 < g / A := by rw [lt_div_iff₀ hA0]; linarith
    linarith
  have hexp : Tendsto (fun t : ℝ => exp (g * t)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hg)
  have hmul : Tendsto (fun t : ℝ => (- z g A) * exp (g * t)) atTop atTop :=
    hexp.const_mul_atTop (by linarith)
  have hden : Tendsto (fun t : ℝ => 1 - z g A * exp (g * t)) atTop atTop := by
    have := tendsto_atTop_add_const_left atTop (1 : ℝ) hmul
    refine this.congr (fun t => ?_)
    ring
  exact tendsto_const_nhds.div_atTop hden

/-- Above the gap, `z` reaches `1` exactly at `blowTime`. -/
theorem blow_at (g A : ℝ) (hg : 0 < g) (hA : g < A) :
    z g A * exp (g * blowTime g A) = 1 := by
  have hA0 : 0 < A := by linarith
  have hAg : 0 < A - g := by linarith
  have hpos : 0 < A / (A - g) := div_pos hA0 hAg
  have hT : g * blowTime g A = log (A / (A - g)) := by
    unfold blowTime
    field_simp
  rw [hT, exp_log hpos]
  unfold z
  field_simp

/-- Before `blowTime` the bump is still finite: its denominator is above zero. -/
theorem finite_before (g A t : ℝ) (hg : 0 < g) (hA : g < A) (ht : t < blowTime g A) :
    0 < 1 - z g A * exp (g * t) := by
  have hA0 : 0 < A := by linarith
  have hz : 0 < z g A := by
    unfold z
    have : g / A < 1 := by rw [div_lt_one hA0]; exact hA
    linarith
  have hlt : exp (g * t) < exp (g * blowTime g A) :=
    exp_lt_exp.mpr (mul_lt_mul_of_pos_left ht hg)
  have := mul_lt_mul_of_pos_left hlt hz
  rw [blow_at g A hg hA] at this
  linarith

/-- The blow-up time is strictly in the future for an above-gap positive bump. -/
theorem blowTime_pos (g A : ℝ) (hg : 0 < g) (hA : g < A) :
    0 < blowTime g A := by
  have hAg : 0 < A - g := sub_pos.mpr hA
  have hratio : 1 < A / (A - g) := by
    rw [lt_div_iff₀ hAg]
    linarith
  exact div_pos (log_pos hratio) hg

/-- Above the gap the bump blows up as time reaches `blowTime`. -/
theorem blows_up (g A : ℝ) (hg : 0 < g) (hA : g < A) :
    Tendsto (bump g A) (𝓝[<] blowTime g A) atTop := by
  have hcont : Continuous (fun t : ℝ => 1 - z g A * exp (g * t)) := by fun_prop
  have h0 : 1 - z g A * exp (g * blowTime g A) = 0 := by
    rw [blow_at g A hg hA]; ring
  have hlim : Tendsto (fun t : ℝ => 1 - z g A * exp (g * t)) (𝓝[<] blowTime g A) (𝓝 0) := by
    have := hcont.continuousAt.tendsto (x := blowTime g A)
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun t : ℝ => 1 - z g A * exp (g * t)) (𝓝[<] blowTime g A) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact finite_before g A t hg hA ht
  have hinv := tendsto_inv_nhdsGT_zero.comp hden
  have hfin := hinv.const_mul_atTop hg
  refine hfin.congr (fun t => ?_)
  unfold bump
  simp [div_eq_mul_inv]

/-- The mirror pair stays matched at every moment. -/
theorem mirror_sum (g A t : ℝ) (hg : g ≠ 0) (hA : A ≠ 0) (h2 : 2 * A - g ≠ 0) :
    g / bump g A t + g / bump g (mirror g A) t = 2 := by
  have key : ∀ B : ℝ, g / bump g B t = 1 - z g B * exp (g * t) := by
    intro B
    unfold bump
    exact div_div_cancel₀ hg
  rw [key, key, z_mirror g A hg hA h2]
  ring

/-- The bump above blows up exactly when its mirror has fallen to half the edge. -/
theorem mirror_time (g A : ℝ) (hg : 0 < g) (hA : g < A) :
    bump g (mirror g A) (blowTime g A) = g / 2 := by
  have hA0 : A ≠ 0 := by linarith
  have h2 : 2 * A - g ≠ 0 := by linarith
  unfold bump
  rw [z_mirror g A hg.ne' hA0 h2, neg_mul, blow_at g A hg hA]
  norm_num

end GapMirrorCalculus

#print axioms GapMirrorCalculus.z_grows
#print axioms GapMirrorCalculus.z_mirror
#print axioms GapMirrorCalculus.bump_zero
#print axioms GapMirrorCalculus.bump_solves
#print axioms GapMirrorCalculus.edge
#print axioms GapMirrorCalculus.fades
#print axioms GapMirrorCalculus.blow_at
#print axioms GapMirrorCalculus.finite_before
#print axioms GapMirrorCalculus.blowTime_pos
#print axioms GapMirrorCalculus.blows_up
#print axioms GapMirrorCalculus.mirror_sum
#print axioms GapMirrorCalculus.mirror_time
