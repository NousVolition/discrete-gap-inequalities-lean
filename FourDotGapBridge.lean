import RingGapBridge

/-!
# A four-dot map preserving continuous heat motion and the alternating reflection

The ring pattern is `(0, a, 0, -a)`. Its heat generator is `-2` times the pattern,
so continuous heat gives the signed amplitude `a * exp (-2*t)`. The readout
`height a = 2*a/(a-1)` obeys the scalar gap equation with `g = 2`, with the same clock.
The existing `RingGapBridge.flip` sends the pattern with amplitude `a` to the pattern
with amplitude `-a`; `height_reflection` identifies this with the gap toy's mirror.

For initial amplitude `a > 1`, `preserves_motion_and_reflection` proves both correspondences
on the forward interval before `poleTime a = log a / 2`, with finite positive readouts.
The upper readout diverges from the left at that time, its mirror equals `1`, and the ring
itself remains continuous there. This is a pole of the readout, not a blow-up of heat flow.

This map retains signed amplitude and is different from `RingGapBridge.height`, which
uses cost/size. The motion here is continuous heat, not an Euler step with the same duration.
The two algebraic motion formulas also agree at totalized poles in Lean; the main interval
theorem excludes those points from the finite-height interpretation.
-/

open Real Filter Topology

namespace FourDotGapBridge

noncomputable def shape (j : ZMod 4) : ℝ :=
  if j.val = 1 then 1 else if j.val = 3 then -1 else 0

noncomputable def pattern (a : ℝ) (j : ZMod 4) : ℝ := a * shape j

/-- The neighbor expression in the repository's ring heat rule. -/
noncomputable def heatGenerator (f : ZMod 4 → ℝ) (j : ZMod 4) : ℝ :=
  f (j + 1) - 2 * f j + f (j - 1)

noncomputable def amplitude (a t : ℝ) : ℝ := a * exp (-2 * t)

noncomputable def flow (a t : ℝ) : ZMod 4 → ℝ := pattern (amplitude a t)

noncomputable def height (a : ℝ) : ℝ := 2 * a / (a - 1)

/-- On the displayed family, dot 1 is precisely the signed amplitude. -/
noncomputable def readout (f : ZMod 4 → ℝ) : ℝ := height (f 1)

noncomputable def poleTime (a : ℝ) : ℝ := log a / 2

theorem shape_flip : RingGapBridge.flip shape = fun j => -shape j := by
  funext j
  fin_cases j
  · change (1 : ℝ) * 0 = -0
    norm_num
  · change ((-1 : ℝ) ^ 1) * 1 = -1
    norm_num
  · change ((-1 : ℝ) ^ 2) * 0 = -0
    norm_num
  · change ((-1 : ℝ) ^ 3) * (-1) = -(-1)
    norm_num

theorem shape_heat (j : ZMod 4) : heatGenerator shape j = -2 * shape j := by
  fin_cases j
  · change (1 : ℝ) - 2 * 0 + -1 = -2 * 0
    norm_num
  · change (0 : ℝ) - 2 * 1 + 0 = -2 * 1
    norm_num
  · change (-1 : ℝ) - 2 * 0 + 1 = -2 * 0
    norm_num
  · change (0 : ℝ) - 2 * (-1) + 0 = -2 * (-1)
    norm_num

theorem pattern_flip (a : ℝ) : RingGapBridge.flip (pattern a) = pattern (-a) := by
  funext j
  have h : (-1 : ℝ) ^ j.val * shape j = -shape j := congrFun shape_flip j
  change (-1 : ℝ) ^ j.val * (a * shape j) = (-a) * shape j
  calc
    (-1 : ℝ) ^ j.val * (a * shape j) = a * ((-1 : ℝ) ^ j.val * shape j) := by ring
    _ = (-a) * shape j := by rw [h]; ring

theorem pattern_heat (a : ℝ) (j : ZMod 4) :
    heatGenerator (pattern a) j = -2 * pattern a j := by
  calc
    heatGenerator (pattern a) j = a * heatGenerator shape j := by
      unfold heatGenerator pattern
      ring
    _ = -2 * pattern a j := by rw [shape_heat]; unfold pattern; ring

theorem amplitude_zero (a : ℝ) : amplitude a 0 = a := by simp [amplitude]

theorem amplitude_neg (a t : ℝ) : amplitude (-a) t = -amplitude a t := by
  unfold amplitude
  ring

theorem amplitude_deriv (a t : ℝ) :
    HasDerivAt (amplitude a) (-2 * amplitude a t) t := by
  have h := (((hasDerivAt_id t).const_mul (-2 : ℝ)).exp).const_mul a
  change HasDerivAt (fun s : ℝ => a * exp (-2 * s)) (-2 * (a * exp (-2 * t))) t
  simpa only [id_eq, mul_one, one_mul, mul_assoc, mul_left_comm, mul_comm] using h

theorem flow_zero (a : ℝ) : flow a 0 = pattern a := by rw [flow, amplitude_zero]

theorem flow_flip (a t : ℝ) : RingGapBridge.flip (flow a t) = flow (-a) t := by
  unfold flow
  rw [pattern_flip, amplitude_neg]

/-- Every dot of the explicit trajectory satisfies the continuous ring heat equation. -/
theorem continuous_heat (a t : ℝ) (j : ZMod 4) :
    HasDerivAt (fun s => flow a s j) (heatGenerator (flow a t) j) t := by
  have h := (amplitude_deriv a t).mul_const (shape j)
  unfold flow
  rw [pattern_heat]
  simpa only [pattern, mul_assoc] using h

theorem readout_pattern (a : ℝ) : readout (pattern a) = height a := by
  simp only [readout, pattern, show shape (1 : ZMod 4) = 1 by rfl, mul_one]

theorem readout_flow (a t : ℝ) : readout (flow a t) = height (amplitude a t) := by
  exact readout_pattern _

theorem height_above_two (a : ℝ) (ha : 1 < a) : 2 < height a := by
  unfold height
  rw [lt_div_iff₀ (sub_pos.mpr ha)]
  linarith

/-- The alternating amplitude sign reversal is exactly the toy mirror, where both are finite. -/
theorem height_reflection (a : ℝ) (ha : a ≠ 1) (hna : a ≠ -1) :
    height (-a) = GapMirrorCalculus.mirror 2 (height a) := by
  have hp : a + 1 ≠ 0 := by intro h; apply hna; linarith
  have hn : height (-a) = 2 * a / (a + 1) := by
    unfold height
    rw [show -a - 1 = -(a + 1) by ring]
    simp only [mul_neg, neg_div_neg_eq]
  have hd : 2 * height a - 2 = 2 * (a + 1) / (a - 1) := by
    unfold height
    field_simp
    ring
  rw [hn]
  unfold GapMirrorCalculus.mirror
  rw [hd]
  unfold height
  field_simp

/-- Algebraic compatibility of amplitude decay and the existing real growth-factor formula. -/
theorem height_dilation (a r : ℝ) (ha : a ≠ 1) (hr : r ≠ 0) :
    height (a / r) = GapMirrorBridge.realStep 2 r (height a) := by
  have hd : r * 2 - (r - 1) * height a = 2 * (a - r) / (a - 1) := by
    unfold height
    field_simp
    ring
  have hn : a / r - 1 = (a - r) / r := by field_simp
  unfold GapMirrorBridge.realStep
  rw [hd]
  unfold height
  rw [hn]
  field_simp

/-- Exact same-clock motion. The identity includes Lean's totalized values at a pole;
the finite positive interval is established in `preserves_motion_and_reflection`. -/
theorem motion (a t : ℝ) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    readout (flow a t) = GapMirrorCalculus.bump 2 (height a) t := by
  have hu : height a ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) ha0) (sub_ne_zero.mpr ha1)
  rw [readout_flow, amplitude, show (-2 : ℝ) * t = -(2 * t) by ring,
    exp_neg, ← div_eq_mul_inv, height_dilation a (exp (2 * t)) ha1 (exp_ne_zero _)]
  exact GapMirrorBridge.real_step_at_time 2 (height a) t hu

/-- The readout satisfies the gap differential equation wherever its amplitude is not at the pole. -/
theorem readout_solves (a t : ℝ) (ht : amplitude a t ≠ 1) :
    HasDerivAt (fun s => readout (flow a s))
      ((readout (flow a t)) ^ 2 - 2 * readout (flow a t)) t := by
  have h := ((amplitude_deriv a t).const_mul 2).div
    ((amplitude_deriv a t).sub_const 1) (sub_ne_zero.mpr ht)
  have he : (2 * (-2 * amplitude a t) * (amplitude a t - 1) -
      2 * amplitude a t * (-2 * amplitude a t)) / (amplitude a t - 1) ^ 2 =
      (height (amplitude a t)) ^ 2 - 2 * height (amplitude a t) := by
    unfold height
    field_simp
    ring
  simp only [readout_flow]
  rw [← he]
  exact h

theorem pole_time_pos (a : ℝ) (ha : 1 < a) : 0 < poleTime a :=
  div_pos (log_pos ha) (by norm_num)

theorem amplitude_before_pole (a t : ℝ) (ha : 1 < a) (ht : t < poleTime a) :
    1 < amplitude a t := by
  have ha0 : 0 < a := by linarith
  have hlog : 2 * t < log a := by unfold poleTime at ht; linarith
  have he : exp (2 * t) < a := by
    rw [← exp_log ha0]
    exact exp_lt_exp.mpr hlog
  unfold amplitude
  rw [show (-2 : ℝ) * t = -(2 * t) by ring, exp_neg, ← div_eq_mul_inv]
  exact (lt_div_iff₀ (exp_pos _)).2 (by simpa using he)

theorem amplitude_at_pole (a : ℝ) (ha : 0 < a) : amplitude a (poleTime a) = 1 := by
  unfold amplitude poleTime
  rw [show (-2 : ℝ) * (log a / 2) = -log a by ring, exp_neg, exp_log ha]
  exact mul_inv_cancel₀ ha.ne'

theorem pole_eq_blowTime (a : ℝ) (ha : 1 < a) :
    poleTime a = GapMirrorCalculus.blowTime 2 (height a) := by
  have ha1 : a ≠ 1 := ne_of_gt ha
  have he : height a / (height a - 2) = a := by
    unfold height
    field_simp
    ring
  simp only [poleTime, GapMirrorCalculus.blowTime, he]

/-- The finite forward interval preserves both trajectories and their reflection, with the same clock. -/
theorem preserves_motion_and_reflection (a t : ℝ) (ha : 1 < a)
    (ht0 : 0 ≤ t) (ht : t < poleTime a) :
    0 < poleTime a ∧ 0 ≤ t ∧ 1 < amplitude a t ∧
    2 < readout (flow a t) ∧
    1 < readout (RingGapBridge.flip (flow a t)) ∧
    readout (RingGapBridge.flip (flow a t)) < 2 ∧
    readout (flow a t) = GapMirrorCalculus.bump 2 (height a) t ∧
    readout (RingGapBridge.flip (flow a t)) =
      GapMirrorCalculus.bump 2 (GapMirrorCalculus.mirror 2 (height a)) t ∧
    readout (RingGapBridge.flip (flow a t)) =
      GapMirrorCalculus.mirror 2 (readout (flow a t)) := by
  have ha0 : a ≠ 0 := by linarith
  have ha1 : a ≠ 1 := ne_of_gt ha
  have han : a ≠ -1 := by linarith
  have hb := amplitude_before_pole a t ha ht
  have hupper := height_above_two (amplitude a t) hb
  have href : readout (RingGapBridge.flip (flow a t)) =
      GapMirrorCalculus.mirror 2 (readout (flow a t)) := by
    rw [flow_flip, readout_flow, readout_flow, amplitude_neg]
    exact height_reflection _ (ne_of_gt hb) (by linarith)
  have hbetween := GapMirrorBridge.mirror_between 2 (height (amplitude a t))
    (by norm_num) hupper
  refine ⟨pole_time_pos a ha, ht0, hb, ?_, ?_, ?_, motion a t ha0 ha1, ?_, href⟩
  · rwa [readout_flow]
  · rw [href, readout_flow]
    simpa using hbetween.1
  · rw [href, readout_flow]
    exact hbetween.2
  · rw [flow_flip, motion (-a) t (neg_ne_zero.mpr ha0) (by linarith),
      height_reflection a ha1 han]

/-- Both readouts obey the gap ODE on that same interval. -/
theorem both_readouts_solve (a t : ℝ) (ha : 1 < a) (ht : t < poleTime a) :
    HasDerivAt (fun s => readout (flow a s))
      ((readout (flow a t)) ^ 2 - 2 * readout (flow a t)) t ∧
    HasDerivAt (fun s => readout (RingGapBridge.flip (flow a s)))
      ((readout (RingGapBridge.flip (flow a t))) ^ 2 -
        2 * readout (RingGapBridge.flip (flow a t))) t := by
  have hb := amplitude_before_pole a t ha ht
  refine ⟨readout_solves a t (ne_of_gt hb), ?_⟩
  simp only [flow_flip]
  apply readout_solves (-a) t
  rw [amplitude_neg]
  linarith

theorem readout_blows_up (a : ℝ) (ha : 1 < a) :
    Tendsto (fun t => readout (flow a t)) (𝓝[<] poleTime a) atTop := by
  have heq : (fun t => readout (flow a t)) = GapMirrorCalculus.bump 2 (height a) :=
    funext (fun t => motion a t (by linarith) (ne_of_gt ha))
  rw [heq, pole_eq_blowTime a ha]
  exact GapMirrorCalculus.blows_up 2 (height a) (by norm_num) (height_above_two a ha)

theorem flipped_at_pole (a : ℝ) (ha : 1 < a) :
    readout (RingGapBridge.flip (flow a (poleTime a))) = 1 := by
  rw [flow_flip, readout_flow, amplitude_neg, amplitude_at_pole a (by linarith)]
  norm_num [height]

/-- The ring has a finite, continuous value at the readout's blow-up time. -/
theorem ring_regular_at_pole (a : ℝ) (ha : 1 < a) :
    flow a (poleTime a) = pattern 1 ∧
      ∀ j : ZMod 4, ContinuousAt (fun t => flow a t j) (poleTime a) := by
  constructor
  · unfold flow
    rw [amplitude_at_pole a (by linarith)]
  · intro j
    exact (continuous_heat a (poleTime a) j).continuousAt

end FourDotGapBridge

#print axioms FourDotGapBridge.shape_flip
#print axioms FourDotGapBridge.shape_heat
#print axioms FourDotGapBridge.pattern_flip
#print axioms FourDotGapBridge.pattern_heat
#print axioms FourDotGapBridge.amplitude_zero
#print axioms FourDotGapBridge.amplitude_neg
#print axioms FourDotGapBridge.amplitude_deriv
#print axioms FourDotGapBridge.flow_zero
#print axioms FourDotGapBridge.flow_flip
#print axioms FourDotGapBridge.continuous_heat
#print axioms FourDotGapBridge.readout_pattern
#print axioms FourDotGapBridge.readout_flow
#print axioms FourDotGapBridge.height_above_two
#print axioms FourDotGapBridge.height_reflection
#print axioms FourDotGapBridge.height_dilation
#print axioms FourDotGapBridge.motion
#print axioms FourDotGapBridge.readout_solves
#print axioms FourDotGapBridge.pole_time_pos
#print axioms FourDotGapBridge.amplitude_before_pole
#print axioms FourDotGapBridge.amplitude_at_pole
#print axioms FourDotGapBridge.pole_eq_blowTime
#print axioms FourDotGapBridge.preserves_motion_and_reflection
#print axioms FourDotGapBridge.both_readouts_solve
#print axioms FourDotGapBridge.readout_blows_up
#print axioms FourDotGapBridge.flipped_at_pole
#print axioms FourDotGapBridge.ring_regular_at_pole
