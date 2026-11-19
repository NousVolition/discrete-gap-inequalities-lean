import TwoWaveDiscreteGapBridge

/-!
# A two-wave readout preserving heat motion and the actual ring flip

This is a new amplitude-dependent map. It does not replace either cost/size map.
Choose nonzero orthogonal real modes `v,w` exchanged by `RingGapBridge.flip`.
Their coefficients are recovered from the pattern by orthogonal projection.
For coefficients `a,b`, put `A = (a*|b| - b*|a|)/2` and `U = 4*A/(A-1)`.

The actual flip exchanges `a,b` and therefore negates `A`. On an even ring,
the eigenvalues of such a pair sum to 4. Continuous heat multiplies `A` by
`exp(-4*t)`, so `U` follows the gap equation with gap 4 and the same clock.
The readout is active exactly when `a*b < 0`. Same-sign coefficients give zero.
For the positive upper/mirror pair, require `A > 1` and `0 ≤ t < log(A)/4`.

For the actual discrete heat step, positive mode multipliers `cs,cr` give
`A_next = cs*cr*A`, exact factor `r = 1/(cs*cr)`, and clock `log(r)/4`.
All integer iterates are covered. On an active pair a positive amplitude scaling
is possible exactly when both multipliers are positive. Before a sampled pole,
`r^k < A` gives both the gap motion and the actual ring reflection.

The classification statements below concern this displayed construction and
linear amplitude readouts; they are not an impossibility claim about every map.
All finite-pair statements exclude both readout poles `A = 1` and `A = -1`.
-/

open Real Filter Topology Finset
open TwoWaveGapBridge

namespace TwoWaveFlipBridge

noncomputable def orient (a b : ℝ) : ℝ := (a * |b| - b * |a|) / 2

noncomputable def height (g A : ℝ) : ℝ := g * A / (A - 1)

noncomputable def decay (g A t : ℝ) : ℝ := A * exp (-g * t)

noncomputable def poleTime (g A : ℝ) : ℝ := log A / g

theorem orient_swap (a b : ℝ) : orient b a = -orient a b := by unfold orient; ring

theorem orient_pos_neg (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 0) : orient a b = -a * b := by
  rw [orient, abs_of_nonneg ha, abs_of_nonpos hb]
  ring

theorem orient_neg_pos (a b : ℝ) (ha : a ≤ 0) (hb : 0 ≤ b) : orient a b = a * b := by
  rw [orient, abs_of_nonpos ha, abs_of_nonneg hb]
  ring

theorem orient_zero_iff (a b : ℝ) : orient a b = 0 ↔ 0 ≤ a * b := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [orient, abs_of_nonneg ha, abs_of_nonneg hb]
    constructor <;> intro h
    · exact mul_nonneg ha hb
    · ring
  · rw [orient_pos_neg a b ha hb]
    have h := mul_nonpos_of_nonneg_of_nonpos ha hb
    constructor <;> intro h' <;> nlinarith
  · rw [orient_neg_pos a b ha hb]
    have h := mul_nonpos_of_nonpos_of_nonneg ha hb
    constructor <;> intro h' <;> nlinarith
  · rw [orient, abs_of_nonpos ha, abs_of_nonpos hb]
    constructor <;> intro h
    · exact mul_nonneg_of_nonpos_of_nonpos ha hb
    · ring

theorem orient_ne_zero_iff (a b : ℝ) : orient a b ≠ 0 ↔ a * b < 0 := by
  rw [ne_eq, orient_zero_iff, not_le]

theorem orient_positive_iff (a b : ℝ) : 0 < orient a b ↔ 0 < a ∧ b < 0 := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [orient, abs_of_nonneg ha, abs_of_nonneg hb]
    constructor <;> intro h <;> nlinarith
  · rw [orient_pos_neg a b ha hb]
    constructor
    · intro h
      constructor
      · by_contra hn; push Not at hn; have : a = 0 := le_antisymm hn ha; subst a; norm_num at h
      · by_contra hn; push Not at hn; have : b = 0 := le_antisymm hb hn; subst b; norm_num at h
    · rintro ⟨hap, hbn⟩
      exact mul_pos_of_neg_of_neg (neg_neg_of_pos hap) hbn
  · rw [orient_neg_pos a b ha hb]
    have h := mul_nonpos_of_nonpos_of_nonneg ha hb
    constructor <;> intro h' <;> nlinarith
  · rw [orient, abs_of_nonpos ha, abs_of_nonpos hb]
    constructor <;> intro h <;> nlinarith

theorem orient_scale (a b c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    orient (c * a) (d * b) = c * d * orient a b := by
  unfold orient
  rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hd]
  ring

/-- Distinct decay rates cause no problem: their sum controls the oriented product. -/
theorem orient_heat (ls lr a b t : ℝ) :
    orient (coefficient ls a t) (coefficient lr b t) = decay (ls + lr) (orient a b) t := by
  unfold coefficient
  rw [mul_comm a, mul_comm b, orient_scale _ _ _ _ (exp_pos _).le (exp_pos _).le,
    ← exp_add]
  unfold decay
  rw [show -ls * t + -lr * t = -(ls + lr) * t by ring]
  ring

theorem height_zero (g : ℝ) : height g 0 = 0 := by simp [height]

theorem height_nonzero_iff (g A : ℝ) (hg : g ≠ 0) (hA : A ≠ 1) :
    height g A ≠ 0 ↔ A ≠ 0 := by
  constructor
  · intro h h0
    rw [h0, height_zero] at h
    exact h rfl
  · intro h0
    exact div_ne_zero (mul_ne_zero hg h0) (sub_ne_zero.mpr hA)

theorem height_reflection (g A : ℝ) (hg : g ≠ 0) (hA : A ≠ 1) (hAn : A ≠ -1) :
    height g (-A) = GapMirrorCalculus.mirror g (height g A) := by
  have hp : A + 1 ≠ 0 := by intro h; apply hAn; linarith
  have hd : 2 * height g A - g = g * (A + 1) / (A - 1) := by
    unfold height
    field_simp
    ring
  unfold GapMirrorCalculus.mirror
  rw [hd]
  unfold height
  rw [show -A - 1 = -(A + 1) by ring]
  field_simp

theorem height_above_gap (g A : ℝ) (hg : 0 < g) (hA : 1 < A) : g < height g A := by
  unfold height
  rw [lt_div_iff₀ (sub_pos.mpr hA)]
  nlinarith

theorem height_dilation (g A r : ℝ) (hg : g ≠ 0) (hA : A ≠ 1) (hr : r ≠ 0) :
    height g (A / r) = GapMirrorBridge.realStep g r (height g A) := by
  have hd : r * g - (r - 1) * height g A = g * (A - r) / (A - 1) := by
    unfold height
    field_simp
    ring
  have hn : A / r - 1 = (A - r) / r := by field_simp
  unfold GapMirrorBridge.realStep
  rw [hd]
  unfold height
  rw [hn]
  field_simp

theorem height_motion (g A t : ℝ) (hg : g ≠ 0) (hA0 : A ≠ 0) (hA1 : A ≠ 1) :
    height g (decay g A t) = GapMirrorCalculus.bump g (height g A) t := by
  have hu : height g A ≠ 0 := (height_nonzero_iff g A hg hA1).2 hA0
  rw [decay, show -g * t = -(g * t) by ring, exp_neg, ← div_eq_mul_inv,
    height_dilation g A (exp (g * t)) hg hA1 (exp_ne_zero _)]
  exact GapMirrorBridge.real_step_at_time _ _ _ hu

theorem decay_before_pole (g A t : ℝ) (hg : 0 < g) (hA : 1 < A) (ht : t < poleTime g A) :
    1 < decay g A t := by
  have hlog : g * t < log A := by
    apply (lt_div_iff₀ hg).mp at ht
    simpa only [mul_comm] using ht
  have he : exp (g * t) < A := by rw [← exp_log (by linarith : 0 < A)]; exact exp_lt_exp.mpr hlog
  unfold decay
  rw [show -g * t = -(g * t) by ring, exp_neg, ← div_eq_mul_inv]
  exact (lt_div_iff₀ (exp_pos _)).2 (by simpa using he)

theorem pole_eq_blowTime (g A : ℝ) (hg : 0 < g) (hA : 1 < A) :
    poleTime g A = GapMirrorCalculus.blowTime g (height g A) := by
  have hA1 : A ≠ 1 := ne_of_gt hA
  have he : height g A / (height g A - g) = A := by
    unfold height
    field_simp
    ring
  simp only [poleTime, GapMirrorCalculus.blowTime, he]

/-- The two denominators defining a finite mirrored pair are nonzero exactly here. -/
theorem finite_pair_iff (A : ℝ) :
    A - 1 ≠ 0 ∧ -A - 1 ≠ 0 ↔ A ≠ 1 ∧ A ≠ -1 := by
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> intro h
  · apply h1; linarith
  · apply h2; linarith
  · apply h1; linarith
  · apply h2; linarith

/-- For this height formula, a nonzero amplitude decaying at rate σ needs gap g = σ
to preserve the continuous clock. The zero readout is excluded from this classification. -/
theorem matching_rate_iff (g σ A : ℝ) (hg : g ≠ 0) (hA0 : A ≠ 0) (hA1 : A ≠ 1) :
    g * σ * A / (A - 1) ^ 2 = (height g A) ^ 2 - g * height g A ↔ σ = g := by
  have hden : (A - 1) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hA1)
  have he : (height g A) ^ 2 - g * height g A = g * g * A / (A - 1) ^ 2 := by
    unfold height
    field_simp
    ring
  rw [he, div_left_inj' hden]
  constructor
  · intro h
    have hz : (g * A) * (σ - g) = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero hg hA0))
  · intro h; rw [h]

/-- A nonzero linear amplitude readout preserves both swap/sign reflection and the
heat decay rate exactly when its coefficients are opposite and both rates equal g. -/
theorem linear_readout_iff (ls lr g c d : ℝ) (hc : c ≠ 0) :
    ((∀ a b : ℝ, c * b + d * a = -(c * a + d * b)) ∧
     (∀ a b : ℝ, c * (-ls * a) + d * (-lr * b) = -g * (c * a + d * b))) ↔
      d = -c ∧ ls = g ∧ lr = g := by
  constructor
  · rintro ⟨hf, hh⟩
    have hd : d = -c := by simpa using hf 1 0
    refine ⟨hd, ?_, ?_⟩
    · have h := hh 1 0
      have hz : c * (ls - g) = 0 := by nlinarith only [h]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hc)
    · have h := hh 0 1
      have hz : c * (lr - g) = 0 := by rw [hd] at h; nlinarith only [h]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hc)
  · rintro ⟨rfl, rfl, rfl⟩
    constructor <;> intro a b <;> ring


theorem decay_deriv (g A t : ℝ) :
    HasDerivAt (decay g A) (-g * decay g A t) t := by
  have h := (((hasDerivAt_id t).const_mul (-g)).exp).const_mul A
  change HasDerivAt (fun s : ℝ => A * exp (-g * s)) (-g * (A * exp (-g * t))) t
  simpa only [id_eq, mul_one, one_mul, mul_assoc, mul_left_comm, mul_comm] using h

theorem height_deriv (g σ A t : ℝ) (ht : decay σ A t ≠ 1) :
    HasDerivAt (fun s => height g (decay σ A s))
      (g * σ * decay σ A t / (decay σ A t - 1) ^ 2) t := by
  have h := ((decay_deriv σ A t).const_mul g).div
    ((decay_deriv σ A t).sub_const 1) (sub_ne_zero.mpr ht)
  have he : ((g * (-σ * decay σ A t)) * (decay σ A t - 1) -
      (g * decay σ A t) * (-σ * decay σ A t)) / (decay σ A t - 1) ^ 2 =
      g * σ * decay σ A t / (decay σ A t - 1) ^ 2 := by ring
  change HasDerivAt (fun s => height g (decay σ A s)) _ t at h
  rwa [he] at h

/-- Necessary and sufficient same-clock ODE condition for a nonstationary readout. -/
theorem solves_iff (g σ A t : ℝ) (hg : g ≠ 0) (hA : A ≠ 0) (ht : decay σ A t ≠ 1) :
    HasDerivAt (fun s => height g (decay σ A s))
      ((height g (decay σ A t)) ^ 2 - g * height g (decay σ A t)) t ↔ σ = g := by
  have hd := height_deriv g σ A t ht
  have hn : decay σ A t ≠ 0 := mul_ne_zero hA (exp_ne_zero _)
  constructor
  · intro h
    exact (matching_rate_iff g σ (decay σ A t) hg hn ht).mp (hd.unique h)
  · intro h
    rw [(matching_rate_iff g σ (decay σ A t) hg hn ht).mpr h] at hd
    exact hd

/-- With complementary ring rates, a nonzero linear readout works only at the middle rate 2. -/
theorem linear_paired_iff (ls lr g c d : ℝ) (hc : c ≠ 0) (hp : ls + lr = 4) :
    ((∀ a b : ℝ, c * b + d * a = -(c * a + d * b)) ∧
     (∀ a b : ℝ, c * (-ls * a) + d * (-lr * b) = -g * (c * a + d * b))) ↔
      d = -c ∧ ls = 2 ∧ lr = 2 ∧ g = 2 := by
  rw [linear_readout_iff ls lr g c d hc]
  constructor
  · rintro ⟨hd, hs, hr⟩
    exact ⟨hd, by linarith, by linarith, by linarith⟩
  · rintro ⟨hd, hs, hr, hg⟩
    exact ⟨hd, by linarith, by linarith⟩

section Ring

variable {n : ℕ} [NeZero n]

noncomputable def modal (v f : ZMod n → ℝ) : ℝ := dot v f / RingGapBridge.size v

noncomputable def amplitude (v w f : ZMod n → ℝ) : ℝ := orient (modal v f) (modal w f)

noncomputable def readout (v w f : ZMod n → ℝ) : ℝ := height 4 (amplitude v w f)

theorem sign_prev (hn : Even n) (j : ZMod n) :
    (-1 : ℝ) ^ (j - 1).val = -((-1 : ℝ) ^ j.val) := by
  have h := RingGapBridge.sign_next hn (j - 1)
  rw [sub_add_cancel] at h
  linarith

/-- The actual alternating flip complements the positive Laplacian eigenvalue. -/
theorem heat_flip (hn : Even n) (f : ZMod n → ℝ) (j : ZMod n) :
    heatGenerator (RingGapBridge.flip f) j =
      -4 * RingGapBridge.flip f j - RingGapBridge.flip (heatGenerator f) j := by
  unfold heatGenerator RingGapBridge.flip
  rw [RingGapBridge.sign_next hn, sign_prev hn]
  ring

theorem flipped_eigen (hn : Even n) (l : ℝ) (v : ZMod n → ℝ)
    (hv : ∀ j, heatGenerator v j = -l * v j) (j : ZMod n) :
    heatGenerator (RingGapBridge.flip v) j = -(4 - l) * RingGapBridge.flip v j := by
  rw [heat_flip hn]
  change -4 * RingGapBridge.flip v j - (-1 : ℝ) ^ j.val * heatGenerator v j = _
  rw [hv]
  unfold RingGapBridge.flip
  ring

omit [NeZero n] in
theorem flip_reverse (v w : ZMod n → ℝ) (hf : RingGapBridge.flip v = w) :
    RingGapBridge.flip w = v := by rw [← hf, RingGapBridge.flip_flip]

theorem paired_eigenvalues (hn : Even n) (ls lr : ℝ) (v w : ZMod n → ℝ)
    (hv : ∀ j, heatGenerator v j = -ls * v j) (hw : ∀ j, heatGenerator w j = -lr * w j)
    (hf : RingGapBridge.flip v = w) (hNv : RingGapBridge.size v ≠ 0) : ls + lr = 4 := by
  have he : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    apply hNv
    simp [RingGapBridge.size, h]
  obtain ⟨j, hj⟩ := he
  have h := flipped_eigen hn lr w hw j
  rw [flip_reverse v w hf, hv] at h
  have hz : (ls + lr - 4) * v j = 0 := by nlinarith
  have := (mul_eq_zero.mp hz).resolve_right hj
  linarith

theorem dot_flip (v f : ZMod n → ℝ) :
    dot v (RingGapBridge.flip f) = dot (RingGapBridge.flip v) f := by
  unfold dot RingGapBridge.flip
  apply sum_congr rfl
  intro j _
  ring

theorem modal_flip (v w f : ZMod n → ℝ) (hf : RingGapBridge.flip v = w) :
    modal v (RingGapBridge.flip f) = modal w f := by
  have hN : RingGapBridge.size w = RingGapBridge.size v := by
    rw [← hf, RingGapBridge.size_flip]
  unfold modal
  rw [dot_flip, hf, hN]

/-- This negates the amplitude for the actual spatial flip, even off the two-mode plane. -/
theorem amplitude_flip (v w f : ZMod n → ℝ) (hf : RingGapBridge.flip v = w) :
    amplitude v w (RingGapBridge.flip f) = -amplitude v w f := by
  unfold amplitude
  rw [modal_flip v w f hf, modal_flip w v f (flip_reverse v w hf), orient_swap]

theorem readout_flip (v w f : ZMod n → ℝ) (hf : RingGapBridge.flip v = w)
    (h1 : amplitude v w f ≠ 1) (hn : amplitude v w f ≠ -1) :
    readout v w (RingGapBridge.flip f) = GapMirrorCalculus.mirror 4 (readout v w f) := by
  unfold readout
  rw [amplitude_flip v w f hf]
  exact height_reflection 4 _ (by norm_num) h1 hn

theorem modal_mix_left (a b : ℝ) (v w : ZMod n → ℝ) (ho : dot v w = 0)
    (hNv : RingGapBridge.size v ≠ 0) : modal v (mix a b v w) = a := by
  have hv : mix 1 0 v w = v := by funext j; simp [mix]
  have h := dot_mix 1 0 a b v w ho
  rw [hv] at h
  simp only [one_mul, zero_mul, add_zero] at h
  unfold modal
  rw [h, mul_div_cancel_right₀ _ hNv]

theorem modal_mix_right (a b : ℝ) (v w : ZMod n → ℝ) (ho : dot v w = 0)
    (hNw : RingGapBridge.size w ≠ 0) : modal w (mix a b v w) = b := by
  have hw : mix 0 1 v w = w := by funext j; simp [mix]
  have h := dot_mix 0 1 a b v w ho
  rw [hw] at h
  simp only [one_mul, zero_mul, zero_add] at h
  unfold modal
  rw [h, mul_div_cancel_right₀ _ hNw]

theorem amplitude_mix (a b : ℝ) (v w : ZMod n → ℝ) (ho : dot v w = 0)
    (hNv : RingGapBridge.size v ≠ 0) (hNw : RingGapBridge.size w ≠ 0) :
    amplitude v w (mix a b v w) = orient a b := by
  rw [amplitude, modal_mix_left a b v w ho hNv, modal_mix_right a b v w ho hNw]

theorem readout_mix (a b : ℝ) (v w : ZMod n → ℝ) (ho : dot v w = 0)
    (hNv : RingGapBridge.size v ≠ 0) (hNw : RingGapBridge.size w ≠ 0) :
    readout v w (mix a b v w) = height 4 (orient a b) := by
  rw [readout, amplitude_mix a b v w ho hNv hNw]

theorem active_iff (a b : ℝ) (v w : ZMod n → ℝ) (ho : dot v w = 0)
    (hNv : RingGapBridge.size v ≠ 0) (hNw : RingGapBridge.size w ≠ 0) (hA : orient a b ≠ 1) :
    readout v w (mix a b v w) ≠ 0 ↔ a * b < 0 := by
  rw [readout_mix a b v w ho hNv hNw, height_nonzero_iff 4 _ (by norm_num) hA,
    orient_ne_zero_iff]

omit [NeZero n] in
theorem flip_mix (a b : ℝ) (v w : ZMod n → ℝ) (hf : RingGapBridge.flip v = w) :
    RingGapBridge.flip (mix a b v w) = mix b a v w := by
  have hr := flip_reverse v w hf
  funext j
  have hv := congrFun hf j
  have hw := congrFun hr j
  change (-1 : ℝ) ^ j.val * (a * v j + b * w j) = b * v j + a * w j
  change (-1 : ℝ) ^ j.val * v j = w j at hv
  change (-1 : ℝ) ^ j.val * w j = v j at hw
  calc
    (-1 : ℝ) ^ j.val * (a * v j + b * w j) =
      a * ((-1 : ℝ) ^ j.val * v j) + b * ((-1 : ℝ) ^ j.val * w j) := by ring
    _ = b * v j + a * w j := by rw [hv, hw]; ring

theorem amplitude_flow (ls lr a b t : ℝ) (v w : ZMod n → ℝ) (ho : dot v w = 0)
    (hNv : RingGapBridge.size v ≠ 0) (hNw : RingGapBridge.size w ≠ 0) :
    amplitude v w (ringFlow ls lr a b v w t) = decay (ls + lr) (orient a b) t := by
  rw [ringFlow, amplitude_mix _ _ v w ho hNv hNw, orient_heat]

theorem flow_readout (ls lr a b t : ℝ) (v w : ZMod n → ℝ) (ho : dot v w = 0)
    (hNv : RingGapBridge.size v ≠ 0) (hNw : RingGapBridge.size w ≠ 0) (hp : ls + lr = 4) :
    readout v w (ringFlow ls lr a b v w t) = height 4 (decay 4 (orient a b) t) := by
  rw [readout, amplitude_flow ls lr a b t v w ho hNv hNw, hp]

theorem paired_motion_and_flip (hn : Even n) (ls lr a b t : ℝ) (v w : ZMod n → ℝ)
    (hv : ∀ j, heatGenerator v j = -ls * v j) (hw : ∀ j, heatGenerator w j = -lr * w j)
    (hf : RingGapBridge.flip v = w) (ho : dot v w = 0) (hNv : RingGapBridge.size v ≠ 0)
    (hA : 1 < orient a b) (ht0 : 0 ≤ t) (ht : t < poleTime 4 (orient a b)) :
    0 ≤ t ∧
    readout v w (ringFlow ls lr a b v w t) =
      GapMirrorCalculus.bump 4 (readout v w (mix a b v w)) t ∧
    readout v w (RingGapBridge.flip (ringFlow ls lr a b v w t)) =
      GapMirrorCalculus.mirror 4 (readout v w (ringFlow ls lr a b v w t)) ∧
    readout v w (ringFlow ls lr b a v w t) =
      GapMirrorCalculus.bump 4 (readout v w (RingGapBridge.flip (mix a b v w))) t ∧
    readout v w (ringFlow ls lr b a v w t) =
      readout v w (RingGapBridge.flip (ringFlow ls lr a b v w t)) ∧
    4 < readout v w (ringFlow ls lr a b v w t) ∧
    2 < readout v w (RingGapBridge.flip (ringFlow ls lr a b v w t)) ∧
    readout v w (RingGapBridge.flip (ringFlow ls lr a b v w t)) < 4 := by
  have hp := paired_eigenvalues hn ls lr v w hv hw hf hNv
  have hNw : RingGapBridge.size w ≠ 0 := by rw [← hf, RingGapBridge.size_flip]; exact hNv
  have hq := decay_before_pole 4 (orient a b) t (by norm_num) hA ht
  have hcur : amplitude v w (ringFlow ls lr a b v w t) = decay 4 (orient a b) t := by
    rw [amplitude_flow ls lr a b t v w ho hNv hNw, hp]
  have href := readout_flip v w (ringFlow ls lr a b v w t) hf
    (by rw [hcur]; linarith) (by rw [hcur]; linarith)
  have hupper : 4 < readout v w (ringFlow ls lr a b v w t) := by
    rw [flow_readout ls lr a b t v w ho hNv hNw hp]
    exact height_above_gap 4 _ (by norm_num) hq
  have hbounds := GapMirrorBridge.mirror_between 4
    (readout v w (ringFlow ls lr a b v w t)) (by norm_num) hupper
  refine ⟨ht0, ?_, href, ?_, ?_, hupper, ?_, ?_⟩
  · rw [flow_readout ls lr a b t v w ho hNv hNw hp, readout_mix a b v w ho hNv hNw]
    exact height_motion 4 _ t (by norm_num) (by linarith) (by linarith)
  · rw [flip_mix a b v w hf, flow_readout ls lr b a t v w ho hNv hNw hp,
      readout_mix b a v w ho hNv hNw, orient_swap]
    exact height_motion 4 _ t (by norm_num) (by linarith) (by linarith)
  · rw [flow_readout ls lr b a t v w ho hNv hNw hp, orient_swap]
    unfold readout
    rw [amplitude_flip v w _ hf, hcur]
    congr 1
    unfold decay
    ring
  · rw [href]; norm_num at hbounds ⊢; exact hbounds.1
  · rw [href]; exact hbounds.2

end Ring


noncomputable def signedMultiplier (c d : ℝ) : ℝ := (c * |d| + d * |c|) / 2

theorem signed_multiplier_positive_iff (c d : ℝ) :
    0 < signedMultiplier c d ↔ 0 < c ∧ 0 < d := by
  rcases le_total 0 c with hc | hc <;> rcases le_total 0 d with hd | hd
  · have he : signedMultiplier c d = c * d := by
      rw [signedMultiplier, abs_of_nonneg hc, abs_of_nonneg hd]; ring
    rw [he]
    constructor
    · intro h
      rcases mul_pos_iff.mp h with hp | hn
      · exact hp
      · obtain ⟨hnc, _⟩ := hn; linarith
    · rintro ⟨h1, h2⟩; exact mul_pos h1 h2
  · have he : signedMultiplier c d = 0 := by
      rw [signedMultiplier, abs_of_nonneg hc, abs_of_nonpos hd]; ring
    rw [he]
    constructor
    · intro h; linarith
    · rintro ⟨_, h⟩; linarith
  · have he : signedMultiplier c d = 0 := by
      rw [signedMultiplier, abs_of_nonpos hc, abs_of_nonneg hd]; ring
    rw [he]
    constructor
    · intro h; linarith
    · rintro ⟨h, _⟩; linarith
  · have he : signedMultiplier c d = -(c * d) := by
      rw [signedMultiplier, abs_of_nonpos hc, abs_of_nonpos hd]; ring
    have hp := mul_nonneg_of_nonpos_of_nonpos hc hd
    rw [he]
    constructor
    · intro h; linarith
    · rintro ⟨h, _⟩; linarith

theorem orient_scaled_opposite (a b c d : ℝ) (hab : a * b < 0) :
    orient (c * a) (d * b) = signedMultiplier c d * orient a b := by
  have he : b * |a| = -(a * |b|) := by
    rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
    · have := mul_nonneg ha hb; linarith
    · rw [abs_of_nonneg ha, abs_of_nonpos hb]; ring
    · rw [abs_of_nonpos ha, abs_of_nonneg hb]; ring
    · have := mul_nonneg_of_nonpos_of_nonpos ha hb; linarith
  calc
    orient (c * a) (d * b) =
        (c * |d| * (a * |b|) - d * |c| * (b * |a|)) / 2 := by
      unfold orient; rw [abs_mul, abs_mul]; ring
    _ = signedMultiplier c d * orient a b := by
      unfold signedMultiplier orient
      rw [he]
      ring

/-- On an active pair, a positive real-clock scaling exists exactly when both
Euler amplitude multipliers are positive; zeros or sign changes do not qualify. -/
theorem positive_step_scale_iff (a b c d : ℝ) (hab : a * b < 0) :
    (∃ q : ℝ, 0 < q ∧ orient (c * a) (d * b) = q * orient a b) ↔ 0 < c ∧ 0 < d := by
  have hA := (orient_ne_zero_iff a b).mpr hab
  rw [orient_scaled_opposite a b c d hab]
  constructor
  · rintro ⟨q, hq, he⟩
    have heq : signedMultiplier c d = q := mul_right_cancel₀ hA he
    apply (signed_multiplier_positive_iff c d).mp
    rwa [heq]
  · intro h
    exact ⟨signedMultiplier c d, (signed_multiplier_positive_iff c d).mpr h, rfl⟩

open TwoWaveDiscreteGapBridge in
noncomputable def stepFactor (ls lr τ : ℝ) : ℝ :=
  1 / (multiplier τ ls * multiplier τ lr)

noncomputable def stepClock (ls lr τ : ℝ) : ℝ := log (stepFactor ls lr τ) / 4

open TwoWaveDiscreteGapBridge

theorem step_factor_positive (ls lr τ : ℝ) (hs : 0 < multiplier τ ls) (hr : 0 < multiplier τ lr) :
    0 < stepFactor ls lr τ := one_div_pos.mpr (mul_pos hs hr)

theorem step_clock_factor (ls lr τ : ℝ) (hs : 0 < multiplier τ ls) (hr : 0 < multiplier τ lr) :
    exp (4 * stepClock ls lr τ) = stepFactor ls lr τ :=
  GapMirrorBridge.clock_factor _ _ (by norm_num) (step_factor_positive ls lr τ hs hr)

theorem step_factor_forward (ls lr τ : ℝ) (hp : ls + lr = 4) (hτ : 0 < τ)
    (hs : 0 < multiplier τ ls) (hr : 0 < multiplier τ lr) : 1 < stepFactor ls lr τ := by
  have hsum : multiplier τ ls + multiplier τ lr < 2 := by
    unfold multiplier
    nlinarith only [hp, hτ]
  have hprod : multiplier τ ls * multiplier τ lr < 1 := by
    nlinarith [sq_nonneg (multiplier τ ls - multiplier τ lr)]
  unfold stepFactor
  rw [lt_div_iff₀ (mul_pos hs hr)]
  simpa using hprod

theorem step_clock_forward (ls lr τ : ℝ) (hp : ls + lr = 4) (hτ : 0 < τ)
    (hs : 0 < multiplier τ ls) (hr : 0 < multiplier τ lr) : 0 < stepClock ls lr τ :=
  div_pos (log_pos (step_factor_forward ls lr τ hp hτ hs hr)) (by norm_num)

theorem iterate_clock_factor (ls lr τ : ℝ) (k : ℕ)
    (hs : 0 < multiplier τ ls) (hr : 0 < multiplier τ lr) :
    exp (4 * ((k : ℝ) * stepClock ls lr τ)) = stepFactor ls lr τ ^ k := by
  rw [show (4 : ℝ) * ((k : ℝ) * stepClock ls lr τ) = (k : ℝ) * (4 * stepClock ls lr τ) by ring,
    exp_nat_mul, step_clock_factor ls lr τ hs hr]

theorem product_power_factor (ls lr τ A : ℝ) (k : ℕ) :
    (multiplier τ ls * multiplier τ lr) ^ k * A = A / stepFactor ls lr τ ^ k := by
  simp only [stepFactor, one_div, inv_pow, div_inv_eq_mul]
  ring

section DiscreteRing

variable {n : ℕ} [NeZero n]

theorem iterate_amplitude (ls lr τ a b : ℝ) (v w : ZMod n → ℝ) (k : ℕ)
    (hv : ∀ j, heatGenerator v j = -ls * v j) (hw : ∀ j, heatGenerator w j = -lr * w j)
    (ho : dot v w = 0) (hNv : RingGapBridge.size v ≠ 0) (hNw : RingGapBridge.size w ≠ 0)
    (hs : 0 < multiplier τ ls) (hr : 0 < multiplier τ lr) :
    amplitude v w ((RingDecay.heatStep τ)^[k] (mix a b v w)) =
      (multiplier τ ls * multiplier τ lr) ^ k * orient a b := by
  rw [iterate_heat_mix ls lr τ a b v w k hv hw, amplitude_mix _ _ v w ho hNv hNw,
    orient_scale _ _ _ _ (pow_pos hs _).le (pow_pos hr _).le, ← mul_pow]

theorem iterate_readout_motion (ls lr τ a b : ℝ) (v w : ZMod n → ℝ) (k : ℕ)
    (hv : ∀ j, heatGenerator v j = -ls * v j) (hw : ∀ j, heatGenerator w j = -lr * w j)
    (ho : dot v w = 0) (hNv : RingGapBridge.size v ≠ 0) (hNw : RingGapBridge.size w ≠ 0)
    (hs : 0 < multiplier τ ls) (hr : 0 < multiplier τ lr)
    (hA0 : orient a b ≠ 0) (hA1 : orient a b ≠ 1) :
    readout v w ((RingDecay.heatStep τ)^[k] (mix a b v w)) =
      GapMirrorCalculus.bump 4 (readout v w (mix a b v w)) ((k : ℝ) * stepClock ls lr τ) := by
  rw [readout_mix a b v w ho hNv hNw, readout,
    iterate_amplitude ls lr τ a b v w k hv hw ho hNv hNw hs hr,
    product_power_factor ls lr τ (orient a b) k,
    height_dilation 4 _ _ (by norm_num) hA1 (pow_ne_zero _ (step_factor_positive ls lr τ hs hr).ne'),
    ← iterate_clock_factor ls lr τ k hs hr]
  exact GapMirrorBridge.real_step_at_time _ _ _ ((height_nonzero_iff 4 _ (by norm_num) hA1).mpr hA0)

/-- Heat and flip need not commute as patterns. This readout makes their values agree. -/
theorem iterate_flip_readout (ls lr τ a b : ℝ) (v w : ZMod n → ℝ) (k : ℕ)
    (hv : ∀ j, heatGenerator v j = -ls * v j) (hw : ∀ j, heatGenerator w j = -lr * w j)
    (hf : RingGapBridge.flip v = w) (ho : dot v w = 0)
    (hNv : RingGapBridge.size v ≠ 0) (hNw : RingGapBridge.size w ≠ 0)
    (hs : 0 < multiplier τ ls) (hr : 0 < multiplier τ lr) :
    readout v w ((RingDecay.heatStep τ)^[k] (RingGapBridge.flip (mix a b v w))) =
      readout v w (RingGapBridge.flip ((RingDecay.heatStep τ)^[k] (mix a b v w))) := by
  rw [flip_mix a b v w hf]
  unfold readout
  rw [amplitude_flip v w _ hf, iterate_amplitude ls lr τ b a v w k hv hw ho hNv hNw hs hr,
    iterate_amplitude ls lr τ a b v w k hv hw ho hNv hNw hs hr, orient_swap]
  congr 1
  ring

theorem discrete_mirror_before (ls lr τ a b : ℝ) (v w : ZMod n → ℝ) (k : ℕ)
    (hv : ∀ j, heatGenerator v j = -ls * v j) (hw : ∀ j, heatGenerator w j = -lr * w j)
    (hf : RingGapBridge.flip v = w) (ho : dot v w = 0)
    (hNv : RingGapBridge.size v ≠ 0) (hNw : RingGapBridge.size w ≠ 0)
    (hs : 0 < multiplier τ ls) (hr : 0 < multiplier τ lr)
    (hbefore : stepFactor ls lr τ ^ k < orient a b) :
    4 < readout v w ((RingDecay.heatStep τ)^[k] (mix a b v w)) ∧
    readout v w (RingGapBridge.flip ((RingDecay.heatStep τ)^[k] (mix a b v w))) =
      GapMirrorCalculus.mirror 4 (readout v w ((RingDecay.heatStep τ)^[k] (mix a b v w))) := by
  have hpos := pow_pos (step_factor_positive ls lr τ hs hr) k
  have hcur : 1 < amplitude v w ((RingDecay.heatStep τ)^[k] (mix a b v w)) := by
    rw [iterate_amplitude ls lr τ a b v w k hv hw ho hNv hNw hs hr,
      product_power_factor ls lr τ (orient a b) k]
    exact (lt_div_iff₀ hpos).mpr (by simpa using hbefore)
  exact ⟨height_above_gap 4 _ (by norm_num) hcur,
    readout_flip v w _ hf (by linarith) (by linarith)⟩

end DiscreteRing

theorem height_positive_iff (g A : ℝ) (hg : 0 < g) :
    0 < height g A ↔ A < 0 ∨ 1 < A := by
  unfold height
  rw [div_pos_iff]
  constructor
  · intro h
    rcases h with ⟨hnum, hden⟩ | ⟨hnum, hden⟩
    · exact Or.inr (by linarith)
    · exact Or.inl (by nlinarith only [hnum, hg])
  · intro h
    rcases h with h | h
    · exact Or.inr ⟨mul_neg_of_pos_of_neg hg h, by linarith⟩
    · exact Or.inl ⟨mul_pos hg (by linarith), by linarith⟩

/-- Both readouts are strictly positive exactly when `|A| > 1`. -/
theorem positive_pair_iff (g A : ℝ) (hg : 0 < g) :
    (0 < height g A ∧ 0 < height g (-A)) ↔ 1 < |A| := by
  rw [height_positive_iff g A hg, height_positive_iff g (-A) hg]
  rcases le_total 0 A with ha | ha
  · rw [abs_of_nonneg ha]
    constructor
    · rintro ⟨h | h, _⟩ <;> linarith
    · intro h
      exact ⟨Or.inr h, Or.inl (by linarith)⟩
  · rw [abs_of_nonpos ha]
    constructor
    · rintro ⟨_, h | h⟩ <;> linarith
    · intro h
      exact ⟨Or.inl (by linarith), Or.inr h⟩

/-- A concrete orthogonal pair exchanged by the actual four-dot flip. -/
theorem flat_rough_flip : RingGapBridge.flip flat4 = rough4 := by
  funext j
  fin_cases j
  · change (1 : ℝ) * 1 = 1; norm_num
  · change ((-1 : ℝ) ^ 1) * 1 = -1; norm_num
  · change ((-1 : ℝ) ^ 2) * 1 = 1; norm_num
  · change ((-1 : ℝ) ^ 3) * 1 = -1; norm_num

/-- Both modes are present. The opposite modal signs produce an upper/mirror pair. -/
theorem concrete_readouts :
    orient 2 (-1) = 2 ∧
    readout flat4 rough4 (mix 2 (-1) flat4 rough4) = 8 ∧
    readout flat4 rough4 (RingGapBridge.flip (mix 2 (-1) flat4 rough4)) = 8 / 3 := by
  have hv : RingGapBridge.size flat4 ≠ 0 := by rw [four_mode_data.2.1]; norm_num
  have hw : RingGapBridge.size rough4 ≠ 0 := by rw [four_mode_data.2.2]; norm_num
  rw [flip_mix 2 (-1) flat4 rough4 flat_rough_flip,
    readout_mix 2 (-1) flat4 rough4 four_mode_data.1 hv hw,
    readout_mix (-1) 2 flat4 rough4 four_mode_data.1 hv hw]
  norm_num [orient, height]

/-- A nonvacuous pair of actual heat solutions with both correspondences checked. -/
theorem concrete_both (t : ℝ) (ht0 : 0 ≤ t) (ht : t < log 2 / 4) :
    readout flat4 rough4 (ringFlow 0 4 2 (-1) flat4 rough4 t) = GapMirrorCalculus.bump 4 8 t ∧
    readout flat4 rough4 (RingGapBridge.flip (ringFlow 0 4 2 (-1) flat4 rough4 t)) =
      GapMirrorCalculus.bump 4 (8 / 3) t ∧
    readout flat4 rough4 (RingGapBridge.flip (ringFlow 0 4 2 (-1) flat4 rough4 t)) =
      GapMirrorCalculus.mirror 4 (readout flat4 rough4 (ringFlow 0 4 2 (-1) flat4 rough4 t)) := by
  have hv : RingGapBridge.size flat4 ≠ 0 := by rw [four_mode_data.2.1]; norm_num
  have h := paired_motion_and_flip (n := 4) (by decide) 0 4 2 (-1) t flat4 rough4
    flat4_eigen rough4_eigen flat_rough_flip four_mode_data.1 hv
    (by norm_num [orient]) ht0 (by simpa [poleTime, orient] using ht)
  obtain ⟨_, hm, hf, hfm, he, _, _, _⟩ := h
  rw [concrete_readouts.2.1] at hm
  rw [concrete_readouts.2.2, he] at hfm
  exact ⟨hm, hfm, hf⟩

/-- A finite discrete step before the pole; the earlier cost/size map has a different factor. -/
theorem concrete_step :
    stepFactor 0 4 (1 / 16) = 4 / 3 ∧
    stepClock 0 4 (1 / 16) = log (4 / 3) / 4 ∧
    readout flat4 rough4 (RingDecay.heatStep (1 / 16) (mix 2 (-1) flat4 rough4)) = 12 ∧
    readout flat4 rough4 (RingGapBridge.flip
      (RingDecay.heatStep (1 / 16) (mix 2 (-1) flat4 rough4))) = 12 / 5 := by
  have hv : RingGapBridge.size flat4 ≠ 0 := by rw [four_mode_data.2.1]; norm_num
  have hw : RingGapBridge.size rough4 ≠ 0 := by rw [four_mode_data.2.2]; norm_num
  rw [heat_step_mix 0 4 (1 / 16) 2 (-1) flat4 rough4 flat4_eigen rough4_eigen,
    flip_mix _ _ flat4 rough4 flat_rough_flip,
    readout_mix _ _ flat4 rough4 four_mode_data.1 hv hw,
    readout_mix _ _ flat4 rough4 four_mode_data.1 hv hw]
  norm_num [stepFactor, stepClock, multiplier, orient, height]

end TwoWaveFlipBridge

#print axioms TwoWaveFlipBridge.orient_swap
#print axioms TwoWaveFlipBridge.orient_pos_neg
#print axioms TwoWaveFlipBridge.orient_neg_pos
#print axioms TwoWaveFlipBridge.orient_zero_iff
#print axioms TwoWaveFlipBridge.orient_ne_zero_iff
#print axioms TwoWaveFlipBridge.orient_positive_iff
#print axioms TwoWaveFlipBridge.orient_scale
#print axioms TwoWaveFlipBridge.orient_heat
#print axioms TwoWaveFlipBridge.height_zero
#print axioms TwoWaveFlipBridge.height_nonzero_iff
#print axioms TwoWaveFlipBridge.height_reflection
#print axioms TwoWaveFlipBridge.height_above_gap
#print axioms TwoWaveFlipBridge.height_dilation
#print axioms TwoWaveFlipBridge.height_motion
#print axioms TwoWaveFlipBridge.decay_before_pole
#print axioms TwoWaveFlipBridge.pole_eq_blowTime
#print axioms TwoWaveFlipBridge.finite_pair_iff
#print axioms TwoWaveFlipBridge.matching_rate_iff
#print axioms TwoWaveFlipBridge.linear_readout_iff
#print axioms TwoWaveFlipBridge.decay_deriv
#print axioms TwoWaveFlipBridge.height_deriv
#print axioms TwoWaveFlipBridge.solves_iff
#print axioms TwoWaveFlipBridge.linear_paired_iff
#print axioms TwoWaveFlipBridge.sign_prev
#print axioms TwoWaveFlipBridge.heat_flip
#print axioms TwoWaveFlipBridge.flipped_eigen
#print axioms TwoWaveFlipBridge.flip_reverse
#print axioms TwoWaveFlipBridge.paired_eigenvalues
#print axioms TwoWaveFlipBridge.dot_flip
#print axioms TwoWaveFlipBridge.modal_flip
#print axioms TwoWaveFlipBridge.amplitude_flip
#print axioms TwoWaveFlipBridge.readout_flip
#print axioms TwoWaveFlipBridge.modal_mix_left
#print axioms TwoWaveFlipBridge.modal_mix_right
#print axioms TwoWaveFlipBridge.amplitude_mix
#print axioms TwoWaveFlipBridge.readout_mix
#print axioms TwoWaveFlipBridge.active_iff
#print axioms TwoWaveFlipBridge.flip_mix
#print axioms TwoWaveFlipBridge.amplitude_flow
#print axioms TwoWaveFlipBridge.flow_readout
#print axioms TwoWaveFlipBridge.paired_motion_and_flip
#print axioms TwoWaveFlipBridge.signed_multiplier_positive_iff
#print axioms TwoWaveFlipBridge.orient_scaled_opposite
#print axioms TwoWaveFlipBridge.positive_step_scale_iff
#print axioms TwoWaveFlipBridge.step_factor_positive
#print axioms TwoWaveFlipBridge.step_clock_factor
#print axioms TwoWaveFlipBridge.step_factor_forward
#print axioms TwoWaveFlipBridge.step_clock_forward
#print axioms TwoWaveFlipBridge.iterate_clock_factor
#print axioms TwoWaveFlipBridge.product_power_factor
#print axioms TwoWaveFlipBridge.iterate_amplitude
#print axioms TwoWaveFlipBridge.iterate_readout_motion
#print axioms TwoWaveFlipBridge.iterate_flip_readout
#print axioms TwoWaveFlipBridge.discrete_mirror_before
#print axioms TwoWaveFlipBridge.height_positive_iff
#print axioms TwoWaveFlipBridge.positive_pair_iff
#print axioms TwoWaveFlipBridge.flat_rough_flip
#print axioms TwoWaveFlipBridge.concrete_readouts
#print axioms TwoWaveFlipBridge.concrete_both
#print axioms TwoWaveFlipBridge.concrete_step
