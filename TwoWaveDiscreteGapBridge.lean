import TwoWaveGapBridge
import RingDecay

/-!
# The two-wave map for the actual discrete heat step

For two orthogonal eigenmodes with eigenvalues `ls < lr`, `RingDecay.heatStep τ`
multiplies their amplitudes by `cs = 1 - τ*ls` and `cr = 1 - τ*lr`.
Their squared sizes therefore acquire the factors `cs²` and `cr²`.
The exact gap-step factor is `r = cs²/cr²`, with gap `g = 2*(lr-ls)` and
toy-clock increment `log r/g`. After `k` actual heat steps the toy clock is
`k*log r/g`; it need not equal the heat clock `k*τ`.

Both the ordinary cost/size readout and its signed mirror are covered.
The signed denominator vanishes exactly when `P*r^k = Q`. The interpolating
toy flow can have a pole between two integer samples. Statements about regular
motion use the strict pre-pole inequality; algebraic identities at zero
denominators use Lean's totalized division and do not assert a finite pole value.
If `cr = 0`, one step removes the rough mode; the finite clock theorem excludes
that endpoint and a separate theorem describes the actual heat step there.
-/

open Real Filter Topology
open TwoWaveGapBridge

namespace TwoWaveDiscreteGapBridge

noncomputable def multiplier (τ l : ℝ) : ℝ := 1 - τ * l

noncomputable def factor (ls lr τ : ℝ) : ℝ :=
  multiplier τ ls ^ 2 / multiplier τ lr ^ 2

noncomputable def clock (ls lr τ : ℝ) : ℝ := log (factor ls lr τ) / gap ls lr

noncomputable def sampleClock (ls lr τ : ℝ) (k : ℕ) : ℝ := k * clock ls lr τ

noncomputable def sampleEnergy (τ l E : ℝ) (k : ℕ) : ℝ :=
  (multiplier τ l ^ 2) ^ k * E

noncomputable def ordinaryAt (ls lr τ P Q : ℝ) (k : ℕ) : ℝ :=
  ordinary (gap ls lr) (sampleEnergy τ ls P k) (sampleEnergy τ lr Q k)

noncomputable def signedAt (ls lr τ P Q : ℝ) (k : ℕ) : ℝ :=
  signed (gap ls lr) (sampleEnergy τ ls P k) (sampleEnergy τ lr Q k)

/-- This is the square of the amplitude ratio, not the unsquared ratio. -/
theorem factor_square (ls lr τ : ℝ) :
    factor ls lr τ = (multiplier τ ls / multiplier τ lr) ^ 2 := by
  simp only [factor, div_pow]

theorem factor_pos (ls lr τ : ℝ)
    (hs : multiplier τ ls ≠ 0) (hr : multiplier τ lr ≠ 0) :
    0 < factor ls lr τ := div_pos (sq_pos_of_ne_zero hs) (sq_pos_of_ne_zero hr)

theorem forward_multipliers (ls lr τ : ℝ) (hl : ls < lr) (hτ : 0 < τ)
    (hr : 0 < multiplier τ lr) :
    0 < multiplier τ ls ∧ multiplier τ lr < multiplier τ ls := by
  have h := mul_lt_mul_of_pos_left hl hτ
  dsimp [multiplier] at *
  constructor <;> linarith

/-- The strict usual stable heat range ensures the rough multiplier is positive. -/
theorem stable_multiplier (lr τ : ℝ) (hl : lr ≤ 4) (hτ : 0 ≤ τ) (hτ4 : τ < 1 / 4) :
    0 < multiplier τ lr := by
  have h := mul_le_mul_of_nonneg_left hl hτ
  dsimp [multiplier]
  linarith

theorem factor_gt_one (ls lr τ : ℝ) (hl : ls < lr) (hτ : 0 < τ)
    (hr : 0 < multiplier τ lr) : 1 < factor ls lr τ := by
  obtain ⟨hs, hlt⟩ := forward_multipliers ls lr τ hl hτ hr
  unfold factor
  rw [lt_div_iff₀ (sq_pos_of_pos hr)]
  nlinarith

theorem clock_pos (ls lr τ : ℝ) (hl : ls < lr) (hτ : 0 < τ)
    (hr : 0 < multiplier τ lr) : 0 < clock ls lr τ := by
  exact div_pos (Real.log_pos (factor_gt_one ls lr τ hl hτ hr)) (gap_pos ls lr hl)

theorem zero_step (ls lr : ℝ) : factor ls lr 0 = 1 ∧ clock ls lr 0 = 0 := by
  simp [factor, multiplier, clock]

theorem clock_factor (ls lr τ : ℝ) (hl : ls < lr)
    (hs : multiplier τ ls ≠ 0) (hr : multiplier τ lr ≠ 0) :
    exp (gap ls lr * clock ls lr τ) = factor ls lr τ :=
  GapMirrorBridge.clock_factor _ _ (gap_pos ls lr hl).ne' (factor_pos ls lr τ hs hr)

theorem sample_clock_factor (ls lr τ : ℝ) (k : ℕ) (hl : ls < lr)
    (hs : multiplier τ ls ≠ 0) (hr : multiplier τ lr ≠ 0) :
    exp (gap ls lr * sampleClock ls lr τ k) = factor ls lr τ ^ k := by
  rw [sampleClock, show gap ls lr * ((k : ℝ) * clock ls lr τ) =
    (k : ℝ) * (gap ls lr * clock ls lr τ) by ring, Real.exp_nat_mul,
    clock_factor ls lr τ hl hs hr]

theorem sample_energy_zero (τ l E : ℝ) : sampleEnergy τ l E 0 = E := by
  simp [sampleEnergy]

theorem sample_energy_pos (τ l E : ℝ) (k : ℕ)
    (hm : multiplier τ l ≠ 0) (hE : 0 < E) : 0 < sampleEnergy τ l E k := by
  exact mul_pos (pow_pos (sq_pos_of_ne_zero hm) _) hE

theorem sample_energy_factor (ls lr τ P : ℝ) (k : ℕ) (hr : multiplier τ lr ≠ 0) :
    sampleEnergy τ ls P k =
      (P * factor ls lr τ ^ k) * (multiplier τ lr ^ 2) ^ k := by
  have h : factor ls lr τ * multiplier τ lr ^ 2 = multiplier τ ls ^ 2 := by
    unfold factor
    exact div_mul_cancel₀ _ (pow_ne_zero _ hr)
  unfold sampleEnergy
  rw [mul_assoc, ← mul_pow, h]
  ring

theorem ordinary_reduced (ls lr τ P Q : ℝ) (k : ℕ) (hr : multiplier τ lr ≠ 0) :
    ordinaryAt ls lr τ P Q k = gap ls lr * Q / (P * factor ls lr τ ^ k + Q) := by
  unfold ordinaryAt ordinary
  rw [sample_energy_factor ls lr τ P k hr]
  unfold sampleEnergy
  rw [mul_comm ((multiplier τ lr ^ 2) ^ k) Q, ← add_mul, ← mul_assoc]
  exact mul_div_mul_right _ _ (pow_ne_zero _ (pow_ne_zero _ hr))

theorem signed_reduced (ls lr τ P Q : ℝ) (k : ℕ) (hr : multiplier τ lr ≠ 0) :
    signedAt ls lr τ P Q k = gap ls lr * Q / (Q - P * factor ls lr τ ^ k) := by
  unfold signedAt signed
  rw [sample_energy_factor ls lr τ P k hr]
  unfold sampleEnergy
  rw [mul_comm ((multiplier τ lr ^ 2) ^ k) Q, ← sub_mul, ← mul_assoc]
  exact mul_div_mul_right _ _ (pow_ne_zero _ (pow_ne_zero _ hr))

theorem ordinary_sample (ls lr τ P Q : ℝ) (k : ℕ) (hl : ls < lr)
    (hs : multiplier τ ls ≠ 0) (hr : multiplier τ lr ≠ 0) :
    ordinaryAt ls lr τ P Q k = ordinaryFlow ls lr P Q (sampleClock ls lr τ k) := by
  rw [ordinary_reduced ls lr τ P Q k hr, TwoWaveGapBridge.ordinary_reduced,
    sample_clock_factor ls lr τ k hl hs hr]

theorem signed_sample (ls lr τ P Q : ℝ) (k : ℕ) (hl : ls < lr)
    (hs : multiplier τ ls ≠ 0) (hr : multiplier τ lr ≠ 0) :
    signedAt ls lr τ P Q k = signedFlow ls lr P Q (sampleClock ls lr τ k) := by
  rw [signed_reduced ls lr τ P Q k hr, TwoWaveGapBridge.signed_reduced,
    sample_clock_factor ls lr τ k hl hs hr]

theorem ordinary_motion (ls lr τ P Q : ℝ) (k : ℕ) (hl : ls < lr)
    (hs : multiplier τ ls ≠ 0) (hr : multiplier τ lr ≠ 0) (hP : 0 < P) (hQ : 0 < Q) :
    ordinaryAt ls lr τ P Q k =
      GapMirrorCalculus.bump (gap ls lr) (ordinary (gap ls lr) P Q) (sampleClock ls lr τ k) := by
  rw [ordinary_sample ls lr τ P Q k hl hs hr]
  exact TwoWaveGapBridge.ordinary_motion _ _ _ _ _ hl hP hQ

/-- At a pole this is only an algebraic identity; see `before_pole_iff` below. -/
theorem signed_motion (ls lr τ P Q : ℝ) (k : ℕ) (hl : ls < lr)
    (hs : multiplier τ ls ≠ 0) (hr : multiplier τ lr ≠ 0) (hQ : 0 < Q) :
    signedAt ls lr τ P Q k =
      GapMirrorCalculus.bump (gap ls lr) (signed (gap ls lr) P Q) (sampleClock ls lr τ k) := by
  rw [signed_sample ls lr τ P Q k hl hs hr]
  exact TwoWaveGapBridge.signed_motion _ _ _ _ _ hl hQ

theorem ordinary_one_step (ls lr τ P Q : ℝ) (hl : ls < lr)
    (hs : multiplier τ ls ≠ 0) (hr : multiplier τ lr ≠ 0) (hP : 0 < P) (hQ : 0 < Q) :
    ordinaryAt ls lr τ P Q 1 =
      GapMirrorBridge.realStep (gap ls lr) (factor ls lr τ) (ordinary (gap ls lr) P Q) := by
  rw [ordinary_motion ls lr τ P Q 1 hl hs hr hP hQ]
  simp only [sampleClock, Nat.cast_one, one_mul]
  rw [← clock_factor ls lr τ hl hs hr]
  exact (GapMirrorBridge.real_step_at_time _ _ _
    (ordinary_between _ _ _ (gap_pos ls lr hl) hP hQ).1.ne').symm

theorem signed_one_step (ls lr τ P Q : ℝ) (hl : ls < lr)
    (hs : multiplier τ ls ≠ 0) (hr : multiplier τ lr ≠ 0) (hP : 0 < P) (hPQ : P < Q) :
    signedAt ls lr τ P Q 1 =
      GapMirrorBridge.realStep (gap ls lr) (factor ls lr τ) (signed (gap ls lr) P Q) := by
  rw [signed_motion ls lr τ P Q 1 hl hs hr (lt_trans hP hPQ)]
  simp only [sampleClock, Nat.cast_one, one_mul]
  rw [← clock_factor ls lr τ hl hs hr]
  exact (GapMirrorBridge.real_step_at_time _ _ _
    (lt_trans (gap_pos ls lr hl) (signed_above_gap _ _ _ (gap_pos ls lr hl) hP hPQ)).ne').symm

theorem sample_mirror (ls lr τ P Q : ℝ) (k : ℕ) (hl : ls < lr)
    (hs : multiplier τ ls ≠ 0) (hr : multiplier τ lr ≠ 0) (hP : 0 < P) (hQ : 0 < Q) :
    signedAt ls lr τ P Q k = GapMirrorCalculus.mirror (gap ls lr) (ordinaryAt ls lr τ P Q k) :=
  signed_is_mirror _ _ _ (gap_pos ls lr hl)
    (sample_energy_pos _ _ _ _ hs hP) (sample_energy_pos _ _ _ _ hr hQ)

theorem signed_denominator (ls lr τ P Q : ℝ) (k : ℕ) (hr : multiplier τ lr ≠ 0) :
    sampleEnergy τ lr Q k - sampleEnergy τ ls P k =
      (Q - P * factor ls lr τ ^ k) * (multiplier τ lr ^ 2) ^ k := by
  rw [sample_energy_factor ls lr τ P k hr]
  unfold sampleEnergy
  ring

/-- A discrete sample hits the pole exactly when the two squared sizes coincide. -/
theorem pole_at_sample_iff (ls lr τ P Q : ℝ) (k : ℕ) (hr : multiplier τ lr ≠ 0) :
    sampleEnergy τ lr Q k - sampleEnergy τ ls P k = 0 ↔ P * factor ls lr τ ^ k = Q := by
  rw [signed_denominator ls lr τ P Q k hr,
    mul_eq_zero_iff_right (pow_ne_zero _ (pow_ne_zero _ hr)), sub_eq_zero, eq_comm]

theorem before_pole_iff (ls lr τ P Q : ℝ) (k : ℕ) (hl : ls < lr)
    (hs : multiplier τ ls ≠ 0) (hr : multiplier τ lr ≠ 0) (hP : 0 < P) (hQ : 0 < Q) :
    P * factor ls lr τ ^ k < Q ↔ sampleClock ls lr τ k < poleTime ls lr P Q := by
  have hg := gap_pos ls lr hl
  calc
    P * factor ls lr τ ^ k < Q ↔ factor ls lr τ ^ k < Q / P := by
      rw [lt_div_iff₀ hP, mul_comm (factor ls lr τ ^ k) P]
    _ ↔ exp (gap ls lr * sampleClock ls lr τ k) < exp (gap ls lr * poleTime ls lr P Q) := by
      rw [sample_clock_factor ls lr τ k hl hs hr, crossing_factor ls lr P Q hl hP hQ]
    _ ↔ sampleClock ls lr τ k < poleTime ls lr P Q := by
      rw [exp_lt_exp]
      exact mul_lt_mul_iff_right₀ hg

theorem pole_clock_iff (ls lr τ P Q : ℝ) (k : ℕ) (hl : ls < lr)
    (hs : multiplier τ ls ≠ 0) (hr : multiplier τ lr ≠ 0) (hP : 0 < P) (hQ : 0 < Q) :
    sampleEnergy τ lr Q k - sampleEnergy τ ls P k = 0 ↔
      sampleClock ls lr τ k = poleTime ls lr P Q := by
  rw [pole_at_sample_iff ls lr τ P Q k hr]
  calc
    P * factor ls lr τ ^ k = Q ↔ factor ls lr τ ^ k = Q / P := by
      rw [eq_div_iff hP.ne', mul_comm (factor ls lr τ ^ k) P]
    _ ↔ exp (gap ls lr * sampleClock ls lr τ k) = exp (gap ls lr * poleTime ls lr P Q) := by
      rw [sample_clock_factor ls lr τ k hl hs hr, crossing_factor ls lr P Q hl hP hQ]
    _ ↔ sampleClock ls lr τ k = poleTime ls lr P Q := by
      rw [exp_injective.eq_iff]
      exact mul_right_inj' (gap_pos ls lr hl).ne'

/-- The pole's real-valued step index; it need not be an integer. -/
noncomputable def poleIndex (ls lr τ P Q : ℝ) : ℝ := log (Q / P) / log (factor ls lr τ)

theorem before_index_iff (ls lr τ P Q : ℝ) (k : ℕ) (hl : ls < lr)
    (hτ : 0 < τ) (hr : 0 < multiplier τ lr) :
    sampleClock ls lr τ k < poleTime ls lr P Q ↔ (k : ℝ) < poleIndex ls lr τ P Q := by
  have hg := gap_pos ls lr hl
  have hlog := Real.log_pos (factor_gt_one ls lr τ hl hτ hr)
  unfold sampleClock clock poleTime poleIndex
  rw [← mul_div_assoc, div_lt_div_iff_of_pos_right hg, lt_div_iff₀ hlog]

theorem signed_regular_before (ls lr τ P Q : ℝ) (k : ℕ) (hl : ls < lr)
    (hs : multiplier τ ls ≠ 0) (hr : multiplier τ lr ≠ 0) (hP : 0 < P)
    (hPQ : P < Q) (hbefore : P * factor ls lr τ ^ k < Q) :
    0 < sampleEnergy τ lr Q k - sampleEnergy τ ls P k ∧
    gap ls lr < signedAt ls lr τ P Q k ∧
    sampleClock ls lr τ k < GapMirrorCalculus.blowTime (gap ls lr) (signed (gap ls lr) P Q) := by
  have hd : 0 < sampleEnergy τ lr Q k - sampleEnergy τ ls P k := by
    rw [signed_denominator ls lr τ P Q k hr]
    exact mul_pos (sub_pos.mpr hbefore) (pow_pos (sq_pos_of_ne_zero hr) _)
  refine ⟨hd, signed_above_gap _ _ _ (gap_pos ls lr hl)
    (sample_energy_pos _ _ _ _ hs hP) (sub_pos.mp hd), ?_⟩
  rw [← pole_eq_blowTime ls lr P Q hl hP hPQ]
  exact (before_pole_iff ls lr τ P Q k hl hs hr hP (lt_trans hP hPQ)).mp hbefore

section Ring

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- The actual repository heat step, applied to the two-mode pattern. -/
theorem heat_step_mix (ls lr τ a b : ℝ) (v w : ZMod n → ℝ)
    (hv : ∀ j, heatGenerator v j = -ls * v j) (hw : ∀ j, heatGenerator w j = -lr * w j) :
    RingDecay.heatStep τ (mix a b v w) =
      mix (multiplier τ ls * a) (multiplier τ lr * b) v w := by
  funext j
  change mix a b v w j + τ * heatGenerator (mix a b v w) j = _
  rw [heat_mix, hv, hw]
  unfold mix multiplier
  ring

omit [NeZero n] in
/-- Iterates here are iterates of `RingDecay.heatStep`, not an assumed mode evolution. -/
theorem iterate_heat_mix (ls lr τ a b : ℝ) (v w : ZMod n → ℝ) (k : ℕ)
    (hv : ∀ j, heatGenerator v j = -ls * v j) (hw : ∀ j, heatGenerator w j = -lr * w j) :
    (RingDecay.heatStep τ)^[k] (mix a b v w) =
      mix (multiplier τ ls ^ k * a) (multiplier τ lr ^ k * b) v w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, heat_step_mix ls lr τ _ _ v w hv hw]
    funext j
    simp only [mix, pow_succ]
    ring

theorem sample_coefficient_energy (τ l a : ℝ) (v : ZMod n → ℝ) (k : ℕ) :
    initialEnergy (multiplier τ l ^ k * a) v = sampleEnergy τ l (initialEnergy a v) k := by
  unfold initialEnergy sampleEnergy
  rw [mul_pow, ← pow_mul, Nat.mul_comm k 2, pow_mul]
  ring

theorem iterate_size (ls lr τ a b : ℝ) (v w : ZMod n → ℝ) (k : ℕ)
    (ho : dot v w = 0) (hv : ∀ j, heatGenerator v j = -ls * v j)
    (hw : ∀ j, heatGenerator w j = -lr * w j) :
    RingGapBridge.size ((RingDecay.heatStep τ)^[k] (mix a b v w)) =
      sampleEnergy τ ls (initialEnergy a v) k + sampleEnergy τ lr (initialEnergy b w) k := by
  rw [iterate_heat_mix ls lr τ a b v w k hv hw, size_mix _ _ v w ho]
  change initialEnergy _ v + initialEnergy _ w = _
  rw [sample_coefficient_energy, sample_coefficient_energy]

theorem iterate_cost (ls lr τ a b : ℝ) (v w : ZMod n → ℝ) (k : ℕ)
    (ho : dot v w = 0) (hv : ∀ j, heatGenerator v j = -ls * v j)
    (hw : ∀ j, heatGenerator w j = -lr * w j) :
    RingGapBridge.cost ((RingDecay.heatStep τ)^[k] (mix a b v w)) =
      ls * sampleEnergy τ ls (initialEnergy a v) k + lr * sampleEnergy τ lr (initialEnergy b w) k := by
  rw [iterate_heat_mix ls lr τ a b v w k hv hw, cost_mix ls lr _ _ v w ho hv hw]
  change ls * initialEnergy _ v + lr * initialEnergy _ w = _
  rw [sample_coefficient_energy, sample_coefficient_energy]

theorem iterate_readout (ls lr τ a b : ℝ) (v w : ZMod n → ℝ) (k : ℕ)
    (ho : dot v w = 0) (hv : ∀ j, heatGenerator v j = -ls * v j)
    (hw : ∀ j, heatGenerator w j = -lr * w j)
    (hs : multiplier τ ls ≠ 0) (hr : multiplier τ lr ≠ 0)
    (hP : 0 < initialEnergy a v) (hQ : 0 < initialEnergy b w) :
    readout ls ((RingDecay.heatStep τ)^[k] (mix a b v w)) =
      ordinaryAt ls lr τ (initialEnergy a v) (initialEnergy b w) k := by
  unfold readout ordinaryAt
  rw [iterate_cost ls lr τ a b v w k ho hv hw, iterate_size ls lr τ a b v w k ho hv hw]
  exact cost_ratio_map _ _ _ _ (add_pos
    (sample_energy_pos _ _ _ _ hs hP) (sample_energy_pos _ _ _ _ hr hQ)).ne'

theorem iterate_motion (ls lr τ a b : ℝ) (v w : ZMod n → ℝ) (k : ℕ)
    (hl : ls < lr) (ho : dot v w = 0) (hv : ∀ j, heatGenerator v j = -ls * v j)
    (hw : ∀ j, heatGenerator w j = -lr * w j)
    (hs : multiplier τ ls ≠ 0) (hr : multiplier τ lr ≠ 0)
    (hP : 0 < initialEnergy a v) (hQ : 0 < initialEnergy b w) :
    readout ls ((RingDecay.heatStep τ)^[k] (mix a b v w)) =
      GapMirrorCalculus.bump (gap ls lr)
        (ordinary (gap ls lr) (initialEnergy a v) (initialEnergy b w)) (sampleClock ls lr τ k) := by
  rw [iterate_readout ls lr τ a b v w k ho hv hw hs hr hP hQ]
  exact ordinary_motion _ _ _ _ _ _ hl hs hr hP hQ

/-- The actual one-step readout obeys the gap step with its exact factor. -/
theorem heat_step_readout (ls lr τ a b : ℝ) (v w : ZMod n → ℝ)
    (hl : ls < lr) (ho : dot v w = 0) (hv : ∀ j, heatGenerator v j = -ls * v j)
    (hw : ∀ j, heatGenerator w j = -lr * w j)
    (hs : multiplier τ ls ≠ 0) (hr : multiplier τ lr ≠ 0)
    (hP : 0 < initialEnergy a v) (hQ : 0 < initialEnergy b w) :
    readout ls (RingDecay.heatStep τ (mix a b v w)) =
      GapMirrorBridge.realStep (gap ls lr) (factor ls lr τ) (readout ls (mix a b v w)) := by
  have hz := iterate_readout ls lr τ a b v w 0 ho hv hw hs hr hP hQ
  simp only [Function.iterate_zero_apply, ordinaryAt, sample_energy_zero] at hz
  have h1 := iterate_readout ls lr τ a b v w 1 ho hv hw hs hr hP hQ
  simp only [Function.iterate_one] at h1
  rw [h1, hz]
  exact ordinary_one_step _ _ _ _ _ hl hs hr hP hQ

theorem iterate_signed_mirror (ls lr τ a b : ℝ) (v w : ZMod n → ℝ) (k : ℕ)
    (hl : ls < lr) (ho : dot v w = 0) (hv : ∀ j, heatGenerator v j = -ls * v j)
    (hw : ∀ j, heatGenerator w j = -lr * w j)
    (hs : multiplier τ ls ≠ 0) (hr : multiplier τ lr ≠ 0)
    (hP : 0 < initialEnergy a v) (hQ : 0 < initialEnergy b w) :
    signedAt ls lr τ (initialEnergy a v) (initialEnergy b w) k =
      GapMirrorCalculus.mirror (gap ls lr)
        (readout ls ((RingDecay.heatStep τ)^[k] (mix a b v w))) := by
  rw [iterate_readout ls lr τ a b v w k ho hv hw hs hr hP hQ]
  exact sample_mirror _ _ _ _ _ _ hl hs hr hP hQ

omit [NeZero n] in
/-- When the rough multiplier is zero, the actual step simply removes that mode. -/
theorem killed_rough_mode (ls lr τ a b : ℝ) (v w : ZMod n → ℝ)
    (hv : ∀ j, heatGenerator v j = -ls * v j) (hw : ∀ j, heatGenerator w j = -lr * w j)
    (hr : multiplier τ lr = 0) :
    RingDecay.heatStep τ (mix a b v w) = fun j => (multiplier τ ls * a) * v j := by
  rw [heat_step_mix ls lr τ a b v w hv hw, hr]
  funext j
  simp [mix]

end Ring

/-- A step of 1/8 for the flat and alternating four-dot modes has factor 4. -/
theorem concrete_clock :
    factor 0 4 (1 / 8) = 4 ∧ clock 0 4 (1 / 8) = log 4 / 8 := by
  norm_num [factor, multiplier, clock, gap]

/-- The actual four-dot heat step can land exactly on the signed pole.
The ordinary readout remains finite and equals half the gap. -/
theorem concrete_hits_pole :
    readout 0 (RingDecay.heatStep (1 / 8) (mix 1 2 flat4 rough4)) = 4 ∧
    sampleEnergy (1 / 8) 4 16 1 - sampleEnergy (1 / 8) 0 4 1 = 0 := by
  have hP : 0 < initialEnergy 1 flat4 := by
    norm_num [initialEnergy, four_mode_data.2.1]
  have hQ : 0 < initialEnergy 2 rough4 := by
    norm_num [initialEnergy, four_mode_data.2.2]
  have h := iterate_readout 0 4 (1 / 8) 1 2 flat4 rough4 1 four_mode_data.1
    flat4_eigen rough4_eigen (by norm_num [multiplier]) (by norm_num [multiplier]) hP hQ
  simp only [Function.iterate_one] at h
  constructor
  · rw [h]
    norm_num [ordinaryAt, ordinary, sampleEnergy, multiplier, gap, initialEnergy,
      four_mode_data.2.1, four_mode_data.2.2]
  · norm_num [sampleEnergy, multiplier]

/-- With a larger stable step the signed readout jumps across the pole.
Its denominator is nonzero at every integer sample, despite the intervening pole. -/
theorem concrete_skips_pole :
    factor 0 4 (3 / 16) = 16 ∧
    signedAt 0 4 (3 / 16) 4 16 0 = 32 / 3 ∧
    signedAt 0 4 (3 / 16) 4 16 1 = -8 / 3 ∧
    (sampleClock 0 4 (3 / 16) 0 < poleTime 0 4 4 16 ∧
      poleTime 0 4 4 16 < sampleClock 0 4 (3 / 16) 1) ∧
    (∀ k : ℕ, sampleEnergy (3 / 16) 4 16 k - sampleEnergy (3 / 16) 0 4 k ≠ 0) := by
  refine ⟨by norm_num [factor, multiplier], by norm_num [signedAt, signed, sampleEnergy, multiplier, gap],
    by norm_num [signedAt, signed, sampleEnergy, multiplier, gap], ?_, ?_⟩
  · constructor
    · apply (before_pole_iff 0 4 (3 / 16) 4 16 0 (by norm_num)
        (by norm_num [multiplier]) (by norm_num [multiplier]) (by norm_num) (by norm_num)).mp
      norm_num
    · apply (mul_lt_mul_iff_right₀ (gap_pos 0 4 (by norm_num))).mp
      apply exp_lt_exp.mp
      rw [crossing_factor 0 4 4 16 (by norm_num) (by norm_num) (by norm_num),
        sample_clock_factor 0 4 (3 / 16) 1 (by norm_num)
          (by norm_num [multiplier]) (by norm_num [multiplier])]
      norm_num [factor, multiplier]
  · intro k
    rw [ne_eq, pole_at_sample_iff 0 4 (3 / 16) 4 16 k (by norm_num [multiplier])]
    norm_num [factor, multiplier]
    have hp (j : ℕ) : (1 : ℝ) ≤ 16 ^ j := by
      induction j with
      | zero => norm_num
      | succ j ih => rw [pow_succ]; nlinarith
    cases k with
    | zero => norm_num
    | succ k => rw [pow_succ]; nlinarith [hp k]

end TwoWaveDiscreteGapBridge

#print axioms TwoWaveDiscreteGapBridge.factor_square
#print axioms TwoWaveDiscreteGapBridge.factor_pos
#print axioms TwoWaveDiscreteGapBridge.forward_multipliers
#print axioms TwoWaveDiscreteGapBridge.stable_multiplier
#print axioms TwoWaveDiscreteGapBridge.factor_gt_one
#print axioms TwoWaveDiscreteGapBridge.clock_pos
#print axioms TwoWaveDiscreteGapBridge.zero_step
#print axioms TwoWaveDiscreteGapBridge.clock_factor
#print axioms TwoWaveDiscreteGapBridge.sample_clock_factor
#print axioms TwoWaveDiscreteGapBridge.sample_energy_zero
#print axioms TwoWaveDiscreteGapBridge.sample_energy_pos
#print axioms TwoWaveDiscreteGapBridge.sample_energy_factor
#print axioms TwoWaveDiscreteGapBridge.ordinary_reduced
#print axioms TwoWaveDiscreteGapBridge.signed_reduced
#print axioms TwoWaveDiscreteGapBridge.ordinary_sample
#print axioms TwoWaveDiscreteGapBridge.signed_sample
#print axioms TwoWaveDiscreteGapBridge.ordinary_motion
#print axioms TwoWaveDiscreteGapBridge.signed_motion
#print axioms TwoWaveDiscreteGapBridge.ordinary_one_step
#print axioms TwoWaveDiscreteGapBridge.signed_one_step
#print axioms TwoWaveDiscreteGapBridge.sample_mirror
#print axioms TwoWaveDiscreteGapBridge.signed_denominator
#print axioms TwoWaveDiscreteGapBridge.pole_at_sample_iff
#print axioms TwoWaveDiscreteGapBridge.before_pole_iff
#print axioms TwoWaveDiscreteGapBridge.pole_clock_iff
#print axioms TwoWaveDiscreteGapBridge.before_index_iff
#print axioms TwoWaveDiscreteGapBridge.signed_regular_before
#print axioms TwoWaveDiscreteGapBridge.heat_step_mix
#print axioms TwoWaveDiscreteGapBridge.iterate_heat_mix
#print axioms TwoWaveDiscreteGapBridge.sample_coefficient_energy
#print axioms TwoWaveDiscreteGapBridge.iterate_size
#print axioms TwoWaveDiscreteGapBridge.iterate_cost
#print axioms TwoWaveDiscreteGapBridge.iterate_readout
#print axioms TwoWaveDiscreteGapBridge.iterate_motion
#print axioms TwoWaveDiscreteGapBridge.heat_step_readout
#print axioms TwoWaveDiscreteGapBridge.iterate_signed_mirror
#print axioms TwoWaveDiscreteGapBridge.killed_rough_mode
#print axioms TwoWaveDiscreteGapBridge.concrete_clock
#print axioms TwoWaveDiscreteGapBridge.concrete_hits_pole
#print axioms TwoWaveDiscreteGapBridge.concrete_skips_pole
