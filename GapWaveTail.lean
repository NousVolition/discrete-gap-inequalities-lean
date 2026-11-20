import TwoWaveGapBridge
import RingDecay

/-!
# Forcing and decay of the gap wave

Parts 1–3 are exact. On the square of side 2π with periodic boundaries, the
vorticity equation is `ω_t + (ψ_y ω_x − ψ_x ω_y) = ν Δω`, with `Δψ = −ω`.
The differential identities hold pointwise for real wavevectors. Integer
wavevectors give periodic waves on the box.

1. Two cosine waves feed their difference and sum with opposite signs. The
   feed vanishes for parallel or equal-length nonzero wavevectors.
2. The box has squared wavenumber gap 1, attained by (1, 0). The rescaled
   discrete-ring gap tends to 1.
3. A single wave solves the vorticity equation. Its amplitude is multiplied by
   exp(−ν |p|² t), which gives decay at rate ν for the gap wave when ν > 0.

Part 4 is the forecast model. It leaves out feedback from the modes created
by the two input waves. Its stationary-time and rescaled-tail theorems refer
to this forced scalar equation. With zero feed the forecast is identically zero.

The tab 9 comparisons reported alongside the model were 1.7% high at one
vertical crest and 0.15% high at three. The reported full-fluid late decay
rates were 0.0500, 0.1000 and 0.2000 at viscosities 0.05, 0.10 and 0.20.
These numbers are measurements.
-/

open Real Filter Topology

namespace GapWaveTail

/-! ## Part 1. When two waves push on each other -/

/-- Cross product of two wave directions. Zero exactly when they are parallel. -/
noncomputable def cross (p q : ℝ × ℝ) : ℝ := p.1 * q.2 - p.2 * q.1

/-- Squared length of a wave direction. -/
noncomputable def sq (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + p.2 ^ 2

/-- Phase of the wave `p` at the point `(x, y)`. -/
noncomputable def phase (p : ℝ × ℝ) (x y : ℝ) : ℝ := p.1 * x + p.2 * y

/-- Vorticity of two waves with heights `a` and `b`. -/
noncomputable def vort (a b : ℝ) (p q : ℝ × ℝ) (x y : ℝ) : ℝ :=
  a * cos (phase p x y) + b * cos (phase q x y)

/-- Its stream function, chosen so that `Δψ = −ω`. -/
noncomputable def stream (a b : ℝ) (p q : ℝ × ℝ) (x y : ℝ) : ℝ :=
  a / sq p * cos (phase p x y) + b / sq q * cos (phase q x y)

/-- The carrying term `ψ_y ω_x − ψ_x ω_y` of the fluid equation. -/
noncomputable def carry (ψ ω : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => ψ x s) y * deriv (fun s => ω s y) x
    - deriv (fun s => ψ s y) x * deriv (fun s => ω x s) y

/-- Second derivatives added up: `ω_xx + ω_yy`. -/
noncomputable def lap (ω : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => deriv (fun r => ω r y) s) x + deriv (fun s => deriv (fun r => ω x r) s) y

private theorem phase_dx (p : ℝ × ℝ) (x y : ℝ) :
    HasDerivAt (fun r => phase p r y) p.1 x := by
  simpa [phase] using (((hasDerivAt_id x).const_mul p.1).add_const (p.2 * y))

private theorem phase_dy (p : ℝ × ℝ) (x y : ℝ) :
    HasDerivAt (fun r => phase p x r) p.2 y := by
  simpa [phase] using (((hasDerivAt_id y).const_mul p.2).const_add (p.1 * x))

private theorem vort_dx (a b : ℝ) (p q : ℝ × ℝ) (x y : ℝ) :
    deriv (fun r => vort a b p q r y) x =
      (-a * p.1) * sin (phase p x y) + (-b * q.1) * sin (phase q x y) := by
  unfold vort
  rw [(((phase_dx p x y).cos.const_mul a).fun_add ((phase_dx q x y).cos.const_mul b)).deriv]
  ring

private theorem vort_dy (a b : ℝ) (p q : ℝ × ℝ) (x y : ℝ) :
    deriv (fun r => vort a b p q x r) y =
      (-a * p.2) * sin (phase p x y) + (-b * q.2) * sin (phase q x y) := by
  unfold vort
  rw [(((phase_dy p x y).cos.const_mul a).fun_add ((phase_dy q x y).cos.const_mul b)).deriv]
  ring

private theorem lap_vort (a b : ℝ) (p q : ℝ × ℝ) (x y : ℝ) :
    lap (vort a b p q) x y =
      -(a * sq p * cos (phase p x y) + b * sq q * cos (phase q x y)) := by
  simp only [lap, vort_dx, vort_dy]
  rw [(((phase_dx p x y).sin.const_mul (-a * p.1)).fun_add
       ((phase_dx q x y).sin.const_mul (-b * q.1))).deriv,
      (((phase_dy p x y).sin.const_mul (-a * p.2)).fun_add
       ((phase_dy q x y).sin.const_mul (-b * q.2))).deriv]
  unfold sq
  ring

/-- The stream function really satisfies `Δψ = −ω`. -/
theorem lap_stream (a b : ℝ) (p q : ℝ × ℝ) (hp : sq p ≠ 0) (hq : sq q ≠ 0) (x y : ℝ) :
    lap (stream a b p q) x y = - vort a b p q x y := by
  change lap (vort (a / sq p) (b / sq q) p q) x y = _
  rw [lap_vort]
  simp [vort, div_mul_cancel₀ _ hp, div_mul_cancel₀ _ hq]

/-- **How two waves push on each other.** -/
theorem carry_two_waves (a b : ℝ) (p q : ℝ × ℝ) (hp : sq p ≠ 0) (hq : sq q ≠ 0) (x y : ℝ) :
    carry (stream a b p q) (vort a b p q) x y =
      -(a * b * cross p q * (1 / sq p - 1 / sq q)) * (sin (phase p x y) * sin (phase q x y)) := by
  change carry (vort (a / sq p) (b / sq q) p q) (vort a b p q) x y = _
  simp only [carry, vort_dx, vort_dy, cross]
  field_simp [hp, hq]
  ring

/-- **Parallel waves do not push on each other.** -/
theorem carry_parallel (a b : ℝ) (p q : ℝ × ℝ) (hp : sq p ≠ 0) (hq : sq q ≠ 0)
    (h : cross p q = 0) (x y : ℝ) :
    carry (stream a b p q) (vort a b p q) x y = 0 := by
  rw [carry_two_waves a b p q hp hq, h]
  ring

/-- Waves of equal squared length do not push on each other. -/
theorem carry_equal_length (a b : ℝ) (p q : ℝ × ℝ) (hp : sq p ≠ 0) (hq : sq q ≠ 0)
    (h : sq p = sq q) (x y : ℝ) :
    carry (stream a b p q) (vort a b p q) x y = 0 := by
  rw [carry_two_waves a b p q hp hq, h]
  ring

/-- A wave alone does not push on itself. -/
theorem carry_single (a : ℝ) (p q : ℝ × ℝ) (hp : sq p ≠ 0) (hq : sq q ≠ 0) (x y : ℝ) :
    carry (stream a 0 p q) (vort a 0 p q) x y = 0 := by
  rw [carry_two_waves a 0 p q hp hq]
  ring

/-- The rate at which waves `p` and `q` feed the difference wave `p − q`. -/
noncomputable def feed (p q : ℝ × ℝ) : ℝ := cross p q * (1 / sq p - 1 / sq q) / 2

/-- The push, written as what it feeds: the difference wave and the sum wave. -/
theorem carry_feeds (a b : ℝ) (p q : ℝ × ℝ) (hp : sq p ≠ 0) (hq : sq q ≠ 0) (x y : ℝ) :
    -carry (stream a b p q) (vort a b p q) x y =
      a * b * feed p q * (cos (phase (p - q) x y) - cos (phase (p + q) x y)) := by
  have hsub : phase (p - q) x y = phase p x y - phase q x y := by
    simp [phase]; ring
  have hadd : phase (p + q) x y = phase p x y + phase q x y := by
    simp [phase]; ring
  rw [carry_two_waves a b p q hp hq, hsub, hadd, cos_sub, cos_add]
  unfold feed
  ring

/-- The feed is zero exactly for parallel waves or waves of equal squared length. -/
theorem feed_eq_zero_iff (p q : ℝ × ℝ) (hp : sq p ≠ 0) (hq : sq q ≠ 0) :
    feed p q = 0 ↔ cross p q = 0 ∨ sq p = sq q := by
  constructor
  · intro h
    have hz : cross p q * (1 / sq p - 1 / sq q) = 0 := by
      unfold feed at h
      linarith
    rcases mul_eq_zero.mp hz with hc | hi
    · exact Or.inl hc
    · exact Or.inr (by
        have he := sub_eq_zero.mp hi
        field_simp [hp, hq] at he
        exact he.symm)
  · rintro (hc | hs) <;> simp [feed, *]

/-- The tested stripes: two and three crests across, `m` crests up. -/
theorem feed_tested (m : ℝ) :
    feed ((2 : ℝ), m) ((3 : ℝ), m) = -5 * m / (2 * (4 + m ^ 2) * (9 + m ^ 2)) := by
  have h4 : (4 : ℝ) + m ^ 2 ≠ 0 := by positivity
  have h9 : (9 : ℝ) + m ^ 2 ≠ 0 := by positivity
  norm_num [feed, cross, sq]
  field_simp [h4, h9]
  ring

/-- For the tested stripes the feed is zero exactly when the stripes are straight. -/
theorem feed_tested_eq_zero_iff (m : ℝ) : feed ((2 : ℝ), m) ((3 : ℝ), m) = 0 ↔ m = 0 := by
  have h4 : (4 : ℝ) + m ^ 2 ≠ 0 := by positivity
  have h9 : (9 : ℝ) + m ^ 2 ≠ 0 := by positivity
  rw [feed_tested]
  simp [div_eq_zero_iff, mul_eq_zero, h4, h9]

/-- Mirror: leaning the other way reverses the sign of the feed and keeps its size. -/
theorem feed_tested_mirror (m : ℝ) :
    feed ((2 : ℝ), -m) ((3 : ℝ), -m) = -feed ((2 : ℝ), m) ((3 : ℝ), m) := by
  rw [feed_tested, feed_tested]
  ring

/-! ## Part 2. The box's gap -/

/-- Every nonzero whole-number wave has squared length at least 1. -/
theorem box_gap (k : ℤ × ℤ) (hk : k ≠ 0) : 1 ≤ k.1 ^ 2 + k.2 ^ 2 := by
  rcases k with ⟨i, j⟩
  change 1 ≤ i ^ 2 + j ^ 2
  have h : i ≠ 0 ∨ j ≠ 0 := by
    by_contra! hz
    exact hk (Prod.ext hz.1 hz.2)
  rcases h with hi | hj
  · have := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hi) (sq_nonneg j)
    omega
  · have := add_pos_of_nonneg_of_pos (sq_nonneg i) (sq_pos_of_ne_zero hj)
    omega

/-- The broad wave `(1, 0)` attains it. -/
theorem box_gap_attained : sq ((1 : ℝ), (0 : ℝ)) = 1 := by
  norm_num [sq]

/-- The n-point ring's gap, measured in the box's units, tends to the box's gap. -/
theorem ring_gap_tends_to_box_gap :
    Tendsto (fun n : ℕ => RingDecay.gap n / (2 * π / n) ^ 2) atTop (𝓝 1) := by
  have hangle := tendsto_const_div_atTop_nhds_zero_nat π
  have hs := ((Real.continuous_sinc.tendsto 0).comp hangle).pow 2
  rw [Real.sinc_zero, one_pow] at hs
  refine hs.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  change sinc (π / n) ^ 2 = RingDecay.gap n / (2 * π / n) ^ 2
  rw [Real.sinc_of_ne_zero (div_ne_zero Real.pi_ne_zero hn'), RingDecay.gap_eq_four_sin_sq]
  field_simp [hn', Real.pi_ne_zero]
  ring

/-! ## Part 3. One wave alone: an exact solution of the fluid equation -/

/-- One wave of starting height `a`, fading at viscosity × its squared length. -/
noncomputable def lone (ν a : ℝ) (p : ℝ × ℝ) (t x y : ℝ) : ℝ :=
  TwoWaveGapBridge.coefficient (ν * sq p) a t * cos (phase p x y)

/-- Its stream function. -/
noncomputable def loneStream (ν a : ℝ) (p : ℝ × ℝ) (t x y : ℝ) : ℝ :=
  lone ν a p t x y / sq p

/-- **One wave alone solves the full fluid equation**: time change + carrying term = ν Δω. -/
theorem lone_solves (ν a : ℝ) (p : ℝ × ℝ) (hp : sq p ≠ 0) (t x y : ℝ) :
    HasDerivAt (fun s => lone ν a p s x y)
      (ν * lap (lone ν a p t) x y - carry (loneStream ν a p t) (lone ν a p t) x y) t := by
  let c := TwoWaveGapBridge.coefficient (ν * sq p) a t
  have hv : lone ν a p t = vort c 0 p p := by
    funext x y
    simp [lone, c, vort]
  have hs : loneStream ν a p t = stream c 0 p p := by
    funext x y
    simp [loneStream, lone, c, stream]
    ring
  have ht := (TwoWaveGapBridge.coefficient_deriv (ν * sq p) a t).mul_const (cos (phase p x y))
  rw [hs, hv, carry_single _ _ _ hp hp, lap_vort]
  apply ht.congr_deriv
  change -(ν * sq p) * c * cos (phase p x y) =
    ν * -(c * sq p * cos (phase p x y) + 0 * sq p * cos (phase p x y)) - 0
  ring

/-- **The gap wave's tail.** Alone, the broad wave `(1, 0)` fades at exactly viscosity × gap. -/
theorem gap_wave_fades (ν a t x y : ℝ) :
    lone ν a ((1 : ℝ), (0 : ℝ)) t x y = a * exp (-(ν * 1) * t) * cos x := by
  simp [lone, TwoWaveGapBridge.coefficient, sq, phase]

/-! ## Part 4. The forecast model (leaves out feedback) -/

/-- The broad wave when it is fed at rate `F` by a pair fading at combined rate `α`,
and fades itself at rate `β`. -/
noncomputable def broad (F α β t : ℝ) : ℝ := F * (exp (-β * t) - exp (-α * t)) / (α - β)

theorem broad_zero (F α β : ℝ) : broad F α β 0 = 0 := by
  simp [broad]

private theorem broad_deriv (F α β t : ℝ) :
    HasDerivAt (broad F α β)
      (F * (-β * exp (-β * t) - (-α * exp (-α * t))) / (α - β)) t := by
  have decay (r : ℝ) : HasDerivAt (fun s : ℝ => exp (-r * s)) (-r * exp (-r * t)) t := by
    simpa only [id_eq, mul_one, mul_comm] using ((hasDerivAt_id t).const_mul (-r)).exp
  exact (((decay β).sub (decay α)).const_mul F).div_const (α - β)

/-- It solves `b' = −β b + F e^{−α t}`. -/
theorem broad_solves (F α β t : ℝ) (h : α ≠ β) :
    HasDerivAt (broad F α β) (-β * broad F α β t + F * exp (-α * t)) t := by
  convert broad_deriv F α β t using 1
  unfold broad
  field_simp [sub_ne_zero.mpr h]
  ring

/-- No feed, no broad wave. -/
theorem broad_no_feed (α β t : ℝ) : broad 0 α β t = 0 := by
  simp [broad]

/-- Mirror: reversing the feed reverses the broad wave at every moment. -/
theorem broad_mirror (F α β t : ℝ) : broad (-F) α β t = -broad F α β t := by
  unfold broad
  ring

/-- Stationary time of the forecast for `0 < β < α`. -/
noncomputable def peakTime (α β : ℝ) : ℝ := log (α / β) / (α - β)

theorem peakTime_pos (α β : ℝ) (hβ : 0 < β) (h : β < α) : 0 < peakTime α β := by
  exact div_pos (Real.log_pos ((one_lt_div hβ).mpr h)) (sub_pos.mpr h)

/-- The derivative of the signed broad wave vanishes at `peakTime`. -/
theorem broad_peak (F α β : ℝ) (hβ : 0 < β) (h : β < α) :
    HasDerivAt (broad F α β) 0 (peakTime α β) := by
  let T := peakTime α β
  have hlog : (α - β) * T = log (α / β) := by
    unfold T peakTime
    field_simp [sub_ne_zero.mpr h.ne']
  have hexp : exp (-β * T) = exp (-α * T) * (α / β) := by
    calc
      exp (-β * T) = exp (-α * T + (α - β) * T) := by congr 1; ring
      _ = exp (-α * T) * (α / β) := by
        rw [exp_add, hlog, Real.exp_log (div_pos (hβ.trans h) hβ)]
  change HasDerivAt _ 0 T
  convert broad_deriv F α β T using 1
  rw [hexp]
  field_simp [hβ.ne', sub_ne_zero.mpr h.ne']
  ring

/-- Rescaling by exp(βt) gives the tail coefficient, including the zero-feed case. -/
theorem broad_tail (F α β : ℝ) (h : β < α) :
    Tendsto (fun t => broad F α β t * exp (β * t)) atTop (𝓝 (F / (α - β))) := by
  have hdecay : Tendsto (fun t : ℝ => exp (-((α - β) * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (sub_pos.mpr h))
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hlim := (((hone.sub hdecay).const_mul F).div_const (α - β))
  simp only [sub_zero, mul_one] at hlim
  refine hlim.congr fun t => ?_
  have hβ : exp (-β * t) * exp (β * t) = 1 := by
    rw [← exp_add, show -β * t + β * t = 0 by ring, exp_zero]
  have hα : exp (-α * t) * exp (β * t) = exp (-((α - β) * t)) := by
    rw [← exp_add]
    congr 1
    ring
  change F * (1 - exp (-((α - β) * t))) / (α - β) = broad F α β t * exp (β * t)
  rw [← hα, ← hβ]
  unfold broad
  ring

/-- The forecast used before the tab 9 runs: viscosity `ν`, stripes `(2, m)` and `(3, m)`,
and the box's gap 1 as the broad wave's own fade rate. -/
noncomputable def forecast (ν m t : ℝ) : ℝ :=
  broad (feed ((2 : ℝ), m) ((3 : ℝ), m))
    (ν * (sq ((2 : ℝ), m) + sq ((3 : ℝ), m))) (ν * 1) t

/-- Straight stripes have zero feed and hence zero broad-wave forecast. -/
theorem forecast_straight (ν t : ℝ) : forecast ν 0 t = 0 := by
  simp [forecast, (feed_tested_eq_zero_iff 0).mpr rfl, broad_no_feed]

/-- Leaning the other way: same size at every moment, opposite sign. -/
theorem forecast_mirror (ν m t : ℝ) : forecast ν (-m) t = -forecast ν m t := by
  simp [forecast, feed_tested_mirror, sq, broad_mirror]

private theorem forecast_rates (ν m : ℝ) (hν : 0 < ν) :
    ν * 1 < ν * (sq ((2 : ℝ), m) + sq ((3 : ℝ), m)) := by
  apply mul_lt_mul_of_pos_left _ hν
  dsimp [sq]
  nlinarith [sq_nonneg m]

/-- The forecast derivative vanishes at the stated time with `β = ν × gap`. -/
theorem forecast_peak (ν m : ℝ) (hν : 0 < ν) :
    HasDerivAt (forecast ν m) 0
      (peakTime (ν * (sq ((2 : ℝ), m) + sq ((3 : ℝ), m))) (ν * 1)) := by
  exact broad_peak _ _ _ (by simpa using hν) (forecast_rates ν m hν)

/-- Rescaling by the viscosity times gap decay factor gives the forecast tail coefficient. -/
theorem forecast_tail (ν m : ℝ) (hν : 0 < ν) :
    Tendsto (fun t => forecast ν m t * exp (ν * 1 * t)) atTop
      (𝓝 (feed ((2 : ℝ), m) ((3 : ℝ), m)
        / (ν * (sq ((2 : ℝ), m) + sq ((3 : ℝ), m)) - ν * 1))) := by
  exact broad_tail _ _ _ (forecast_rates ν m hν)

end GapWaveTail
