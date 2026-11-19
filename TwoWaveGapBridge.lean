import RingGapBridge

/-!
# The two-wave map and its signed pole

For orthogonal ring eigenmodes with eigenvalues `ls < lr`, the squared mode sizes evolve as
`P(t) = P0 * exp (-2*ls*t)` and `Q(t) = Q0 * exp (-2*lr*t)`. The scalar gap is `2*(lr-ls)`.
The ordinary readout is `g*Q/(P+Q)`; its toy mirror is the signed readout `g*Q/(Q-P)`.
For positive initial mode sizes, a future pole occurs exactly when `Q0 > P0`, at
`log(Q0/P0)/g`. The signed readout diverges from the left while the ordinary one equals `g/2`.
The ring trajectory itself remains regular. The signed quotient is not an ordinary positive
cost/size quotient, and its mirror is not claimed to be the alternating ring flip.

The ring section proves the integration-by-parts identity, the two-mode size and cost formulas,
and the continuous heat equation coordinate by coordinate. Eigenmode and orthogonality conditions
are explicit; a flat/alternating four-dot example verifies that these conditions are realizable.

The motion is continuous heat. The interval and limit statements exclude interpreting Lean's
totalized division value at a pole as a finite physical height.
-/

open Real Filter Topology Finset

namespace TwoWaveGapBridge

noncomputable def gap (ls lr : ℝ) : ℝ := 2 * (lr - ls)

noncomputable def energy (l E t : ℝ) : ℝ := E * exp (-2 * l * t)

noncomputable def ordinary (g P Q : ℝ) : ℝ := g * Q / (P + Q)

noncomputable def signed (g P Q : ℝ) : ℝ := g * Q / (Q - P)

noncomputable def ordinaryFlow (ls lr P Q t : ℝ) : ℝ :=
  ordinary (gap ls lr) (energy ls P t) (energy lr Q t)

noncomputable def signedFlow (ls lr P Q t : ℝ) : ℝ :=
  signed (gap ls lr) (energy ls P t) (energy lr Q t)

noncomputable def poleTime (ls lr P Q : ℝ) : ℝ := log (Q / P) / gap ls lr

theorem gap_pos (ls lr : ℝ) (hl : ls < lr) : 0 < gap ls lr := by
  unfold gap
  linarith

theorem flat_gap (lr : ℝ) : gap 0 lr = 2 * lr := by simp [gap]

theorem energy_zero (l E : ℝ) : energy l E 0 = E := by simp [energy]

theorem energy_pos (l E t : ℝ) (hE : 0 < E) : 0 < energy l E t :=
  mul_pos hE (exp_pos _)

theorem energy_deriv (l E t : ℝ) :
    HasDerivAt (energy l E) (-2 * l * energy l E t) t := by
  have h := (((hasDerivAt_id t).const_mul (-2 * l)).exp).const_mul E
  change HasDerivAt (fun s : ℝ => E * exp (-2 * l * s))
    (-2 * l * (E * exp (-2 * l * t))) t
  simpa only [id_eq, mul_one, one_mul, mul_assoc, mul_left_comm, mul_comm] using h

/-- Factoring out the rough wave's positive decay isolates the relative growth factor. -/
theorem energy_factor (ls lr P t : ℝ) :
    energy ls P t = (P * exp (gap ls lr * t)) * exp (-2 * lr * t) := by
  unfold energy
  rw [show -2 * ls * t = gap ls lr * t + (-2 * lr * t) by unfold gap; ring, exp_add]
  ring

theorem ordinary_reduced (ls lr P Q t : ℝ) :
    ordinaryFlow ls lr P Q t = gap ls lr * Q / (P * exp (gap ls lr * t) + Q) := by
  unfold ordinaryFlow ordinary
  rw [energy_factor ls lr P t]
  unfold energy
  rw [← add_mul, ← mul_assoc]
  exact mul_div_mul_right _ _ (exp_ne_zero _)

theorem signed_reduced (ls lr P Q t : ℝ) :
    signedFlow ls lr P Q t = gap ls lr * Q / (Q - P * exp (gap ls lr * t)) := by
  unfold signedFlow signed
  rw [energy_factor ls lr P t]
  unfold energy
  rw [← sub_mul, ← mul_assoc]
  exact mul_div_mul_right _ _ (exp_ne_zero _)

theorem ordinary_between (g P Q : ℝ) (hg : 0 < g) (hP : 0 < P) (hQ : 0 < Q) :
    0 < ordinary g P Q ∧ ordinary g P Q < g := by
  have hsum : 0 < P + Q := add_pos hP hQ
  constructor
  · exact div_pos (mul_pos hg hQ) hsum
  · unfold ordinary
    rw [div_lt_iff₀ hsum]
    nlinarith [mul_pos hg hP]

theorem signed_above_gap (g P Q : ℝ) (hg : 0 < g) (hP : 0 < P) (hPQ : P < Q) :
    g < signed g P Q := by
  unfold signed
  rw [lt_div_iff₀ (sub_pos.mpr hPQ)]
  nlinarith [mul_pos hg hP]

theorem ordinary_z (g P Q : ℝ) (hg : g ≠ 0) (hQ : Q ≠ 0) :
    GapMirrorCalculus.z g (ordinary g P Q) = -P / Q := by
  unfold GapMirrorCalculus.z ordinary
  field_simp
  ring

theorem signed_z (g P Q : ℝ) (hg : g ≠ 0) (hQ : Q ≠ 0) :
    GapMirrorCalculus.z g (signed g P Q) = P / Q := by
  unfold GapMirrorCalculus.z signed
  field_simp
  ring

/-- The mirror changes the denominator from a sum to a signed difference. -/
theorem signed_is_mirror (g P Q : ℝ) (hg : 0 < g) (hP : 0 < P) (hQ : 0 < Q) :
    signed g P Q = GapMirrorCalculus.mirror g (ordinary g P Q) := by
  have hs : 0 < P + Q := add_pos hP hQ
  have hd : 2 * ordinary g P Q - g = g * (Q - P) / (P + Q) := by
    unfold ordinary
    field_simp
    ring
  unfold GapMirrorCalculus.mirror
  rw [hd]
  unfold signed ordinary
  field_simp

theorem ordinary_motion (ls lr P Q t : ℝ) (hl : ls < lr) (hP : 0 < P) (hQ : 0 < Q) :
    ordinaryFlow ls lr P Q t =
      GapMirrorCalculus.bump (gap ls lr) (ordinary (gap ls lr) P Q) t := by
  rw [ordinary_reduced]
  unfold GapMirrorCalculus.bump
  rw [ordinary_z _ _ _ (gap_pos ls lr hl).ne' hQ.ne']
  have hs : P * exp (gap ls lr * t) + Q ≠ 0 :=
    (add_pos (mul_pos hP (exp_pos _)) hQ).ne'
  field_simp [hQ.ne', hs]
  rw [show Q - -(P * exp (gap ls lr * t)) = P * exp (gap ls lr * t) + Q by ring]
  field_simp [hs]

/-- Algebraic equality also holds at totalized poles; regular evolution is stated below. -/
theorem signed_motion (ls lr P Q t : ℝ) (hl : ls < lr) (hQ : 0 < Q) :
    signedFlow ls lr P Q t =
      GapMirrorCalculus.bump (gap ls lr) (signed (gap ls lr) P Q) t := by
  rw [signed_reduced]
  unfold GapMirrorCalculus.bump
  rw [signed_z _ _ _ (gap_pos ls lr hl).ne' hQ.ne']
  field_simp

theorem crossing_factor (ls lr P Q : ℝ) (hl : ls < lr) (hP : 0 < P) (hQ : 0 < Q) :
    exp (gap ls lr * poleTime ls lr P Q) = Q / P := by
  have hg : gap ls lr ≠ 0 := (gap_pos ls lr hl).ne'
  unfold poleTime
  rw [mul_div_cancel₀ _ hg, exp_log (div_pos hQ hP)]

/-- The two positive squared mode sizes agree at exactly one real time. -/
theorem energies_equal_iff (ls lr P Q t : ℝ)
    (hl : ls < lr) (hP : 0 < P) (hQ : 0 < Q) :
    energy ls P t = energy lr Q t ↔ t = poleTime ls lr P Q := by
  rw [energy_factor ls lr P t]
  unfold energy
  rw [mul_left_inj' (exp_ne_zero _)]
  have hratio : P * exp (gap ls lr * t) = Q ↔ exp (gap ls lr * t) = Q / P := by
    constructor
    · intro h
      apply (eq_div_iff hP.ne').2
      simpa [mul_comm] using h
    · intro h
      rw [h]
      field_simp
  rw [hratio, ← crossing_factor ls lr P Q hl hP hQ, exp_injective.eq_iff]
  exact mul_right_inj' (gap_pos ls lr hl).ne'

theorem rough_larger_before (ls lr P Q t : ℝ) (hl : ls < lr)
    (hP : 0 < P) (hQ : 0 < Q) (ht : t < poleTime ls lr P Q) :
    energy ls P t < energy lr Q t := by
  have hlt : exp (gap ls lr * t) < Q / P := by
    rw [← crossing_factor ls lr P Q hl hP hQ, exp_lt_exp]
    exact mul_lt_mul_of_pos_left ht (gap_pos ls lr hl)
  have hm := (lt_div_iff₀ hP).1 hlt
  rw [energy_factor ls lr P t]
  unfold energy
  apply mul_lt_mul_of_pos_right _ (exp_pos _)
  simpa [mul_comm] using hm

theorem pole_time_pos_iff (ls lr P Q : ℝ) (hl : ls < lr) (hP : 0 < P) (hQ : 0 < Q) :
    0 < poleTime ls lr P Q ↔ P < Q := by
  unfold poleTime
  rw [div_pos_iff_of_pos_right (gap_pos ls lr hl), log_pos_iff (div_pos hQ hP).le,
    lt_div_iff₀ hP]
  simp

theorem pole_time_neg_iff (ls lr P Q : ℝ) (hl : ls < lr) (hP : 0 < P) (hQ : 0 < Q) :
    poleTime ls lr P Q < 0 ↔ Q < P := by
  unfold poleTime
  rw [div_lt_iff₀ (gap_pos ls lr hl), zero_mul, log_neg_iff (div_pos hQ hP),
    div_lt_one hP]

theorem equal_sizes_pole_zero (ls lr P : ℝ) (hP : P ≠ 0) : poleTime ls lr P P = 0 := by
  simp [poleTime, div_self hP]

theorem pole_eq_blowTime (ls lr P Q : ℝ) (hl : ls < lr) (hP : 0 < P) (hPQ : P < Q) :
    poleTime ls lr P Q = GapMirrorCalculus.blowTime (gap ls lr) (signed (gap ls lr) P Q) := by
  have hg : gap ls lr ≠ 0 := (gap_pos ls lr hl).ne'
  have hd : Q - P ≠ 0 := (sub_pos.mpr hPQ).ne'
  have he : signed (gap ls lr) P Q / (signed (gap ls lr) P Q - gap ls lr) = Q / P := by
    unfold signed
    field_simp [hP.ne']
    ring
  simp only [poleTime, GapMirrorCalculus.blowTime, he]

theorem ordinary_solves (ls lr P Q t : ℝ) (hl : ls < lr) (hP : 0 < P) (hQ : 0 < Q) :
    HasDerivAt (ordinaryFlow ls lr P Q)
      ((ordinaryFlow ls lr P Q t)^2 - gap ls lr * ordinaryFlow ls lr P Q t) t := by
  have hb := ordinary_between (gap ls lr) P Q (gap_pos ls lr hl) hP hQ
  have he : ordinaryFlow ls lr P Q = GapMirrorCalculus.bump (gap ls lr) (ordinary (gap ls lr) P Q) :=
    funext (fun s => ordinary_motion ls lr P Q s hl hP hQ)
  rw [he]
  exact (GapMirrorBridge.lower_regular _ _ t (gap_pos ls lr hl) hb.1 hb.2).2.2.1

/-- Every regular branch of the signed readout satisfies the same ODE, including negative heights. -/
theorem signed_solves_regular (ls lr P Q t : ℝ) (hd : energy lr Q t - energy ls P t ≠ 0) :
    HasDerivAt (signedFlow ls lr P Q)
      ((signedFlow ls lr P Q t)^2 - gap ls lr * signedFlow ls lr P Q t) t := by
  have h := ((energy_deriv lr Q t).const_mul (gap ls lr)).div
    ((energy_deriv lr Q t).sub (energy_deriv ls P t)) hd
  have he : ((gap ls lr * (-2 * lr * energy lr Q t)) * (energy lr Q t - energy ls P t) -
      (gap ls lr * energy lr Q t) * ((-2 * lr * energy lr Q t) - (-2 * ls * energy ls P t))) /
      (energy lr Q t - energy ls P t)^2 =
      (signedFlow ls lr P Q t)^2 - gap ls lr * signedFlow ls lr P Q t := by
    unfold signedFlow signed gap
    field_simp
    ring
  rw [← he]
  exact h

theorem signed_solves_before (ls lr P Q t : ℝ) (hl : ls < lr)
    (hP : 0 < P) (hPQ : P < Q) (ht : t < poleTime ls lr P Q) :
    HasDerivAt (signedFlow ls lr P Q)
      ((signedFlow ls lr P Q t)^2 - gap ls lr * signedFlow ls lr P Q t) t := by
  have hQ : 0 < Q := lt_trans hP hPQ
  have he : signedFlow ls lr P Q = GapMirrorCalculus.bump (gap ls lr) (signed (gap ls lr) P Q) :=
    funext (fun s => signed_motion ls lr P Q s hl hQ)
  rw [he]
  apply GapMirrorCalculus.bump_solves
  apply ne_of_gt
  apply GapMirrorCalculus.finite_before _ _ _ (gap_pos ls lr hl)
    (signed_above_gap _ _ _ (gap_pos ls lr hl) hP hPQ)
  rwa [← pole_eq_blowTime ls lr P Q hl hP hPQ]

theorem signed_blows_up (ls lr P Q : ℝ) (hl : ls < lr) (hP : 0 < P) (hPQ : P < Q) :
    Tendsto (signedFlow ls lr P Q) (𝓝[<] poleTime ls lr P Q) atTop := by
  have he : signedFlow ls lr P Q = GapMirrorCalculus.bump (gap ls lr) (signed (gap ls lr) P Q) :=
    funext (fun s => signed_motion ls lr P Q s hl (lt_trans hP hPQ))
  rw [he, pole_eq_blowTime ls lr P Q hl hP hPQ]
  exact GapMirrorCalculus.blows_up _ _ (gap_pos ls lr hl)
    (signed_above_gap _ _ _ (gap_pos ls lr hl) hP hPQ)

theorem ordinary_at_pole (ls lr P Q : ℝ) (hl : ls < lr) (hP : 0 < P) (hQ : 0 < Q) :
    ordinaryFlow ls lr P Q (poleTime ls lr P Q) = gap ls lr / 2 := by
  have he := (energies_equal_iff ls lr P Q (poleTime ls lr P Q) hl hP hQ).2 rfl
  have hp := energy_pos ls P (poleTime ls lr P Q) hP
  unfold ordinaryFlow ordinary
  rw [← he]
  field_simp
  ring

theorem no_future_pole (ls lr P Q : ℝ) (hl : ls < lr) (hP : 0 < P) (hQ : 0 < Q) (hQP : Q < P) :
    ∀ t : ℝ, 0 ≤ t → energy lr Q t - energy ls P t ≠ 0 := by
  intro t ht hzero
  have he : energy ls P t = energy lr Q t := (sub_eq_zero.mp hzero).symm
  have heq := (energies_equal_iff ls lr P Q t hl hP hQ).1 he
  have hneg := (pole_time_neg_iff ls lr P Q hl hP hQ).2 hQP
  linarith

theorem future_pole_iff (ls lr P Q : ℝ) (hl : ls < lr) (hP : 0 < P) (hQ : 0 < Q) :
    (∃ t : ℝ, 0 < t ∧ energy lr Q t - energy ls P t = 0) ↔ P < Q := by
  constructor
  · rintro ⟨t, ht, hz⟩
    have he := (energies_equal_iff ls lr P Q t hl hP hQ).1 (sub_eq_zero.mp hz).symm
    exact (pole_time_pos_iff ls lr P Q hl hP hQ).1 (by rwa [← he])
  · intro hPQ
    refine ⟨poleTime ls lr P Q, (pole_time_pos_iff ls lr P Q hl hP hQ).2 hPQ, ?_⟩
    exact sub_eq_zero.mpr ((energies_equal_iff ls lr P Q _ hl hP hQ).2 rfl).symm

theorem ordinary_fades (ls lr P Q : ℝ) (hl : ls < lr) (hP : 0 < P) (hQ : 0 < Q) :
    Tendsto (ordinaryFlow ls lr P Q) atTop (𝓝 0) := by
  have hb := ordinary_between (gap ls lr) P Q (gap_pos ls lr hl) hP hQ
  have he : ordinaryFlow ls lr P Q = GapMirrorCalculus.bump (gap ls lr) (ordinary (gap ls lr) P Q) :=
    funext (fun s => ordinary_motion ls lr P Q s hl hP hQ)
  rw [he]
  exact GapMirrorCalculus.fades _ _ (gap_pos ls lr hl) hb.1 hb.2

theorem pure_rough (g Q : ℝ) (hQ : Q ≠ 0) : ordinary g 0 Q = g := by simp [ordinary, hQ]

theorem pure_smooth (g P : ℝ) : ordinary g P 0 = 0 := by simp [ordinary]

theorem cost_ratio_map (ls lr P Q : ℝ) (hs : P + Q ≠ 0) :
    2 * ((ls * P + lr * Q) / (P + Q) - ls) = ordinary (gap ls lr) P Q := by
  unfold ordinary gap
  field_simp
  ring

/-- The signed readout comes from a difference of quadratic forms, not an ordinary ring cost. -/
theorem signed_ratio_map (ls lr P Q : ℝ) (hd : P - Q ≠ 0) :
    2 * ((ls * P - lr * Q) / (P - Q) - ls) = signed (gap ls lr) P Q := by
  have he : Q - P = -(P - Q) := by ring
  unfold signed gap
  rw [he, div_neg]
  field_simp
  ring

theorem mirror_at_time (ls lr P Q t : ℝ) (hl : ls < lr) (hP : 0 < P) (hQ : 0 < Q) :
    signedFlow ls lr P Q t = GapMirrorCalculus.mirror (gap ls lr) (ordinaryFlow ls lr P Q t) :=
  signed_is_mirror _ _ _ (gap_pos ls lr hl) (energy_pos ls P t hP) (energy_pos lr Q t hQ)

section Ring

variable {n : ℕ} [NeZero n]

noncomputable def dot (v w : ZMod n → ℝ) : ℝ := ∑ j, v j * w j

noncomputable def heatGenerator (f : ZMod n → ℝ) (j : ZMod n) : ℝ :=
  f (j + 1) - 2 * f j + f (j - 1)

noncomputable def mix (A B : ℝ) (v w : ZMod n → ℝ) (j : ZMod n) : ℝ :=
  A * v j + B * w j

noncomputable def coefficient (l a t : ℝ) : ℝ := a * exp (-l * t)

noncomputable def initialEnergy (a : ℝ) (v : ZMod n → ℝ) : ℝ := a ^ 2 * RingGapBridge.size v

noncomputable def ringFlow (ls lr a b : ℝ) (v w : ZMod n → ℝ) (t : ℝ) : ZMod n → ℝ :=
  mix (coefficient ls a t) (coefficient lr b t) v w

noncomputable def readout (ls : ℝ) (f : ZMod n → ℝ) : ℝ :=
  2 * (RingGapBridge.cost f / RingGapBridge.size f - ls)

/-- This readout also uses the specified mode decomposition. -/
noncomputable def signedReadout (ls lr a b : ℝ) (v w : ZMod n → ℝ) (t : ℝ) : ℝ :=
  signedFlow ls lr (initialEnergy a v) (initialEnergy b w) t

theorem cross_shift (f : ZMod n → ℝ) :
    (∑ j, f j * f (j - 1)) = ∑ j, f j * f (j + 1) := by
  calc
    (∑ j, f j * f (j - 1)) = ∑ j, f (j + 1) * f j :=
      Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun j => by simp)
    _ = ∑ j, f j * f (j + 1) := by
      apply sum_congr rfl
      intro j _
      ring

/-- Discrete integration by parts on the periodic ring, with exactly the existing edge cost. -/
theorem cost_eq_neg_dot_heat (f : ZMod n → ℝ) :
    RingGapBridge.cost f = -dot f (heatGenerator f) := by
  have hc : RingGapBridge.cost f = 2 * RingGapBridge.size f - 2 * ∑ j, f j * f (j + 1) := by
    calc
      RingGapBridge.cost f = ∑ j, (f (j + 1)^2 + f j^2 - 2 * (f j * f (j + 1))) := by
        apply sum_congr rfl
        intro j _
        ring
      _ = 2 * RingGapBridge.size f - 2 * ∑ j, f j * f (j + 1) := by
        rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, RingGapBridge.sum_shift]
        change RingGapBridge.size f + RingGapBridge.size f - _ = _
        ring
  have hh : dot f (heatGenerator f) = 2 * ∑ j, f j * f (j + 1) - 2 * RingGapBridge.size f := by
    calc
      dot f (heatGenerator f) = ∑ j, (f j * f (j + 1) - 2 * f j^2 + f j * f (j - 1)) := by
        apply sum_congr rfl
        intro j _
        unfold heatGenerator
        ring
      _ = 2 * ∑ j, f j * f (j + 1) - 2 * RingGapBridge.size f := by
        rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, cross_shift]
        change _ - 2 * RingGapBridge.size f + _ = _
        ring
  rw [hc, hh]
  ring

theorem size_mix (A B : ℝ) (v w : ZMod n → ℝ) (ho : dot v w = 0) :
    RingGapBridge.size (mix A B v w) = A^2 * RingGapBridge.size v + B^2 * RingGapBridge.size w := by
  calc
    RingGapBridge.size (mix A B v w) =
        ∑ j, (A^2 * v j^2 + B^2 * w j^2 + (2*A*B) * (v j*w j)) := by
      apply sum_congr rfl
      intro j _
      unfold mix
      ring
    _ = A^2 * RingGapBridge.size v + B^2 * RingGapBridge.size w + (2*A*B) * dot v w := by
      simp only [sum_add_distrib, ← mul_sum, RingGapBridge.size, dot]
    _ = A^2 * RingGapBridge.size v + B^2 * RingGapBridge.size w := by rw [ho, mul_zero, add_zero]

theorem dot_mix (A B C D : ℝ) (v w : ZMod n → ℝ) (ho : dot v w = 0) :
    dot (mix A B v w) (mix C D v w) =
      A*C * RingGapBridge.size v + B*D * RingGapBridge.size w := by
  calc
    dot (mix A B v w) (mix C D v w) =
        ∑ j, ((A*C) * v j^2 + (B*D) * w j^2 + (A*D+B*C) * (v j*w j)) := by
      apply sum_congr rfl
      intro j _
      unfold mix
      ring
    _ = A*C * RingGapBridge.size v + B*D * RingGapBridge.size w + (A*D+B*C) * dot v w := by
      simp only [sum_add_distrib, ← mul_sum, RingGapBridge.size, dot]
    _ = A*C * RingGapBridge.size v + B*D * RingGapBridge.size w := by rw [ho, mul_zero, add_zero]

omit [NeZero n] in
theorem heat_mix (A B : ℝ) (v w : ZMod n → ℝ) (j : ZMod n) :
    heatGenerator (mix A B v w) j = A * heatGenerator v j + B * heatGenerator w j := by
  unfold heatGenerator mix
  ring

theorem cost_mix (ls lr A B : ℝ) (v w : ZMod n → ℝ) (ho : dot v w = 0)
    (hv : ∀ j, heatGenerator v j = -ls * v j) (hw : ∀ j, heatGenerator w j = -lr * w j) :
    RingGapBridge.cost (mix A B v w) =
      ls * (A^2 * RingGapBridge.size v) + lr * (B^2 * RingGapBridge.size w) := by
  have hh : heatGenerator (mix A B v w) = mix (-ls*A) (-lr*B) v w := by
    funext j
    rw [heat_mix, hv, hw]
    unfold mix
    ring
  rw [cost_eq_neg_dot_heat, hh, dot_mix A B (-ls*A) (-lr*B) v w ho]
  ring

theorem coefficient_deriv (l a t : ℝ) :
    HasDerivAt (coefficient l a) (-l * coefficient l a t) t := by
  have h := (((hasDerivAt_id t).const_mul (-l)).exp).const_mul a
  change HasDerivAt (fun s : ℝ => a * exp (-l * s)) (-l * (a * exp (-l * t))) t
  simpa only [id_eq, mul_one, one_mul, mul_assoc, mul_left_comm, mul_comm] using h

theorem coefficient_energy (l a t : ℝ) (v : ZMod n → ℝ) :
    (coefficient l a t)^2 * RingGapBridge.size v = energy l (initialEnergy a v) t := by
  have he : (exp (-l * t))^2 = exp (-2 * l * t) := by
    rw [pow_two, ← exp_add]
    congr 1
    ring
  unfold coefficient energy initialEnergy
  rw [mul_pow, he]
  ring

omit [NeZero n] in
/-- Every coordinate is proved to follow the continuous ring heat equation. -/
theorem continuous_heat (ls lr a b t : ℝ) (v w : ZMod n → ℝ)
    (hv : ∀ j, heatGenerator v j = -ls * v j) (hw : ∀ j, heatGenerator w j = -lr * w j)
    (j : ZMod n) :
    HasDerivAt (fun s => ringFlow ls lr a b v w s j) (heatGenerator (ringFlow ls lr a b v w t) j) t := by
  have h := ((coefficient_deriv ls a t).mul_const (v j)).add
    ((coefficient_deriv lr b t).mul_const (w j))
  have hh : heatGenerator (ringFlow ls lr a b v w t) j =
      (-ls * coefficient ls a t) * v j + (-lr * coefficient lr b t) * w j := by
    unfold ringFlow
    rw [heat_mix, hv, hw]
    ring
  rw [hh]
  exact h

theorem flow_size (ls lr a b t : ℝ) (v w : ZMod n → ℝ) (ho : dot v w = 0) :
    RingGapBridge.size (ringFlow ls lr a b v w t) =
      energy ls (initialEnergy a v) t + energy lr (initialEnergy b w) t := by
  rw [ringFlow, size_mix _ _ v w ho, coefficient_energy, coefficient_energy]

theorem flow_cost (ls lr a b t : ℝ) (v w : ZMod n → ℝ) (ho : dot v w = 0)
    (hv : ∀ j, heatGenerator v j = -ls * v j) (hw : ∀ j, heatGenerator w j = -lr * w j) :
    RingGapBridge.cost (ringFlow ls lr a b v w t) =
      ls * energy ls (initialEnergy a v) t + lr * energy lr (initialEnergy b w) t := by
  rw [ringFlow, cost_mix _ _ _ _ v w ho hv hw, coefficient_energy, coefficient_energy]

/-- Claude's cost/size formula is the same scalar trajectory, for the actual evolving pattern. -/
theorem ring_readout (ls lr a b t : ℝ) (v w : ZMod n → ℝ) (ho : dot v w = 0)
    (hv : ∀ j, heatGenerator v j = -ls * v j) (hw : ∀ j, heatGenerator w j = -lr * w j)
    (hP : 0 < initialEnergy a v) (hQ : 0 < initialEnergy b w) :
    readout ls (ringFlow ls lr a b v w t) = ordinaryFlow ls lr (initialEnergy a v) (initialEnergy b w) t := by
  unfold readout
  rw [flow_cost ls lr a b t v w ho hv hw, flow_size ls lr a b t v w ho]
  exact cost_ratio_map _ _ _ _ (add_pos (energy_pos _ _ _ hP) (energy_pos _ _ _ hQ)).ne'

theorem ring_motion (ls lr a b t : ℝ) (v w : ZMod n → ℝ) (hl : ls < lr) (ho : dot v w = 0)
    (hv : ∀ j, heatGenerator v j = -ls * v j) (hw : ∀ j, heatGenerator w j = -lr * w j)
    (hP : 0 < initialEnergy a v) (hQ : 0 < initialEnergy b w) :
    readout ls (ringFlow ls lr a b v w t) =
      GapMirrorCalculus.bump (gap ls lr) (ordinary (gap ls lr) (initialEnergy a v) (initialEnergy b w)) t := by
  rw [ring_readout ls lr a b t v w ho hv hw hP hQ]
  exact ordinary_motion _ _ _ _ _ hl hP hQ

theorem ring_signed_mirror (ls lr a b t : ℝ) (v w : ZMod n → ℝ) (hl : ls < lr) (ho : dot v w = 0)
    (hv : ∀ j, heatGenerator v j = -ls * v j) (hw : ∀ j, heatGenerator w j = -lr * w j)
    (hP : 0 < initialEnergy a v) (hQ : 0 < initialEnergy b w) :
    signedReadout ls lr a b v w t = GapMirrorCalculus.mirror (gap ls lr) (readout ls (ringFlow ls lr a b v w t)) := by
  rw [ring_readout ls lr a b t v w ho hv hw hP hQ]
  exact mirror_at_time _ _ _ _ _ hl hP hQ

omit [NeZero n] in
/-- The ring is continuous at every real time, including any signed-readout pole. -/
theorem ring_regular (ls lr a b t : ℝ) (v w : ZMod n → ℝ)
    (hv : ∀ j, heatGenerator v j = -ls * v j) (hw : ∀ j, heatGenerator w j = -lr * w j)
    (j : ZMod n) : ContinuousAt (fun s => ringFlow ls lr a b v w s j) t :=
  (continuous_heat ls lr a b t v w hv hw j).continuousAt

/-- A future readout blow-up and a finite ring occur together; the ordinary readout is half-gap. -/
theorem ring_signed_event (ls lr a b : ℝ) (v w : ZMod n → ℝ) (hl : ls < lr) (ho : dot v w = 0)
    (hv : ∀ j, heatGenerator v j = -ls * v j) (hw : ∀ j, heatGenerator w j = -lr * w j)
    (hP : 0 < initialEnergy a v) (hPQ : initialEnergy a v < initialEnergy b w) :
    let T := poleTime ls lr (initialEnergy a v) (initialEnergy b w)
    0 < T ∧ Tendsto (signedReadout ls lr a b v w) (𝓝[<] T) atTop ∧
      readout ls (ringFlow ls lr a b v w T) = gap ls lr / 2 ∧
      ∀ j, ContinuousAt (fun s => ringFlow ls lr a b v w s j) T := by
  dsimp
  have hQ := lt_trans hP hPQ
  refine ⟨(pole_time_pos_iff _ _ _ _ hl hP hQ).2 hPQ,
    signed_blows_up _ _ _ _ hl hP hPQ, ?_, fun j => ring_regular _ _ _ _ _ v w hv hw j⟩
  rw [ring_readout _ _ _ _ _ v w ho hv hw hP hQ]
  exact ordinary_at_pole _ _ _ _ hl hP hQ

end Ring

/-- A concrete pair of ring eigenmodes makes the generic assumptions independently realizable. -/
noncomputable def flat4 (_j : ZMod 4) : ℝ := 1

noncomputable def rough4 (j : ZMod 4) : ℝ := if j.val = 0 ∨ j.val = 2 then 1 else -1

theorem flat4_eigen (j : ZMod 4) : heatGenerator flat4 j = -(0 : ℝ) * flat4 j := by
  norm_num [heatGenerator, flat4]

theorem rough4_eigen (j : ZMod 4) : heatGenerator rough4 j = -(4 : ℝ) * rough4 j := by
  fin_cases j
  · change (-1 : ℝ) - 2 * 1 + -1 = -4 * 1
    norm_num
  · change (1 : ℝ) - 2 * (-1) + 1 = -4 * (-1)
    norm_num
  · change (-1 : ℝ) - 2 * 1 + -1 = -4 * 1
    norm_num
  · change (1 : ℝ) - 2 * (-1) + 1 = -4 * (-1)
    norm_num

theorem four_mode_data : dot flat4 rough4 = 0 ∧ RingGapBridge.size flat4 = 4 ∧ RingGapBridge.size rough4 = 4 := by
  have hsum (f : ZMod 4 → ℝ) : (∑ j, f j) = f 0 + f 1 + f 2 + f 3 := by
    change (Fin 4 → ℝ) at f
    change (∑ j : Fin 4, f j) = f (0 : Fin 4) + f 1 + f 2 + f 3
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change f (0 : Fin 4) + (f 1 + (f 2 + f 3)) = f 0 + f 1 + f 2 + f 3
    ring
  unfold dot RingGapBridge.size
  rw [hsum, hsum, hsum]
  change (1 : ℝ)*1 + 1*(-1) + 1*1 + 1*(-1) = 0 ∧
    (1 : ℝ)^2 + 1^2 + 1^2 + 1^2 = 4 ∧
    (1 : ℝ)^2 + (-1)^2 + 1^2 + (-1)^2 = 4
  norm_num

/-- Actual flat and alternating four-dot modes, with initial squared sizes 4 and 16. -/
theorem concrete_signed_event :
    0 < poleTime 0 4 4 16 ∧ Tendsto (signedReadout 0 4 1 2 flat4 rough4) (𝓝[<] poleTime 0 4 4 16) atTop ∧
    readout 0 (ringFlow 0 4 1 2 flat4 rough4 (poleTime 0 4 4 16)) = 4 ∧
    ∀ j, ContinuousAt (fun s => ringFlow 0 4 1 2 flat4 rough4 s j) (poleTime 0 4 4 16) := by
  have hP : initialEnergy 1 flat4 = 4 := by simp [initialEnergy, four_mode_data.2.1]
  have hQ : initialEnergy 2 rough4 = 16 := by norm_num [initialEnergy, four_mode_data.2.2]
  have h := ring_signed_event 0 4 1 2 flat4 rough4 (by norm_num) four_mode_data.1 flat4_eigen rough4_eigen
    (by rw [hP]; norm_num) (by rw [hP, hQ]; norm_num)
  simpa only [hP, hQ, gap, sub_zero, mul_one, show (2 : ℝ) * 4 / 2 = 4 by norm_num] using h

end TwoWaveGapBridge

#print axioms TwoWaveGapBridge.gap_pos
#print axioms TwoWaveGapBridge.flat_gap
#print axioms TwoWaveGapBridge.energy_zero
#print axioms TwoWaveGapBridge.energy_pos
#print axioms TwoWaveGapBridge.energy_deriv
#print axioms TwoWaveGapBridge.energy_factor
#print axioms TwoWaveGapBridge.ordinary_reduced
#print axioms TwoWaveGapBridge.signed_reduced
#print axioms TwoWaveGapBridge.ordinary_between
#print axioms TwoWaveGapBridge.signed_above_gap
#print axioms TwoWaveGapBridge.ordinary_z
#print axioms TwoWaveGapBridge.signed_z
#print axioms TwoWaveGapBridge.signed_is_mirror
#print axioms TwoWaveGapBridge.ordinary_motion
#print axioms TwoWaveGapBridge.signed_motion
#print axioms TwoWaveGapBridge.crossing_factor
#print axioms TwoWaveGapBridge.energies_equal_iff
#print axioms TwoWaveGapBridge.rough_larger_before
#print axioms TwoWaveGapBridge.pole_time_pos_iff
#print axioms TwoWaveGapBridge.pole_time_neg_iff
#print axioms TwoWaveGapBridge.equal_sizes_pole_zero
#print axioms TwoWaveGapBridge.pole_eq_blowTime
#print axioms TwoWaveGapBridge.ordinary_solves
#print axioms TwoWaveGapBridge.signed_solves_regular
#print axioms TwoWaveGapBridge.signed_solves_before
#print axioms TwoWaveGapBridge.signed_blows_up
#print axioms TwoWaveGapBridge.ordinary_at_pole
#print axioms TwoWaveGapBridge.no_future_pole
#print axioms TwoWaveGapBridge.future_pole_iff
#print axioms TwoWaveGapBridge.ordinary_fades
#print axioms TwoWaveGapBridge.pure_rough
#print axioms TwoWaveGapBridge.pure_smooth
#print axioms TwoWaveGapBridge.cost_ratio_map
#print axioms TwoWaveGapBridge.signed_ratio_map
#print axioms TwoWaveGapBridge.mirror_at_time
#print axioms TwoWaveGapBridge.cross_shift
#print axioms TwoWaveGapBridge.cost_eq_neg_dot_heat
#print axioms TwoWaveGapBridge.size_mix
#print axioms TwoWaveGapBridge.dot_mix
#print axioms TwoWaveGapBridge.heat_mix
#print axioms TwoWaveGapBridge.cost_mix
#print axioms TwoWaveGapBridge.coefficient_deriv
#print axioms TwoWaveGapBridge.coefficient_energy
#print axioms TwoWaveGapBridge.continuous_heat
#print axioms TwoWaveGapBridge.flow_size
#print axioms TwoWaveGapBridge.flow_cost
#print axioms TwoWaveGapBridge.ring_readout
#print axioms TwoWaveGapBridge.ring_motion
#print axioms TwoWaveGapBridge.ring_signed_mirror
#print axioms TwoWaveGapBridge.ring_regular
#print axioms TwoWaveGapBridge.ring_signed_event
#print axioms TwoWaveGapBridge.flat4_eigen
#print axioms TwoWaveGapBridge.rough4_eigen
#print axioms TwoWaveGapBridge.four_mode_data
#print axioms TwoWaveGapBridge.concrete_signed_event
