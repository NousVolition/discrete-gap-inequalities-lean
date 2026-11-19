import GapMirror
import GapMirrorCalculus
import Mathlib.Data.Rat.Cast.Order

/-!
# The rational growth factor and the real clock describe the same scalar motion

`GapMirror.step` takes rational arguments, so it cannot be fed an arbitrary real exponential.
`realStep` is the same algebraic formula over the reals; `cast_step` proves exact agreement on
rational inputs. `real_step_at_time` identifies it with `GapMirrorCalculus.bump` when the factor
is `exp (g * t)`. `same_motion_before_blowup` also proves the relevant denominators are positive
and that the clock interval agrees with the pre-pole factor interval.

Every rational forward factor before its pole has an exact real clock `log r / g`, as proved by
`rational_step_at_clock`. No approximation or assumption that all exponentials are rational is used.

The last section distinguishes an upper bump's blow-up time from a lower bump's half-edge crossing.
Mathlib's total `Real.log` satisfies `log (-x) = log x`, so the two written clock formulas coincide
algebraically even though only the above-gap case is a blow-up. `both_in_future` retains the joint
event: divergence from the left and the mirror equal to half the gap at the same positive time.
This is an endpoint only for the upper solution. `mirror_continues` proves that the lower mirror
is regular at every real time, has a negative derivative, and tends to zero as time tends to infinity.
-/

open Real Filter Topology

namespace GapMirrorBridge

/-- The formula of `GapMirror.step`, extended to real inputs. -/
noncomputable def realStep (g r A : ℝ) : ℝ := g * A / (r * g - (r - 1) * A)

theorem cast_z (g A : ℚ) :
    (GapMirror.z g A : ℝ) = GapMirrorCalculus.z (g : ℝ) (A : ℝ) := by
  simp [GapMirror.z, GapMirrorCalculus.z]

theorem cast_mirror (g A : ℚ) :
    (GapMirror.mirror g A : ℝ) = GapMirrorCalculus.mirror (g : ℝ) (A : ℝ) := by
  simp [GapMirror.mirror, GapMirrorCalculus.mirror]

/-- The real extension preserves every value of the original rational operation. -/
theorem cast_step (g r A : ℚ) :
    (GapMirror.step g r A : ℝ) = realStep (g : ℝ) (r : ℝ) (A : ℝ) := by
  simp [GapMirror.step, realStep]

theorem denominator_factor (g r A : ℝ) (hA : A ≠ 0) :
    r * g - (r - 1) * A = A * (1 - GapMirrorCalculus.z g A * r) := by
  unfold GapMirrorCalculus.z
  field_simp
  ring

/-- Pointwise algebraic identity, including totalized values at poles.
Use `same_motion_before_blowup` for the physical pre-pole interval. -/
theorem real_step_at_time (g A t : ℝ) (hA : A ≠ 0) :
    realStep g (exp (g * t)) A = GapMirrorCalculus.bump g A t := by
  unfold realStep GapMirrorCalculus.bump
  rw [denominator_factor g (exp (g * t)) A hA, mul_comm A]
  exact mul_div_mul_right g _ hA

theorem factor_at_blowTime (g A : ℝ) (hg : 0 < g) (hA : g < A) :
    exp (g * GapMirrorCalculus.blowTime g A) = A / (A - g) := by
  have hA0 : 0 < A := lt_trans hg hA
  have hAg : 0 < A - g := sub_pos.mpr hA
  have he : g * GapMirrorCalculus.blowTime g A = log (A / (A - g)) := by
    unfold GapMirrorCalculus.blowTime
    field_simp
  rw [he, exp_log (div_pos hA0 hAg)]

/-- Being before the factor pole is equivalent to being before the clock-time blow-up. -/
theorem before_iff (g A t : ℝ) (hg : 0 < g) (hA : g < A) :
    exp (g * t) < A / (A - g) ↔ t < GapMirrorCalculus.blowTime g A := by
  rw [← factor_at_blowTime g A hg hA, exp_lt_exp]
  exact mul_lt_mul_iff_right₀ hg

/-- Exact equality of motions, with positive denominators and the original forward-factor range. -/
theorem same_motion_before_blowup (g A t : ℝ) (hg : 0 < g) (hA : g < A)
    (ht0 : 0 ≤ t) (ht : t < GapMirrorCalculus.blowTime g A) :
    realStep g (exp (g * t)) A = GapMirrorCalculus.bump g A t ∧
    0 < exp (g * t) * g - (exp (g * t) - 1) * A ∧
    1 ≤ exp (g * t) ∧ exp (g * t) < A / (A - g) := by
  have hA0 : 0 < A := lt_trans hg hA
  refine ⟨real_step_at_time g A t hA0.ne', ?_, one_le_exp (mul_nonneg hg.le ht0),
    (before_iff g A t hg hA).2 ht⟩
  rw [denominator_factor g (exp (g * t)) A hA0.ne']
  exact mul_pos hA0 (GapMirrorCalculus.finite_before g A t hg hA ht)

/-- Whenever an exponential factor is rational, the original operation itself matches the real bump. -/
theorem rational_step_at_time (g r A : ℚ) (t : ℝ) (hA : A ≠ 0)
    (hr : (r : ℝ) = exp ((g : ℝ) * t)) :
    (GapMirror.step g r A : ℝ) = GapMirrorCalculus.bump (g : ℝ) (A : ℝ) t := by
  rw [cast_step, hr]
  exact real_step_at_time _ _ _ (by exact_mod_cast hA)

/-- A positive factor corresponds exactly to the real clock `log r / g`. -/
theorem clock_factor (g r : ℝ) (hg : g ≠ 0) (hr : 0 < r) :
    exp (g * (log r / g)) = r := by
  have he : g * (log r / g) = log r := by field_simp
  rw [he, exp_log hr]

/-- Every pre-pole rational forward step has the same value at its exact, nonnegative real clock. -/
theorem rational_step_at_clock (g r A : ℚ) (hg : 0 < g) (hA : g < A)
    (hr : 1 ≤ r) (hbefore : r < A / (A - g)) :
    let t : ℝ := log (r : ℝ) / (g : ℝ)
    0 ≤ t ∧ t < GapMirrorCalculus.blowTime (g : ℝ) (A : ℝ) ∧
      (GapMirror.step g r A : ℝ) = GapMirrorCalculus.bump (g : ℝ) (A : ℝ) t := by
  dsimp
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hAR : (g : ℝ) < A := by exact_mod_cast hA
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hrR
  have hbR : (r : ℝ) < (A : ℝ) / ((A : ℝ) - (g : ℝ)) := by exact_mod_cast hbefore
  have hfactor := clock_factor (g : ℝ) (r : ℝ) hgR.ne' hr0
  refine ⟨div_nonneg (log_nonneg hrR) hgR.le, ?_, ?_⟩
  · apply (before_iff (g : ℝ) (A : ℝ) _ hgR hAR).1
    rwa [hfactor]
  · exact rational_step_at_time g r A _ (ne_of_gt (lt_trans hg hA)) hfactor.symm

/-- The motion written with the growth-factor formula has the same differential equation. -/
theorem real_step_solves_before (g A t : ℝ) (hg : 0 < g) (hA : g < A)
    (ht : t < GapMirrorCalculus.blowTime g A) :
    HasDerivAt (fun s : ℝ => realStep g (exp (g * s)) A)
      ((realStep g (exp (g * t)) A) ^ 2 - g * realStep g (exp (g * t)) A) t := by
  have hA0 : A ≠ 0 := (lt_trans hg hA).ne'
  have heq : (fun s : ℝ => realStep g (exp (g * s)) A) = GapMirrorCalculus.bump g A :=
    funext (fun s => real_step_at_time g A s hA0)
  rw [real_step_at_time g A t hA0, heq]
  exact GapMirrorCalculus.bump_solves g A t (GapMirrorCalculus.finite_before g A t hg hA ht).ne'

/-- "Both" is one shared future time: the upper limit diverges, and the mirror is half the gap. -/
theorem both_in_future (g A : ℝ) (hg : 0 < g) (hA : g < A) :
    0 < GapMirrorCalculus.blowTime g A ∧
    Tendsto (GapMirrorCalculus.bump g A) (𝓝[<] GapMirrorCalculus.blowTime g A) atTop ∧
    GapMirrorCalculus.bump g (GapMirrorCalculus.mirror g A) (GapMirrorCalculus.blowTime g A) = g / 2 :=
  ⟨GapMirrorCalculus.blowTime_pos g A hg hA, GapMirrorCalculus.blows_up g A hg hA,
    GapMirrorCalculus.mirror_time g A hg hA⟩

/-- The partner of an above-gap bump starts strictly between half the gap and the gap. -/
theorem mirror_between (g A : ℝ) (hg : 0 < g) (hA : g < A) :
    g / 2 < GapMirrorCalculus.mirror g A ∧ GapMirrorCalculus.mirror g A < g := by
  have hden : 0 < 2 * A - g := by linarith
  have hprod : 0 < g * (A - g) := mul_pos hg (sub_pos.mpr hA)
  unfold GapMirrorCalculus.mirror
  constructor
  · rw [lt_div_iff₀ hden]
    nlinarith [sq_pos_of_pos hg]
  · rw [div_lt_iff₀ hden]
    nlinarith

/-- A lower bump is regular and has strictly negative derivative at every real clock time. -/
theorem lower_regular (g B t : ℝ) (hg : 0 < g) (hB0 : 0 < B) (hB : B < g) :
    0 < GapMirrorCalculus.bump g B t ∧ GapMirrorCalculus.bump g B t < g ∧
    HasDerivAt (GapMirrorCalculus.bump g B)
      ((GapMirrorCalculus.bump g B t) ^ 2 - g * GapMirrorCalculus.bump g B t) t ∧
    (GapMirrorCalculus.bump g B t) ^ 2 - g * GapMirrorCalculus.bump g B t < 0 := by
  have hz : GapMirrorCalculus.z g B < 0 := by
    unfold GapMirrorCalculus.z
    have : 1 < g / B := (lt_div_iff₀ hB0).2 (by simpa using hB)
    linarith
  have hmul : GapMirrorCalculus.z g B * exp (g * t) < 0 :=
    mul_neg_of_neg_of_pos hz (exp_pos _)
  have hd : 1 < 1 - GapMirrorCalculus.z g B * exp (g * t) := by linarith
  have hd0 : 0 < 1 - GapMirrorCalculus.z g B * exp (g * t) := lt_trans zero_lt_one hd
  have hp : 0 < GapMirrorCalculus.bump g B t := div_pos hg hd0
  have hl : GapMirrorCalculus.bump g B t < g := by
    unfold GapMirrorCalculus.bump
    apply (div_lt_iff₀ hd0).2
    simpa using mul_lt_mul_of_pos_left hd hg
  refine ⟨hp, hl, GapMirrorCalculus.bump_solves g B t hd0.ne', ?_⟩
  have hfall := mul_lt_mul_of_pos_right hl hp
  nlinarith

/-- The upper blow-up time is not an endpoint of its mirror: the mirror is regular at all times,
has a negative derivative, and continues toward zero. -/
theorem mirror_continues (g A : ℝ) (hg : 0 < g) (hA : g < A) :
    (∀ t : ℝ, 0 < GapMirrorCalculus.bump g (GapMirrorCalculus.mirror g A) t ∧
      HasDerivAt (GapMirrorCalculus.bump g (GapMirrorCalculus.mirror g A))
        ((GapMirrorCalculus.bump g (GapMirrorCalculus.mirror g A) t) ^ 2 -
          g * GapMirrorCalculus.bump g (GapMirrorCalculus.mirror g A) t) t ∧
      (GapMirrorCalculus.bump g (GapMirrorCalculus.mirror g A) t) ^ 2 -
          g * GapMirrorCalculus.bump g (GapMirrorCalculus.mirror g A) t < 0) ∧
    Tendsto (GapMirrorCalculus.bump g (GapMirrorCalculus.mirror g A)) atTop (𝓝 0) := by
  have hm := mirror_between g A hg hA
  have hm0 : 0 < GapMirrorCalculus.mirror g A := by linarith [hm.1]
  refine ⟨?_, GapMirrorCalculus.fades g _ hg hm0 hm.2⟩
  intro t
  have h := lower_regular g _ t hg hm0 hm.2
  exact ⟨h.1, h.2.2.1, h.2.2.2⟩

/-- Crossing half the edge for a lower bump, with a positive logarithm argument when `0 < B < g`. -/
noncomputable def halfTime (g B : ℝ) : ℝ := log (B / (g - B)) / g

/-- Mathlib's total logarithm makes the two written formulas equal.
Outside `0 < g < A`, the name `blowTime` alone does not establish a blow-up. -/
theorem total_log_clock_identity (g B : ℝ) :
    GapMirrorCalculus.blowTime g B = halfTime g B := by
  unfold GapMirrorCalculus.blowTime halfTime
  have he : B - g = -(g - B) := by ring
  rw [he, div_neg, log_neg_eq_log]

theorem factor_at_halfTime (g B : ℝ) (hg : 0 < g) (hB0 : 0 < B) (hB : B < g) :
    exp (g * halfTime g B) = B / (g - B) :=
  clock_factor g _ hg.ne' (div_pos hB0 (sub_pos.mpr hB))

/-- At the lower bump's crossing time its value is exactly half the gap. -/
theorem half_time_reaches_half (g B : ℝ) (hg : 0 < g) (hB0 : 0 < B) (hB : B < g) :
    GapMirrorCalculus.bump g B (halfTime g B) = g / 2 := by
  have hden : 0 < g - B := sub_pos.mpr hB
  unfold GapMirrorCalculus.bump
  rw [factor_at_halfTime g B hg hB0 hB]
  unfold GapMirrorCalculus.z
  have he : 1 - (1 - g / B) * (B / (g - B)) = 2 := by
    field_simp
    ring
  rw [he]

theorem halfTime_pos_iff (g B : ℝ) (hg : 0 < g) (hB0 : 0 < B) (hB : B < g) :
    0 < halfTime g B ↔ g / 2 < B := by
  have hden : 0 < g - B := sub_pos.mpr hB
  have hratio : 0 < B / (g - B) := div_pos hB0 hden
  unfold halfTime
  rw [lt_div_iff₀ hg, zero_mul, log_pos_iff hratio.le, lt_div_iff₀ hden]
  constructor <;> intro h <;> linarith

theorem halfTime_neg_iff (g B : ℝ) (hg : 0 < g) (hB0 : 0 < B) (hB : B < g) :
    halfTime g B < 0 ↔ B < g / 2 := by
  have hden : 0 < g - B := sub_pos.mpr hB
  have hratio : 0 < B / (g - B) := div_pos hB0 hden
  unfold halfTime
  rw [div_lt_iff₀ hg, zero_mul, log_neg_iff hratio, div_lt_iff₀ hden]
  constructor <;> intro h <;> linarith

theorem halfTime_at_half (g : ℝ) (hg : 0 < g) : halfTime g (g / 2) = 0 := by
  have he : g / 2 / (g - g / 2) = 1 := by field_simp; ring
  simp [halfTime, he]

/-- The lower member of an above-gap mirror pair crosses half the edge at the upper blow-up time. -/
theorem halfTime_mirror (g A : ℝ) (hg : 0 < g) (hA : g < A) :
    halfTime g (GapMirrorCalculus.mirror g A) = GapMirrorCalculus.blowTime g A := by
  have hAg : 0 < A - g := sub_pos.mpr hA
  have h2 : 0 < 2 * A - g := by linarith
  have h2n : A * 2 - g ≠ 0 := by linarith
  have hdiff : g - GapMirrorCalculus.mirror g A = g * (A - g) / (2 * A - g) := by
    unfold GapMirrorCalculus.mirror
    field_simp [h2.ne', h2n, hg.ne']
    ring
  have hratio : GapMirrorCalculus.mirror g A / (g - GapMirrorCalculus.mirror g A) = A / (A - g) := by
    rw [hdiff]
    unfold GapMirrorCalculus.mirror
    field_simp [h2.ne', h2n, hAg.ne', hg.ne']
  simp only [halfTime, GapMirrorCalculus.blowTime, hratio]

end GapMirrorBridge

#print axioms GapMirrorBridge.cast_z
#print axioms GapMirrorBridge.cast_mirror
#print axioms GapMirrorBridge.cast_step
#print axioms GapMirrorBridge.denominator_factor
#print axioms GapMirrorBridge.real_step_at_time
#print axioms GapMirrorBridge.factor_at_blowTime
#print axioms GapMirrorBridge.before_iff
#print axioms GapMirrorBridge.same_motion_before_blowup
#print axioms GapMirrorBridge.rational_step_at_time
#print axioms GapMirrorBridge.clock_factor
#print axioms GapMirrorBridge.rational_step_at_clock
#print axioms GapMirrorBridge.real_step_solves_before
#print axioms GapMirrorBridge.both_in_future
#print axioms GapMirrorBridge.mirror_between
#print axioms GapMirrorBridge.lower_regular
#print axioms GapMirrorBridge.mirror_continues
#print axioms GapMirrorBridge.total_log_clock_identity
#print axioms GapMirrorBridge.factor_at_halfTime
#print axioms GapMirrorBridge.half_time_reaches_half
#print axioms GapMirrorBridge.halfTime_pos_iff
#print axioms GapMirrorBridge.halfTime_neg_iff
#print axioms GapMirrorBridge.halfTime_at_half
#print axioms GapMirrorBridge.halfTime_mirror
