import Wirtinger
import TwoWaveGapBridge
import Gap

/-!
# Ring spreading inside the store bound

For a nonempty ring, continuous heat preserves the sum. A path whose initial sum is
zero has squared size bounded by `HugGap.breathe` with no input and release rate
`2 * (2 - 2 * cos (2π/n))`. The factor two comes from differentiating squared size.

For `n ≥ 3`, the first cosine wave is a mean-zero heat solution and attains equality.
Every larger release rate gives a smaller proposed bound at every positive time,
so that rate cannot hold for all such paths.

Original idea and wording, dictation and direction: NousVolition.
Claude first connected the idea's shape and wording to a recognizable mathematical
name, then supplied the proof plan and sharpness test.
Lean code generated and checked by Codex.
-/

open Finset Real Set

namespace WirtingerStore

/-- A differentiable quantity with `E' ≤ -r E` stays below the store with no input.
The hypotheses are required only at nonnegative times. -/
theorem lets_go_at_least_as_fast (E E' : ℝ → ℝ) (r : ℝ)
    (hE : ∀ t, 0 ≤ t → HasDerivAt E (E' t) t)
    (hdecay : ∀ t, 0 ≤ t → E' t ≤ -r * E t)
    (t : ℝ) (ht : 0 ≤ t) : E t ≤ HugGap.breathe r 0 (E 0) t := by
  let F : ℝ → ℝ := fun s => E s * exp (r * s)
  have hF (s : ℝ) (hs : 0 ≤ s) :
      HasDerivAt F ((E' s + r * E s) * exp (r * s)) s := by
    have h := (hE s hs).mul (((hasDerivAt_id s).const_mul r).exp)
    simp only [id_eq, mul_one] at h
    convert h using 1 <;> first | rfl | ring
  have hanti : AntitoneOn F (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro s hs
      exact (hF s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hF s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs0 : 0 ≤ s := interior_subset hs
      rw [(hF s hs0).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hdecay s hs0]) (exp_pos _).le
  have hbound : F t ≤ F 0 := hanti (by simp) ht ht
  have hmul := mul_le_mul_of_nonneg_right hbound (exp_pos (-r * t)).le
  have he : exp (r * t) * exp (-r * t) = 1 := by
    rw [← exp_add, show r * t + -r * t = 0 by ring, exp_zero]
  rw [HugGap.input_ended]
  simpa only [F, mul_assoc, he, mul_zero, exp_zero, mul_one, one_mul] using hmul

section Ring

variable {n : ℕ} [NeZero n]

/-- The two neighbor shifts permute the ring, so spreading has zero total rate. -/
theorem sum_heatGenerator (g : ZMod n → ℝ) :
    ∑ j, TwoWaveGapBridge.heatGenerator g j = 0 := by
  have hnext : (∑ j, g (j + 1)) = ∑ j, g j :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  have hprev : (∑ j, g (j - 1)) = ∑ j, g j :=
    Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun _ => rfl)
  simp only [TwoWaveGapBridge.heatGenerator, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [hnext, hprev]
  ring

theorem sum_hasDerivAt_zero (f : ℝ → ZMod n → ℝ)
    (hf : ∀ j t, HasDerivAt (fun s => f s j)
      (TwoWaveGapBridge.heatGenerator (f t) j) t) (t : ℝ) :
    HasDerivAt (fun s => ∑ j, f s j) 0 t := by
  have h := HasDerivAt.fun_sum (u := (univ : Finset (ZMod n))) (fun j _ => hf j t)
  simpa only [sum_heatGenerator] using h

/-- The total at every time is the initial total, including for negative times. -/
theorem sum_preserved (f : ℝ → ZMod n → ℝ)
    (hf : ∀ j t, HasDerivAt (fun s => f s j)
      (TwoWaveGapBridge.heatGenerator (f t) j) t) (t : ℝ) :
    ∑ j, f t j = ∑ j, f 0 j := by
  exact is_const_of_deriv_eq_zero (fun s => (sum_hasDerivAt_zero f hf s).differentiableAt)
    (fun s => (sum_hasDerivAt_zero f hf s).deriv) t 0

theorem mean_zero_preserved (f : ℝ → ZMod n → ℝ)
    (hf : ∀ j t, HasDerivAt (fun s => f s j)
      (TwoWaveGapBridge.heatGenerator (f t) j) t)
    (hzero : ∑ j, f 0 j = 0) (t : ℝ) : ∑ j, f t j = 0 := by
  rw [sum_preserved f hf t, hzero]

/-- Differentiating the sum of squares produces twice the dot product. -/
theorem size_hasDerivAt_dot (f : ℝ → ZMod n → ℝ)
    (hf : ∀ j t, HasDerivAt (fun s => f s j)
      (TwoWaveGapBridge.heatGenerator (f t) j) t) (t : ℝ) :
    HasDerivAt (fun s => RingGapBridge.size (f s))
      (2 * TwoWaveGapBridge.dot (f t) (TwoWaveGapBridge.heatGenerator (f t))) t := by
  have h : HasDerivAt (fun s => ∑ j, (f s j)^2)
      (∑ j, 2 * f t j * TwoWaveGapBridge.heatGenerator (f t) j) t := by
    apply HasDerivAt.fun_sum
    intro j _
    convert (hf j t).mul (hf j t) using 1 <;>
      first | rfl | (funext s; change f s j ^ 2 = f s j * f s j; ring) | ring
  simpa only [RingGapBridge.size, TwoWaveGapBridge.dot, mul_sum, mul_assoc] using h

/-- Integration by parts changes that dot product into minus the edge cost. -/
theorem size_hasDerivAt_cost (f : ℝ → ZMod n → ℝ)
    (hf : ∀ j t, HasDerivAt (fun s => f s j)
      (TwoWaveGapBridge.heatGenerator (f t) j) t) (t : ℝ) :
    HasDerivAt (fun s => RingGapBridge.size (f s)) (-2 * RingGapBridge.cost (f t)) t := by
  have he : 2 * TwoWaveGapBridge.dot (f t) (TwoWaveGapBridge.heatGenerator (f t)) =
      -2 * RingGapBridge.cost (f t) := by
    rw [TwoWaveGapBridge.cost_eq_neg_dot_heat]
    ring
  rw [← he]
  exact size_hasDerivAt_dot f hf t

theorem size_rate_le (f : ℝ → ZMod n → ℝ)
    (hf : ∀ j t, HasDerivAt (fun s => f s j)
      (TwoWaveGapBridge.heatGenerator (f t) j) t)
    (hzero : ∑ j, f 0 j = 0) (t : ℝ) :
    -2 * RingGapBridge.cost (f t) ≤
      -(2 * (2 - 2 * cos (2 * π / n))) * RingGapBridge.size (f t) := by
  have hw := CycleWirtinger.wirtinger (f t) (mean_zero_preserved f hf hzero t)
  change (2 - 2 * cos (2 * π / n)) * RingGapBridge.size (f t) ≤
    RingGapBridge.cost (f t) at hw
  nlinarith

/-- Wirtinger puts mean-zero ring spreading inside the no-input store bound. -/
theorem ring_spreading_le_store (f : ℝ → ZMod n → ℝ)
    (hf : ∀ j t, HasDerivAt (fun s => f s j)
      (TwoWaveGapBridge.heatGenerator (f t) j) t)
    (hzero : ∑ j, f 0 j = 0) (t : ℝ) (ht : 0 ≤ t) :
    RingGapBridge.size (f t) ≤
      HugGap.breathe (2 * (2 - 2 * cos (2 * π / n))) 0 (RingGapBridge.size (f 0)) t := by
  exact lets_go_at_least_as_fast (fun s => RingGapBridge.size (f s))
    (fun s => -2 * RingGapBridge.cost (f s)) (2 * (2 - 2 * cos (2 * π / n)))
    (fun s _ => size_hasDerivAt_cost f hf s) (fun s _ => size_rate_le f hf hzero s) t ht

/-! ## The slowest wave attains the bound -/

noncomputable def slowWave (j : ZMod n) : ℝ := cos (2 * π * j.val / n)

noncomputable def slowPath (t : ℝ) (j : ZMod n) : ℝ :=
  exp (-(2 - 2 * cos (2 * π / n)) * t) * slowWave j

theorem slowWave_mean_and_cost (hn : 3 ≤ n) :
    (∑ j : ZMod n, slowWave j) = 0 ∧
    RingGapBridge.cost (slowWave (n := n)) =
      (2 - 2 * cos (2 * π / n)) * RingGapBridge.size (slowWave (n := n)) := by
  exact CycleWirtinger.wirtinger_sharp hn

theorem slowWave_size_pos : 0 < RingGapBridge.size (slowWave (n := n)) := by
  have h0 : slowWave (0 : ZMod n) = 1 := by simp [slowWave]
  have h : (slowWave (0 : ZMod n))^2 ≤ RingGapBridge.size (slowWave (n := n)) :=
    single_le_sum (fun j _ => sq_nonneg (slowWave j)) (mem_univ 0)
  rw [h0] at h
  norm_num at h
  linarith

/-- Character addition includes the wraparound edges of the cosine wave. -/
theorem slowWave_eigen (hn : 3 ≤ n) (j : ZMod n) :
    TwoWaveGapBridge.heatGenerator slowWave j =
      -(2 - 2 * cos (2 * π / n)) * slowWave j := by
  have : Fact (1 < n) := ⟨by omega⟩
  have hre (k : ZMod n) : slowWave k = (ZMod.stdAddChar k).re := by
    rw [CycleWirtinger.e_eq_exp, Complex.exp_ofReal_mul_I_re]
    rfl
  have h1 : (ZMod.stdAddChar (1 : ZMod n)).re = cos (2 * π / n) := by
    rw [CycleWirtinger.e_eq_exp, Complex.exp_ofReal_mul_I_re, ZMod.val_one]
    simp
  unfold TwoWaveGapBridge.heatGenerator
  rw [hre (j + 1), hre j, hre (j - 1), show j - 1 = j + (-1) by ring,
    AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, ← CycleWirtinger.conj_e]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  rw [← h1]
  ring

omit [NeZero n] in
theorem heat_scale (c : ℝ) (v : ZMod n → ℝ) (j : ZMod n) :
    TwoWaveGapBridge.heatGenerator (fun k => c * v k) j =
      c * TwoWaveGapBridge.heatGenerator v j := by
  unfold TwoWaveGapBridge.heatGenerator
  ring

omit [NeZero n] in
theorem slowPath_zero : slowPath (n := n) 0 = slowWave := by
  funext j
  simp [slowPath]

theorem slowPath_spreads (hn : 3 ≤ n) (j : ZMod n) (t : ℝ) :
    HasDerivAt (fun s => slowPath s j)
      (TwoWaveGapBridge.heatGenerator (slowPath t) j) t := by
  have h := (TwoWaveGapBridge.coefficient_deriv (2 - 2 * cos (2 * π / n)) 1 t).mul_const
    (slowWave j)
  change HasDerivAt (fun s => slowPath s j)
    (TwoWaveGapBridge.heatGenerator
      (fun k => exp (-(2 - 2 * cos (2 * π / n)) * t) * slowWave k) j) t
  rw [heat_scale, slowWave_eigen hn]
  simpa only [slowPath, TwoWaveGapBridge.coefficient, one_mul, mul_assoc, mul_left_comm, mul_comm]
    using h

theorem slowPath_mean_zero (hn : 3 ≤ n) (t : ℝ) : ∑ j : ZMod n, slowPath t j = 0 := by
  simp only [slowPath, ← mul_sum, (slowWave_mean_and_cost hn).1, mul_zero]

/-- The first cosine wave attains equality with the store at rate twice the gap. -/
theorem slowPath_attains_bound (t : ℝ) :
    RingGapBridge.size (slowPath (n := n) t) =
      HugGap.breathe (2 * (2 - 2 * cos (2 * π / n))) 0
        (RingGapBridge.size (slowPath (n := n) 0)) t := by
  have he : (exp (-(2 - 2 * cos (2 * π / n)) * t))^2 =
      exp (-(2 * (2 - 2 * cos (2 * π / n))) * t) := by
    rw [pow_two, ← exp_add]
    congr 1
    ring
  rw [HugGap.input_ended, slowPath_zero]
  change RingGapBridge.size (fun j : ZMod n =>
    exp (-(2 - 2 * cos (2 * π / n)) * t) * slowWave j) = _
  rw [RingGapBridge.size_scale, he]
  ring

/-- Raising the rate makes the proposed bound smaller than this wave at every positive time. -/
theorem faster_rate_fails (r t : ℝ)
    (hr : 2 * (2 - 2 * cos (2 * π / n)) < r) (ht : 0 < t) :
    HugGap.breathe r 0 (RingGapBridge.size (slowPath (n := n) 0)) t <
      RingGapBridge.size (slowPath (n := n) t) := by
  rw [slowPath_attains_bound t, HugGap.input_ended, HugGap.input_ended, slowPath_zero]
  apply mul_lt_mul_of_pos_left _ slowWave_size_pos
  rw [exp_lt_exp]
  nlinarith

/-- The counterexample has every premise of the main theorem and violates any faster rate. -/
theorem sharp_counterexample (hn : 3 ≤ n) (r : ℝ)
    (hr : 2 * (2 - 2 * cos (2 * π / n)) < r) :
    (∀ (j : ZMod n) (t : ℝ), HasDerivAt (fun s => slowPath s j)
      (TwoWaveGapBridge.heatGenerator (slowPath t) j) t) ∧
    (∑ j : ZMod n, slowPath 0 j) = 0 ∧
    ∀ t : ℝ, 0 < t → HugGap.breathe r 0 (RingGapBridge.size (slowPath (n := n) 0)) t <
      RingGapBridge.size (slowPath (n := n) t) := by
  exact ⟨slowPath_spreads hn, slowPath_mean_zero hn 0, fun t ht => faster_rate_fails r t hr ht⟩

end Ring

end WirtingerStore

#print axioms WirtingerStore.lets_go_at_least_as_fast
#print axioms WirtingerStore.sum_heatGenerator
#print axioms WirtingerStore.sum_hasDerivAt_zero
#print axioms WirtingerStore.sum_preserved
#print axioms WirtingerStore.mean_zero_preserved
#print axioms WirtingerStore.size_hasDerivAt_dot
#print axioms WirtingerStore.size_hasDerivAt_cost
#print axioms WirtingerStore.size_rate_le
#print axioms WirtingerStore.ring_spreading_le_store
#print axioms WirtingerStore.slowWave_mean_and_cost
#print axioms WirtingerStore.slowWave_size_pos
#print axioms WirtingerStore.slowWave_eigen
#print axioms WirtingerStore.heat_scale
#print axioms WirtingerStore.slowPath_zero
#print axioms WirtingerStore.slowPath_spreads
#print axioms WirtingerStore.slowPath_mean_zero
#print axioms WirtingerStore.slowPath_attains_bound
#print axioms WirtingerStore.faster_rate_fails
#print axioms WirtingerStore.sharp_counterexample
