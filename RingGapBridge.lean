import GapMirrorBridge
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases

/-!
# An exact algebraic map from even-ring patterns to gap mirrors

For a real pattern on a nonempty even ring, `size` is the sum of squares and `cost` is the
sum of squared differences around the ring, as in the repository's `Wirtinger.lean`.
`flip f j = (-1)^j.val * f j` is the alternating sign flip, including the closing edge.

The new observable `height g f = 2*g*size f / cost f` assigns a scalar bump height to a pattern.
On the domain `g > 0`, `size f > 0`, and `0 < cost f < 4*size f`, flipping the pattern gives
exactly `GapMirrorCalculus.mirror g (height g f)`. This is an algebraic map preserving the
reflection, not a claim that the ring's heat evolution obeys the scalar bump ODE.
The map discards amplitude: `height_scale` proves it is unchanged by nonzero rescaling.
Zero cost and maximal cost are excluded when interpreting the output as a finite positive pair.
The six-point example at the end verifies the difference in evolution: the ring heat step only
rescales that pattern, leaving its assigned height at `2*g`, where the bump's growth rate is positive.
-/

open Finset

namespace RingGapBridge

variable {n : ℕ} [NeZero n]

noncomputable def size (f : ZMod n → ℝ) : ℝ := ∑ j, f j ^ 2

noncomputable def cost (f : ZMod n → ℝ) : ℝ := ∑ j, (f (j + 1) - f j) ^ 2

noncomputable def flip (f : ZMod n → ℝ) (j : ZMod n) : ℝ := (-1) ^ j.val * f j

noncomputable def normalizedCost (f : ZMod n → ℝ) : ℝ := cost f / (2 * size f)

/-- A ring observable whose reflection identity is proved below. -/
noncomputable def height (g : ℝ) (f : ZMod n → ℝ) : ℝ := 2 * g * size f / cost f

theorem sign_sq (k : ℕ) : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

omit [NeZero n] in
theorem sign_mod (hn : Even n) (k : ℕ) : (-1 : ℝ) ^ (k % n) = (-1 : ℝ) ^ k := by
  calc
    (-1 : ℝ) ^ (k % n) = (-1 : ℝ) ^ (k % n + n * (k / n)) := by
      rw [pow_add, pow_mul, hn.neg_one_pow, one_pow, mul_one]
    _ = (-1 : ℝ) ^ k := by rw [Nat.mod_add_div]

theorem sign_next (hn : Even n) (j : ZMod n) :
    (-1 : ℝ) ^ (j + 1).val = -((-1 : ℝ) ^ j.val) := by
  have hn2 : 1 < n := by
    rcases hn with ⟨k, hk⟩
    have hne := NeZero.ne n
    omega
  let : Fact (1 < n) := ⟨hn2⟩
  rw [ZMod.val_add, ZMod.val_one, sign_mod hn, pow_succ]
  ring

omit [NeZero n] in
theorem flip_flip (f : ZMod n → ℝ) : flip (flip f) = f := by
  funext j
  change (-1 : ℝ) ^ j.val * ((-1 : ℝ) ^ j.val * f j) = f j
  rw [← mul_assoc, ← pow_two, sign_sq, one_mul]

theorem size_flip (f : ZMod n → ℝ) : size (flip f) = size f := by
  unfold size flip
  simp only [mul_pow, sign_sq, one_mul]

theorem flipped_edge (hn : Even n) (f : ZMod n → ℝ) (j : ZMod n) :
    (flip f (j + 1) - flip f j) ^ 2 = (f (j + 1) + f j) ^ 2 := by
  unfold flip
  rw [sign_next hn]
  calc
    (-((-1 : ℝ) ^ j.val) * f (j + 1) - (-1 : ℝ) ^ j.val * f j) ^ 2 =
        ((-1 : ℝ) ^ j.val) ^ 2 * (f (j + 1) + f j) ^ 2 := by ring
    _ = (f (j + 1) + f j) ^ 2 := by rw [sign_sq, one_mul]

theorem sum_shift (f : ZMod n → ℝ) : ∑ j, f (j + 1) ^ 2 = size f := by
  exact Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)

/-- The complement identity includes the wraparound edge; evenness is essential there. -/
theorem cost_pair (hn : Even n) (f : ZMod n → ℝ) :
    cost f + cost (flip f) = 4 * size f := by
  have hedge (j : ZMod n) :
      (f (j + 1) - f j) ^ 2 + (flip f (j + 1) - flip f j) ^ 2 =
        2 * f (j + 1) ^ 2 + 2 * f j ^ 2 := by
    rw [flipped_edge hn]
    ring
  calc
    cost f + cost (flip f) =
        ∑ j, ((f (j + 1) - f j) ^ 2 + (flip f (j + 1) - flip f j) ^ 2) := by
      rw [sum_add_distrib]
      rfl
    _ = ∑ j, (2 * f (j + 1) ^ 2 + 2 * f j ^ 2) := by
      apply sum_congr rfl
      intro j _
      exact hedge j
    _ = 4 * size f := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_shift]
      change 2 * size f + 2 * size f = 4 * size f
      ring

theorem cost_flip (hn : Even n) (f : ZMod n → ℝ) :
    cost (flip f) = 4 * size f - cost f := by
  linarith [cost_pair hn f]

theorem normalized_pair (hn : Even n) (f : ZMod n → ℝ) (hN : size f ≠ 0) :
    normalizedCost f + normalizedCost (flip f) = 2 := by
  unfold normalizedCost
  rw [size_flip, ← add_div, cost_pair hn]
  field_simp
  ring

theorem gap_over_height (g : ℝ) (f : ZMod n → ℝ)
    (hg : g ≠ 0) (hN : size f ≠ 0) :
    g / height g f = normalizedCost f := by
  unfold height normalizedCost
  field_simp

theorem z_height (g : ℝ) (f : ZMod n → ℝ)
    (hg : g ≠ 0) (hN : size f ≠ 0) :
    GapMirrorCalculus.z g (height g f) = 1 - normalizedCost f := by
  unfold GapMirrorCalculus.z
  rw [gap_over_height g f hg hN]

/-- Exact sign reversal in the scalar mirror coordinate. -/
theorem z_flip (hn : Even n) (g : ℝ) (f : ZMod n → ℝ)
    (hg : g ≠ 0) (hN : size f ≠ 0) :
    GapMirrorCalculus.z g (height g (flip f)) =
      -GapMirrorCalculus.z g (height g f) := by
  rw [z_height g f hg hN, z_height g (flip f) hg (by simpa [size_flip] using hN)]
  linarith [normalized_pair hn f hN]

/-- The actual connection: assigning a height after a ring flip equals mirroring the height. -/
theorem height_flip (hn : Even n) (g : ℝ) (f : ZMod n → ℝ)
    (hg : 0 < g) (hN : 0 < size f) (hE : 0 < cost f) (hEmax : cost f < 4 * size f) :
    height g (flip f) = GapMirrorCalculus.mirror g (height g f) := by
  have hrem : 0 < 4 * size f - cost f := sub_pos.mpr hEmax
  unfold height GapMirrorCalculus.mirror
  rw [size_flip, cost_flip hn]
  field_simp
  ring

theorem height_pos (g : ℝ) (f : ZMod n → ℝ)
    (hg : 0 < g) (hN : 0 < size f) (hE : 0 < cost f) :
    0 < height g f := by
  exact div_pos (mul_pos (mul_pos (by norm_num) hg) hN) hE

/-- Below the middle ring cost corresponds to an above-gap bump. -/
theorem height_above_gap_iff (g : ℝ) (f : ZMod n → ℝ)
    (hg : 0 < g) (hE : 0 < cost f) :
    g < height g f ↔ cost f < 2 * size f := by
  unfold height
  rw [lt_div_iff₀ hE]
  constructor <;> intro h <;> nlinarith

theorem size_scale (c : ℝ) (f : ZMod n → ℝ) :
    size (fun j => c * f j) = c ^ 2 * size f := by
  simp only [size, mul_pow, mul_sum]

theorem cost_scale (c : ℝ) (f : ZMod n → ℝ) :
    cost (fun j => c * f j) = c ^ 2 * cost f := by
  simp only [cost, ← mul_sub, mul_pow, mul_sum]

/-- This observable forgets amplitude, so preservation of reflection alone does not identify motion. -/
theorem height_scale (g c : ℝ) (f : ZMod n → ℝ) (hc : c ≠ 0) :
    height g (fun j => c * f j) = height g f := by
  unfold height
  rw [size_scale, cost_scale]
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero _ hc
  calc
    2 * g * (c ^ 2 * size f) / (c ^ 2 * cost f) =
        c ^ 2 * (2 * g * size f) / (c ^ 2 * cost f) := by ring
    _ = 2 * g * size f / cost f := mul_div_mul_left _ _ hc2

/-- A concrete mean-zero wave: `(1, 1/2, -1/2, -1, -1/2, 1/2)`. -/
noncomputable def sixWave (j : ZMod 6) : ℝ :=
  if j.val = 0 then 1 else if j.val = 1 then 1 / 2 else if j.val = 2 then -(1 / 2)
  else if j.val = 3 then -1 else if j.val = 4 then -(1 / 2) else 1 / 2

theorem six_wave_sums : size sixWave = 3 ∧ cost sixWave = 3 ∧ ∑ j, sixWave j = 0 := by
  have hsum (f : ZMod 6 → ℝ) :
      ∑ j, f j = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
    change (Fin 6 → ℝ) at f
    change (∑ j : Fin 6, f j) = f (0 : Fin 6) + f 1 + f 2 + f 3 + f 4 + f 5
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change f (0 : Fin 6) + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5
    ring
  unfold size cost
  rw [hsum, hsum, hsum]
  change
    (1 : ℝ) ^ 2 + (1 / 2) ^ 2 + (-(1 / 2)) ^ 2 + (-1) ^ 2 + (-(1 / 2)) ^ 2 +
      (1 / 2) ^ 2 = 3 ∧
    ((1 / 2 : ℝ) - 1) ^ 2 + (-(1 / 2) - 1 / 2) ^ 2 + (-1 - -(1 / 2)) ^ 2 +
      (-(1 / 2) - -1) ^ 2 + (1 / 2 - -(1 / 2)) ^ 2 + (1 - 1 / 2) ^ 2 = 3 ∧
    (1 : ℝ) + 1 / 2 + -(1 / 2) + -1 + -(1 / 2) + 1 / 2 = 0
  norm_num

theorem six_wave_laplacian (j : ZMod 6) :
    sixWave (j + 1) - 2 * sixWave j + sixWave (j - 1) = -sixWave j := by
  fin_cases j
  · change (1 / 2 : ℝ) - 2 * 1 + 1 / 2 = -1
    norm_num
  · change (-(1 / 2) : ℝ) - 2 * (1 / 2) + 1 = -(1 / 2)
    norm_num
  · change (-1 : ℝ) - 2 * (-(1 / 2)) + 1 / 2 = -(-(1 / 2))
    norm_num
  · change (-(1 / 2) : ℝ) - 2 * (-1) + -(1 / 2) = -(-1)
    norm_num
  · change (1 / 2 : ℝ) - 2 * (-(1 / 2)) + -1 = -(-(1 / 2))
    norm_num
  · change (1 : ℝ) - 2 * (1 / 2) + -(1 / 2) = -(1 / 2)
    norm_num

theorem six_wave_height (g : ℝ) : height g sixWave = 2 * g := by
  unfold height
  rw [six_wave_sums.1, six_wave_sums.2.1]
  ring

/-- The update here is exactly the defining formula of `RingDecay.heatStep`.
For example, every step size in the repository's range `0 ≤ t ≤ 1/4` satisfies `t ≠ 1`. -/
theorem six_wave_heat_height (g t : ℝ) (ht : t ≠ 1) :
    height g (fun j => sixWave j + t *
      (sixWave (j + 1) - 2 * sixWave j + sixWave (j - 1))) = 2 * g := by
  have hfun : (fun j => sixWave j + t *
      (sixWave (j + 1) - 2 * sixWave j + sixWave (j - 1))) =
      (fun j => (1 - t) * sixWave j) := by
    funext j
    rw [six_wave_laplacian]
    ring
  rw [hfun, height_scale g (1 - t) sixWave (by exact sub_ne_zero.mpr (Ne.symm ht)),
    six_wave_height]

/-- The mapped ring height is constant under those heat steps, while the bump rule wants growth. -/
theorem six_wave_gap_rate (g : ℝ) (hg : 0 < g) :
    (height g sixWave) ^ 2 - g * height g sixWave = 2 * g ^ 2 ∧
      0 < (height g sixWave) ^ 2 - g * height g sixWave := by
  rw [six_wave_height]
  constructor
  · ring
  · nlinarith [sq_pos_of_pos hg]

end RingGapBridge

#print axioms RingGapBridge.sign_sq
#print axioms RingGapBridge.sign_mod
#print axioms RingGapBridge.sign_next
#print axioms RingGapBridge.flip_flip
#print axioms RingGapBridge.size_flip
#print axioms RingGapBridge.flipped_edge
#print axioms RingGapBridge.sum_shift
#print axioms RingGapBridge.cost_pair
#print axioms RingGapBridge.cost_flip
#print axioms RingGapBridge.normalized_pair
#print axioms RingGapBridge.gap_over_height
#print axioms RingGapBridge.z_height
#print axioms RingGapBridge.z_flip
#print axioms RingGapBridge.height_flip
#print axioms RingGapBridge.height_pos
#print axioms RingGapBridge.height_above_gap_iff
#print axioms RingGapBridge.size_scale
#print axioms RingGapBridge.cost_scale
#print axioms RingGapBridge.height_scale
#print axioms RingGapBridge.six_wave_sums
#print axioms RingGapBridge.six_wave_laplacian
#print axioms RingGapBridge.six_wave_height
#print axioms RingGapBridge.six_wave_heat_height
#print axioms RingGapBridge.six_wave_gap_rate
