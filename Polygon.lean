import Wirtinger

/-!
# The isoperimetric inequality for polygons, by finite Fourier series

A closed polygon with `n ≥ 3` vertices is a map `z : ZMod n → ℂ`. Two quantities:

* `area2 z = ∑ⱼ Im (conj (z j) · z (j+1))`, twice the signed area
  (positive for counter-clockwise polygons);
* `sides z = ∑ⱼ |z (j+1) − z j|²`, the sum of the squared side lengths.

**Theorem (`polygon_isoperimetric`).** `2 tan (π/n) · area2 z ≤ sides z`.
Equivalently, `4 tan (π/n) · area ≤ ∑ side²`.

**Sharpness (`polygon_sharp`).** The regular polygon `z j = exp (2π i j / n)` gives equality.

The proof is Hurwitz's Fourier proof of the isoperimetric inequality (1901), in discrete form.
It uses the same finite Fourier transform as the discrete Wirtinger inequality (`Wirtinger.lean`):

* Plancherel (`plancherel`) turns both sides into sums over frequencies `k`:
  - `n · area2 = ∑ₖ Im e(−k) · |Ẑ k|²`;
  - `n · sides = ∑ₖ |e(−k) − 1|² · |Ẑ k|²`.
* Each frequency is then compared separately. The bound
  `tan (π/n) · sin (2π m/n) ≤ 1 − cos (2π m/n)` (`tan_bound`) says every `n`-th root of unity
  lies on the inner side of the line through `1` and `e(1)`: the regular polygon is convex.
-/

open Finset ComplexConjugate CycleWirtinger
open scoped Real

namespace PolygonIso

variable {n : ℕ} [NeZero n]

/-! ## Complex Fourier coefficients -/

/-- Fourier coefficients of a complex function on `ZMod n`. -/
noncomputable def cfourier (z : ZMod n → ℂ) (k : ZMod n) : ℂ :=
  ∑ j, z j * ZMod.stdAddChar (j * k)

/-- Plancherel: `∑ₖ conj (Ẑ k) · Ŵ k = n · ∑ⱼ conj (z j) · w j`. -/
lemma plancherel (z w : ZMod n → ℂ) :
    ∑ k, conj (cfourier z k) * cfourier w k = (n : ℂ) * ∑ j, conj (z j) * w j := by
  have h1 : ∀ k, conj (cfourier z k) * cfourier w k
      = ∑ j, ∑ l, conj (z j) * w l * ZMod.stdAddChar (k * (l - j)) := by
    intro k
    simp only [cfourier, map_sum, map_mul, conj_e, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [show k * (l - j) = -(j * k) + l * k by ring, AddChar.map_add_eq_mul]
    ring
  have h2 : ∀ j l : ZMod n, ∑ k, conj (z j) * w l * ZMod.stdAddChar (k * (l - j))
      = if l = j then (n : ℂ) * (conj (z j) * w j) else 0 := by
    intro j l
    rw [← Finset.mul_sum, ortho]
    simp only [sub_eq_zero]
    split_ifs with h
    · subst h
      ring
    · ring
  calc ∑ k, conj (cfourier z k) * cfourier w k
      = ∑ k, ∑ j, ∑ l, conj (z j) * w l * ZMod.stdAddChar (k * (l - j)) :=
        Finset.sum_congr rfl (fun k _ => h1 k)
    _ = ∑ j, ∑ l, ∑ k, conj (z j) * w l * ZMod.stdAddChar (k * (l - j)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
    _ = ∑ j, ∑ l, (if l = j then (n : ℂ) * (conj (z j) * w j) else 0) := by
        simp only [h2]
    _ = ∑ j, (n : ℂ) * (conj (z j) * w j) := by
        simp
    _ = (n : ℂ) * ∑ j, conj (z j) * w j := by
        rw [Finset.mul_sum]

/-- Shifting `j ↦ j + 1` multiplies the `k`-th coefficient by `e(−k)`. -/
lemma cfourier_shift (z : ZMod n → ℂ) (k : ZMod n) :
    cfourier (fun j => z (j + 1)) k = ZMod.stdAddChar (-k) * cfourier z k := by
  simp only [cfourier]
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun j => by
    simp only [Equiv.coe_addRight]
    rw [show j * k = (j + 1) * k + -k by ring, AddChar.map_add_eq_mul]
    ring)

/-- The side vectors `z (j+1) − z j` multiply the `k`-th coefficient by `e(−k) − 1`. -/
lemma cfourier_step (z : ZMod n → ℂ) (k : ZMod n) :
    cfourier (fun j => z (j + 1) - z j) k = (ZMod.stdAddChar (-k) - 1) * cfourier z k := by
  have hsplit : cfourier (fun j => z (j + 1) - z j) k
      = cfourier (fun j => z (j + 1)) k - cfourier z k := by
    simp only [cfourier, sub_mul, Finset.sum_sub_distrib]
  rw [hsplit, cfourier_shift]
  ring

/-! ## The character -/

/-- `Im e(m) = sin (2π m / n)`. -/
lemma e_im (m : ZMod n) : (ZMod.stdAddChar m).im = Real.sin (2 * π * m.val / n) := by
  rw [e_eq_exp, Complex.exp_ofReal_mul_I_im]

lemma normSq_e (m : ZMod n) : Complex.normSq (ZMod.stdAddChar m) = 1 := by
  rw [ZMod.stdAddChar_apply, Circle.normSq_coe]

/-- **Convexity of the regular polygon.** For `n ≥ 3` and every `m`,
`tan (π/n) · sin (2π m/n) ≤ 1 − cos (2π m/n)`. Equality holds at `m = 0` and `m = 1`. -/
lemma tan_bound (hn : 3 ≤ n) (m : ZMod n) :
    Real.tan (π / n) * Real.sin (2 * π * m.val / n) ≤ 1 - Real.cos (2 * π * m.val / n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hmn : (m.val : ℝ) < n := by exact_mod_cast ZMod.val_lt m
  have hb0 : 0 < π / n := by positivity
  have hb : π / n < π / 2 := by
    rw [div_lt_div_iff₀ hnpos two_pos]
    nlinarith [Real.pi_pos]
  have hcb : 0 < Real.cos (π / n) := Real.cos_pos_of_mem_Ioo ⟨by linarith, hb⟩
  have harg : 2 * π * m.val / n = 2 * (π * m.val / n) := by ring
  rw [harg, Real.tan_eq_sin_div_cos, div_mul_eq_mul_div, div_le_iff₀ hcb]
  have hθ0 : 0 ≤ π * m.val / n := by positivity
  have hθπ : π * m.val / n ≤ π := by
    rw [div_le_iff₀ hnpos]
    nlinarith [Real.pi_pos]
  have hs : 0 ≤ Real.sin (π * m.val / n) := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθπ
  have hprod : 0 ≤ Real.sin (π * m.val / n) * Real.sin (π * m.val / n - π / n) := by
    rcases Nat.eq_zero_or_pos m.val with h0 | hpos
    · simp [h0]
    · apply mul_nonneg hs
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · have h1 : (1 : ℝ) ≤ m.val := by exact_mod_cast hpos
        rw [sub_nonneg, div_le_div_iff_of_pos_right hnpos]
        nlinarith [Real.pi_pos]
      · linarith
  rw [Real.sin_sub] at hprod
  have hpy := Real.sin_sq_add_cos_sq (π * m.val / n)
  rw [Real.sin_two_mul, Real.cos_two_mul]
  have key : (1 - (2 * Real.cos (π * m.val / n) ^ 2 - 1)) * Real.cos (π / n)
      - Real.sin (π / n) * (2 * Real.sin (π * m.val / n) * Real.cos (π * m.val / n))
      = 2 * (Real.sin (π * m.val / n) * (Real.sin (π * m.val / n) * Real.cos (π / n)
          - Real.cos (π * m.val / n) * Real.sin (π / n))) := by
    linear_combination (-2 * Real.cos (π / n)) * hpy
  nlinarith [key, hprod]

/-! ## The inequality -/

/-- Twice the signed area of the closed polygon `z 0, z 1, …, z (n−1)`. -/
noncomputable def area2 (z : ZMod n → ℂ) : ℝ := ∑ j, (conj (z j) * z (j + 1)).im

/-- Sum of the squared side lengths. -/
noncomputable def sides (z : ZMod n → ℂ) : ℝ := ∑ j, Complex.normSq (z (j + 1) - z j)

/-- The area in frequencies: `n · area2 z = ∑ₖ Im e(−k) · |Ẑ k|²`. -/
lemma area2_fourier (z : ZMod n → ℂ) :
    (n : ℝ) * area2 z = ∑ k, (ZMod.stdAddChar (-k)).im * Complex.normSq (cfourier z k) := by
  have h := plancherel z (fun j => z (j + 1))
  simp only [cfourier_shift] at h
  have h' : ∑ k, conj (cfourier z k) * (ZMod.stdAddChar (-k) * cfourier z k)
      = ∑ k, ZMod.stdAddChar (-k) * (Complex.normSq (cfourier z k) : ℂ) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [h'] at h
  have hk : ∀ (a : ℂ) (r : ℝ), (a * (r : ℂ)).im = a.im * r := by
    intro a r
    simp [Complex.mul_im]
  have hn' : ∀ Q : ℂ, ((n : ℂ) * Q).im = n * Q.im := by
    intro Q
    simp [Complex.mul_im]
  have him := congrArg Complex.im h
  rw [Complex.im_sum, hn', Complex.im_sum] at him
  simp only [hk] at him
  rw [area2]
  exact him.symm

/-- The sides in frequencies: `n · sides z = ∑ₖ |e(−k) − 1|² · |Ẑ k|²`. -/
lemma sides_fourier (z : ZMod n → ℂ) :
    (n : ℝ) * sides z
      = ∑ k, Complex.normSq (ZMod.stdAddChar (-k) - 1) * Complex.normSq (cfourier z k) := by
  have h := plancherel (fun j => z (j + 1) - z j) (fun j => z (j + 1) - z j)
  simp only [cfourier_step, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_mul] at h
  rw [sides]
  exact_mod_cast h.symm

/-- **Isoperimetric inequality for polygons.** For every closed polygon with `n ≥ 3`
vertices, `2 tan (π/n) · (twice the area) ≤ ∑ side²`. -/
theorem polygon_isoperimetric (hn : 3 ≤ n) (z : ZMod n → ℂ) :
    2 * Real.tan (π / n) * area2 z ≤ sides z := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hterm : ∀ k : ZMod n,
      2 * Real.tan (π / n) * ((ZMod.stdAddChar (-k)).im * Complex.normSq (cfourier z k))
        ≤ Complex.normSq (ZMod.stdAddChar (-k) - 1) * Complex.normSq (cfourier z k) := by
    intro k
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (Complex.normSq_nonneg _)
    rw [normSq_e_sub_one, e_im]
    have := tan_bound hn (-k)
    linarith
  have hsum : 2 * Real.tan (π / n)
        * ∑ k, (ZMod.stdAddChar (-k)).im * Complex.normSq (cfourier z k)
      ≤ ∑ k, Complex.normSq (ZMod.stdAddChar (-k) - 1) * Complex.normSq (cfourier z k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => hterm k)
  rw [← area2_fourier, ← sides_fourier] at hsum
  have hmul : (n : ℝ) * (2 * Real.tan (π / n) * area2 z) ≤ (n : ℝ) * sides z := by
    linarith
  exact le_of_mul_le_mul_left hmul hnpos

/-! ## Sharpness -/

/-- **The regular polygon attains equality.** -/
theorem polygon_sharp (hn : 3 ≤ n) :
    2 * Real.tan (π / n) * area2 (fun j : ZMod n => ZMod.stdAddChar j)
      = sides (fun j : ZMod n => ZMod.stdAddChar j) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : ∀ j : ZMod n, conj (ZMod.stdAddChar j) * ZMod.stdAddChar (j + 1)
      = ZMod.stdAddChar (1 : ZMod n) := by
    intro j
    rw [conj_e, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have h2 : ∀ j : ZMod n, ZMod.stdAddChar (j + 1) - ZMod.stdAddChar j
      = ZMod.stdAddChar j * (ZMod.stdAddChar (1 : ZMod n) - 1) := by
    intro j
    rw [AddChar.map_add_eq_mul]
    ring
  have hA : area2 (fun j : ZMod n => ZMod.stdAddChar j) = n * Real.sin (2 * π / n) := by
    simp only [area2, h1, e_im, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
      ZMod.val_one, Nat.cast_one, mul_one]
  have hS : sides (fun j : ZMod n => ZMod.stdAddChar j)
      = n * (2 - 2 * Real.cos (2 * π / n)) := by
    simp only [sides, h2, Complex.normSq_mul, normSq_e, one_mul, normSq_e_sub_one,
      Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, ZMod.val_one, Nat.cast_one,
      mul_one]
  rw [hA, hS]
  have hb : π / n < π / 2 := by
    rw [div_lt_div_iff₀ hnpos two_pos]
    nlinarith [Real.pi_pos]
  have hc : Real.cos (π / n) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [show 0 < π / n by positivity], hb⟩).ne'
  rw [show 2 * π / (n : ℝ) = 2 * (π / n) by ring, Real.sin_two_mul, Real.cos_two_mul,
    Real.tan_eq_sin_div_cos]
  calc 2 * (Real.sin (π / n) / Real.cos (π / n))
        * (n * (2 * Real.sin (π / n) * Real.cos (π / n)))
      = 4 * n * Real.sin (π / n) * (Real.sin (π / n) / Real.cos (π / n) * Real.cos (π / n)) := by
        ring
    _ = 4 * n * Real.sin (π / n) * Real.sin (π / n) := by
        rw [div_mul_cancel₀ _ hc]
    _ = n * (2 - 2 * (2 * Real.cos (π / n) ^ 2 - 1)) := by
        linear_combination (4 * (n : ℝ)) * Real.sin_sq_add_cos_sq (π / n)

end PolygonIso
