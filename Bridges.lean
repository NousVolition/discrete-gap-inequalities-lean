import Polygon
import CubeCheeger

/-!
# Bridges between the cycle, polygon and cube packages

* `cycle_gap_two`: the cycle gap `2 − 2 cos (2π/n)` at length `n = 2` is `4`.
* `cube_poincare`: for mean-zero `f` on the `n`-cube, `(2 − 2 cos (2π/2)) · ∑ f² ≤ energy f`.
  The cube's gap is the gap of a cycle of length 2, the cube's one-edge factor. Taking a product
  does not lower the gap. `(−1)^(x 0)` gives equality.
* `cfourier_ofReal`: on real data, the polygon package's complex Fourier transform is the
  Wirtinger package's transform.
* `parseval_real_of_plancherel`: the Wirtinger Parseval identity, recovered from the polygon
  package's Plancherel identity.
-/

open Finset ComplexConjugate
open scoped Real

namespace Bridges

/-- The cycle gap at length 2 is 4. -/
lemma cycle_gap_two : (2 : ℝ) - 2 * Real.cos (2 * π / 2) = 4 := by
  rw [show (2 : ℝ) * π / 2 = π by ring, Real.cos_pi]
  norm_num

/-- For mean-zero `f`, `spread f = 2 · 2ⁿ · ∑ f²`. -/
lemma spread_of_mean_zero {n : ℕ} (f : CubeCheeger.Cube n → ℝ) (h0 : ∑ x, f x = 0) :
    CubeCheeger.spread f = 2 * (Fintype.card (CubeCheeger.Cube n) : ℝ) * ∑ x, f x ^ 2 := by
  have hcross : ∀ x : CubeCheeger.Cube n, ∑ y, f x * f y = 0 := fun x => by
    rw [← Finset.mul_sum, h0, mul_zero]
  have hsq : ∑ _x : CubeCheeger.Cube n, ∑ y : CubeCheeger.Cube n, f y ^ 2
      = (Fintype.card (CubeCheeger.Cube n) : ℝ) * ∑ y, f y ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsq' : ∑ x : CubeCheeger.Cube n, ∑ _y : CubeCheeger.Cube n, f x ^ 2
      = (Fintype.card (CubeCheeger.Cube n) : ℝ) * ∑ x, f x ^ 2 := by
    rw [Finset.sum_comm]
    exact hsq
  have hexp : CubeCheeger.spread f
      = ∑ x : CubeCheeger.Cube n, ∑ _y : CubeCheeger.Cube n, f x ^ 2
        + ∑ _x : CubeCheeger.Cube n, ∑ y : CubeCheeger.Cube n, f y ^ 2
        - 2 * ∑ x : CubeCheeger.Cube n, ∑ y : CubeCheeger.Cube n, f x * f y := by
    unfold CubeCheeger.spread
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  rw [hexp, hsq', hsq, Finset.sum_eq_zero (fun x _ => hcross x), mul_zero, sub_zero]
  ring

/-- **The cube's gap is the length-2 cycle gap.** For mean-zero `f`,
`(2 − 2 cos (2π/2)) · ∑ f² ≤ energy f`. -/
theorem cube_poincare {n : ℕ} (f : CubeCheeger.Cube n → ℝ) (h0 : ∑ x, f x = 0) :
    (2 - 2 * Real.cos (2 * π / 2)) * ∑ x, f x ^ 2 ≤ CubeCheeger.energy f := by
  rw [cycle_gap_two]
  have hg := CubeCheeger.gap n f
  rw [spread_of_mean_zero f h0, CubeCheeger.card_cube] at hg
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hmul : (2 : ℝ) ^ n * (4 * ∑ x, f x ^ 2) ≤ 2 ^ n * CubeCheeger.energy f := by
    linarith
  exact le_of_mul_le_mul_left hmul hN

/-- On real data the polygon's Fourier transform is the Wirtinger one. -/
lemma cfourier_ofReal {n : ℕ} [NeZero n] (f : ZMod n → ℝ) (k : ZMod n) :
    PolygonIso.cfourier (fun j => (f j : ℂ)) k = CycleWirtinger.fourier f k := by
  first
  | rfl
  | simp [PolygonIso.cfourier, CycleWirtinger.fourier]

/-- The polygon's Plancherel identity gives back the Wirtinger Parseval identity. -/
lemma parseval_real_of_plancherel {n : ℕ} [NeZero n] (f : ZMod n → ℝ) :
    ∑ k, Complex.normSq (CycleWirtinger.fourier f k) = n * ∑ j, f j ^ 2 := by
  have h := PolygonIso.plancherel (fun j => (f j : ℂ)) (fun j => (f j : ℂ))
  simp only [cfourier_ofReal, ← Complex.normSq_eq_conj_mul_self, Complex.conj_ofReal] at h
  have h2 : ∀ j : ZMod n, (f j : ℂ) * (f j : ℂ) = ((f j ^ 2 : ℝ) : ℂ) := fun j => by
    push_cast
    ring
  simp only [h2] at h
  exact_mod_cast h

end Bridges
