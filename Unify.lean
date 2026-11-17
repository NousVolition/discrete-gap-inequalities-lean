import Polygon
import CubeCheeger

/-!
# One floor, three pushes

Three earlier results are the same inequality, energy ≥ floor × something, with different things
pushed against the floor. This file proves the two general lemmas behind them and restates the
three results as uses of those lemmas.

## Lemma 1: mode by mode (`mode_compare`)

If every mode `k` pays at least `c` times what it contributes (`c · b k ≤ a k`) and the weights
`w k` are nonnegative, then the total pays at least `c` times the total:
`c · ∑ b k · w k ≤ ∑ a k · w k`.

* **A wave** (`wirtinger_by_modes`): on the ring, mode `k ≠ 0` costs `|e(k) − 1|²`, at least the
  floor `2 − 2 cos (2π/n)`; the mean-zero condition removes mode `0`. This is the Wirtinger
  inequality.
* **A shape** (`polygon_by_modes`): for a closed polygon, mode `k` costs `|e(−k) − 1|²` in squared
  sides and carries `Im e(−k)` of area; the cost per unit of area is at least `2 tan (π/n)`. This
  is the polygon isoperimetric inequality.

## Lemma 2: a floor forces long borders (`patch_from_gap`)

On any finite graph with symmetric weights, if
`λ · spread f ≤ |V| · energy f` for every `f` (a floor `λ`), then every patch `S` satisfies
`λ · |S| · (|V| − |S|) ≤ |V| · boundary S`. The proof pushes the on/off pattern of `S` against
the floor.

* **The cube** (`cube_cheeger_by_gap`): with floor `2`, any set of at most half the corners has
  at least as many edges leaving it as it has corners. This is `CubeCheeger.cheeger`, now a
  one-step use of the general lemma.
* **The ring** (`ring_gap`, `ring_patch`): the ring's floor `2 − 2 cos (2π/n)` gives a border
  bound for every patch of the ring. The bound is small because the floor is small: two snips cut
  a ring in two. A small floor means the shape is easy to cut.

In every case the shape that meets the floor exactly is the slowest wave itself: the cosine
(a wave), the half-cube (the cube's slowest wave cut into on/off), the regular polygon (the
slowest wave drawn in the plane).
-/

open Finset ComplexConjugate
open scoped Real

noncomputable section

namespace Unify

/-! ## Lemma 1: mode by mode -/

/-- **Mode-by-mode comparison.** If every mode pays at least `c` times what it contributes, the
total pays at least `c` times the total. -/
theorem mode_compare {ι : Type*} (s : Finset ι) (a b w : ι → ℝ) (c : ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (h : ∀ k ∈ s, c * b k ≤ a k) :
    c * ∑ k ∈ s, b k * w k ≤ ∑ k ∈ s, a k * w k := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun k hk => ?_)
  calc c * (b k * w k) = (c * b k) * w k := by ring
    _ ≤ a k * w k := mul_le_mul_of_nonneg_right (h k hk) (hw k hk)

section Modes

variable {n : ℕ} [NeZero n]

/-- On the ring, every mode pays at least the floor, except mode `0`, which carries nothing. -/
lemma ring_mode (k : ZMod n) :
    (2 - 2 * Real.cos (2 * π / n)) * (if k = 0 then (0 : ℝ) else 1)
      ≤ Complex.normSq (ZMod.stdAddChar k - 1) := by
  by_cases hk : k = 0
  · rw [hk, if_pos rfl, mul_zero]
    exact Complex.normSq_nonneg _
  · rw [if_neg hk, mul_one, CycleWirtinger.normSq_e_sub_one]
    have := CycleWirtinger.cos_le k hk
    linarith

/-- **A wave: the Wirtinger inequality as mode-by-mode comparison.** Same statement as
`CycleWirtinger.wirtinger`. -/
theorem wirtinger_by_modes (f : ZMod n → ℝ) (hmean : ∑ j, f j = 0) :
    (2 - 2 * Real.cos (2 * π / n)) * ∑ j, f j ^ 2 ≤ ∑ j, (f (j + 1) - f j) ^ 2 := by
  have hF0 : CycleWirtinger.fourier f 0 = 0 := by
    simp only [CycleWirtinger.fourier, mul_zero, AddChar.map_zero_eq_one, mul_one]
    exact_mod_cast hmean
  have hcmp : (2 - 2 * Real.cos (2 * π / n))
        * ∑ k, (if k = 0 then (0 : ℝ) else 1) * Complex.normSq (CycleWirtinger.fourier f k)
      ≤ ∑ k, Complex.normSq (ZMod.stdAddChar k - 1)
          * Complex.normSq (CycleWirtinger.fourier f k) :=
    mode_compare Finset.univ
      (fun k => Complex.normSq (ZMod.stdAddChar k - 1))
      (fun k => if k = 0 then (0 : ℝ) else 1)
      (fun k => Complex.normSq (CycleWirtinger.fourier f k))
      (2 - 2 * Real.cos (2 * π / n))
      (fun k _ => Complex.normSq_nonneg _)
      (fun k _ => ring_mode k)
  have hL : ∑ k, (if k = 0 then (0 : ℝ) else 1) * Complex.normSq (CycleWirtinger.fourier f k)
      = ∑ k, Complex.normSq (CycleWirtinger.fourier f k) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : k = 0
    · rw [hk, if_pos rfl, zero_mul, hF0, Complex.normSq_zero]
    · rw [if_neg hk, one_mul]
  have hR : ∑ k, Complex.normSq (ZMod.stdAddChar k - 1)
        * Complex.normSq (CycleWirtinger.fourier f k)
      = ∑ k, Complex.normSq (CycleWirtinger.fourier (fun j => f (j + 1) - f j) k) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [CycleWirtinger.fourier_step, Complex.normSq_mul, CycleWirtinger.normSq_e_neg_sub_one]
  have hg := CycleWirtinger.parseval_real (fun j => f (j + 1) - f j)
  beta_reduce at hg
  have hf := CycleWirtinger.parseval_real f
  rw [hL, hR, hf, hg] at hcmp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  nlinarith [hcmp, hnpos]

/-- For a polygon, every mode's cost in squared sides is at least `2 tan (π/n)` times the area
it carries. -/
lemma polygon_mode (hn : 3 ≤ n) (k : ZMod n) :
    2 * Real.tan (π / n) * (ZMod.stdAddChar (-k)).im
      ≤ Complex.normSq (ZMod.stdAddChar (-k) - 1) := by
  rw [CycleWirtinger.normSq_e_sub_one, PolygonIso.e_im]
  have := PolygonIso.tan_bound hn (-k)
  linarith

/-- **A shape: the polygon isoperimetric inequality as mode-by-mode comparison.** Same
statement as `PolygonIso.polygon_isoperimetric`. -/
theorem polygon_by_modes (hn : 3 ≤ n) (z : ZMod n → ℂ) :
    2 * Real.tan (π / n) * PolygonIso.area2 z ≤ PolygonIso.sides z := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcmp : 2 * Real.tan (π / n)
        * ∑ k, (ZMod.stdAddChar (-k)).im * Complex.normSq (PolygonIso.cfourier z k)
      ≤ ∑ k, Complex.normSq (ZMod.stdAddChar (-k) - 1)
          * Complex.normSq (PolygonIso.cfourier z k) :=
    mode_compare Finset.univ
      (fun k => Complex.normSq (ZMod.stdAddChar (-k) - 1))
      (fun k => (ZMod.stdAddChar (-k)).im)
      (fun k => Complex.normSq (PolygonIso.cfourier z k))
      (2 * Real.tan (π / n))
      (fun k _ => Complex.normSq_nonneg _)
      (fun k _ => polygon_mode hn k)
  rw [← PolygonIso.area2_fourier, ← PolygonIso.sides_fourier] at hcmp
  have hmul : (n : ℝ) * (2 * Real.tan (π / n) * PolygonIso.area2 z)
      ≤ (n : ℝ) * PolygonIso.sides z := by
    linarith
  exact le_of_mul_le_mul_left hmul hnpos

end Modes

/-! ## Lemma 2: a floor forces long borders -/

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Energy over ordered pairs, with edge weights `w`. -/
def energy (w : V → V → ℝ) (f : V → ℝ) : ℝ := ∑ x, ∑ y, w x y * (f x - f y) ^ 2

/-- Sum of squared differences over all ordered pairs. -/
def spread (f : V → ℝ) : ℝ := ∑ x, ∑ y, (f x - f y) ^ 2

/-- The on/off pattern of a patch `S`. -/
def ind (S : Finset V) (x : V) : ℝ := if x ∈ S then 1 else 0

/-- Weighted edges leaving `S`: pairs `(x, y)` with `x ∈ S`, `y ∉ S`. -/
def boundary (w : V → V → ℝ) (S : Finset V) : ℝ :=
  ∑ x, ∑ y, w x y * (ind S x * (1 - ind S y))

lemma ind_sq_diff (S : Finset V) (x y : V) :
    (ind S x - ind S y) ^ 2 = ind S x * (1 - ind S y) + ind S y * (1 - ind S x) := by
  unfold ind
  split_ifs <;> norm_num

lemma sum_ind (S : Finset V) : ∑ x, ind S x = (S.card : ℝ) := by
  unfold ind
  first
  | rw [Finset.sum_boole, Finset.filter_univ_mem]
  | simp

/-- Pushing an on/off pattern against the energy counts its border twice. -/
lemma energy_ind (w : V → V → ℝ) (hsym : ∀ x y, w x y = w y x) (S : Finset V) :
    energy w (ind S) = 2 * boundary w S := by
  have h : energy w (ind S)
      = boundary w S + ∑ x, ∑ y, w x y * (ind S y * (1 - ind S x)) := by
    unfold energy boundary
    simp only [ind_sq_diff, mul_add, Finset.sum_add_distrib]
  have h2 : ∑ x, ∑ y, w x y * (ind S y * (1 - ind S x)) = boundary w S := by
    unfold boundary
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [hsym]
  rw [h, h2]
  ring

/-- The spread of an on/off pattern is `2 · |S| · |outside|`. -/
lemma spread_ind (S : Finset V) :
    spread (ind S) = 2 * (∑ x, ind S x) * ((Fintype.card V : ℝ) - ∑ x, ind S x) := by
  have hone : ∑ y : V, (1 - ind S y) = (Fintype.card V : ℝ) - ∑ y, ind S y := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have h1 : ∑ x : V, ∑ y : V, ind S x * (1 - ind S y)
      = (∑ x, ind S x) * ∑ y, (1 - ind S y) := by
    rw [Finset.sum_mul_sum]
  have h2 : ∑ x : V, ∑ y : V, ind S y * (1 - ind S x)
      = (∑ x, ind S x) * ∑ y, (1 - ind S y) := by
    rw [Finset.sum_comm]
    exact h1
  unfold spread
  simp only [ind_sq_diff, Finset.sum_add_distrib]
  rw [h1, h2, hone]
  ring

/-- For mean-zero `f`, `spread f = 2 · |V| · ∑ f²`. -/
lemma spread_of_mean_zero (f : V → ℝ) (h0 : ∑ x, f x = 0) :
    spread f = 2 * (Fintype.card V : ℝ) * ∑ x, f x ^ 2 := by
  have hrow : ∀ x : V, ∑ y, (f x - f y) ^ 2 = (Fintype.card V : ℝ) * f x ^ 2 + ∑ y, f y ^ 2 := by
    intro x
    have hexp : ∀ y, (f x - f y) ^ 2 = f x ^ 2 + f y ^ 2 - 2 * f x * f y := fun y => by ring
    rw [Finset.sum_congr rfl (fun y _ => hexp y), Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum, h0, mul_zero, sub_zero]
  unfold spread
  rw [Finset.sum_congr rfl (fun x _ => hrow x), Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- **A floor forces long borders.** If `λ · spread f ≤ |V| · energy f` for every `f`, then every
patch `S` has `λ · |S| · (|V| − |S|) ≤ |V| · boundary S`. -/
theorem patch_from_gap (w : V → V → ℝ) (hsym : ∀ x y, w x y = w y x) (lam : ℝ)
    (hgap : ∀ f : V → ℝ, lam * spread f ≤ (Fintype.card V : ℝ) * energy w f)
    (S : Finset V) :
    lam * (S.card : ℝ) * ((Fintype.card V : ℝ) - S.card)
      ≤ (Fintype.card V : ℝ) * boundary w S := by
  have hg := hgap (ind S)
  rw [spread_ind, energy_ind w hsym, sum_ind] at hg
  have key : 2 * (lam * (S.card : ℝ) * ((Fintype.card V : ℝ) - S.card))
      ≤ 2 * ((Fintype.card V : ℝ) * boundary w S) := by
    calc 2 * (lam * (S.card : ℝ) * ((Fintype.card V : ℝ) - S.card))
        = lam * (2 * (S.card : ℝ) * ((Fintype.card V : ℝ) - S.card)) := by ring
      _ ≤ (Fintype.card V : ℝ) * (2 * boundary w S) := hg
      _ = 2 * ((Fintype.card V : ℝ) * boundary w S) := by ring
  linarith

end Graph

/-! ## The cube: Cheeger as one use of the general lemma -/

/-- **A patch on the cube.** Same statement as `CubeCheeger.cheeger`, now from
`patch_from_gap` with floor `2`. -/
theorem cube_cheeger_by_gap {n : ℕ} (S : Finset (CubeCheeger.Cube n))
    (hS : 2 * S.card ≤ 2 ^ n) :
    (S.card : ℝ) ≤ CubeCheeger.boundary S := by
  have hgap : ∀ f : CubeCheeger.Cube n → ℝ,
      2 * spread f ≤ (Fintype.card (CubeCheeger.Cube n) : ℝ) * energy CubeCheeger.adj f := by
    intro f
    rw [CubeCheeger.card_cube]
    exact CubeCheeger.gap n f
  have h := patch_from_gap CubeCheeger.adj CubeCheeger.adj_comm 2 hgap S
  have hb : boundary CubeCheeger.adj S = CubeCheeger.boundary S := rfl
  rw [hb, CubeCheeger.card_cube] at h
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hs0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hS' : 2 * (S.card : ℝ) ≤ 2 ^ n := by exact_mod_cast hS
  have hmul : (2 : ℝ) ^ n * S.card ≤ 2 ^ n * CubeCheeger.boundary S := by
    nlinarith [mul_nonneg hs0 (sub_nonneg.2 hS')]
  exact le_of_mul_le_mul_left hmul hN

/-! ## The ring: the same lemma, a small floor, a weak border bound -/

section RingPatch

variable {n : ℕ} [NeZero n]

/-- Ring edges: `x` and `y` are joined when one is the other plus one. -/
def ringW (x y : ZMod n) : ℝ := (if y = x + 1 then 1 else 0) + (if x = y + 1 then 1 else 0)

lemma ringW_comm (x y : ZMod n) : ringW x y = ringW y x := by
  unfold ringW
  exact add_comm _ _

/-- The ring's energy counts each step twice. -/
lemma ring_energy (f : ZMod n → ℝ) :
    energy ringW f = 2 * ∑ j, (f (j + 1) - f j) ^ 2 := by
  have hA : ∑ x : ZMod n, ∑ y : ZMod n, (if y = x + 1 then (f x - f y) ^ 2 else 0)
      = ∑ x : ZMod n, (f x - f (x + 1)) ^ 2 := by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hB : ∑ x : ZMod n, ∑ y : ZMod n, (if x = y + 1 then (f x - f y) ^ 2 else 0)
      = ∑ y : ZMod n, (f (y + 1) - f y) ^ 2 := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have h1 : ∑ x : ZMod n, (f x - f (x + 1)) ^ 2 = ∑ j : ZMod n, (f (j + 1) - f j) ^ 2 :=
    Finset.sum_congr rfl (fun x _ => by ring)
  unfold energy ringW
  simp only [add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib]
  rw [hA, hB, h1]
  ring

/-- **The ring's floor in graph form.** `(2 − 2 cos (2π/n)) · spread f ≤ n · energy f` for every
`f`, from the Wirtinger inequality applied to `f` minus its mean. -/
theorem ring_gap (f : ZMod n → ℝ) :
    (2 - 2 * Real.cos (2 * π / n)) * spread f
      ≤ (Fintype.card (ZMod n) : ℝ) * energy ringW f := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hm : (∑ i, f i) / n * n = ∑ i, f i := div_mul_cancel₀ _ hn0
  -- `g` is `f` minus its mean
  set g : ZMod n → ℝ := fun j => f j - (∑ i, f i) / n with hg
  have hg0 : ∑ j, g j = 0 := by
    simp only [hg]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
      mul_comm, hm, sub_self]
  have hW := CycleWirtinger.wirtinger g hg0
  have hsteps : ∑ j, (g (j + 1) - g j) ^ 2 = ∑ j, (f (j + 1) - f j) ^ 2 :=
    Finset.sum_congr rfl (fun j _ => by simp only [hg]; ring)
  rw [hsteps] at hW
  have hshift : spread f = spread g := by
    unfold spread
    exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by
      simp only [hg]; ring))
  have hspread : spread f = 2 * (n : ℝ) * ∑ j, g j ^ 2 := by
    rw [hshift, spread_of_mean_zero g hg0, ZMod.card]
  rw [hspread, ring_energy, ZMod.card]
  have h2n : (0 : ℝ) ≤ 2 * n := by positivity
  have := mul_le_mul_of_nonneg_left hW h2n
  linarith

/-- **A patch on the ring.** The ring's floor gives a border bound for every patch, from the
same lemma as the cube. -/
theorem ring_patch (S : Finset (ZMod n)) :
    (2 - 2 * Real.cos (2 * π / n)) * (S.card : ℝ) * ((n : ℝ) - S.card)
      ≤ (n : ℝ) * boundary ringW S := by
  have h := patch_from_gap ringW ringW_comm (2 - 2 * Real.cos (2 * π / n)) ring_gap S
  rw [ZMod.card] at h
  exact h

end RingPatch

end Unify
