import Mathlib

/-!
# The hypercube's spectral gap, and Cheeger's inequality on the cube

Vertices of the `n`-cube are `Fin n → Bool`; `adj x y = 1` when they differ in one coordinate.
For `f : Cube n → ℝ`:

* `energy f = ∑ₓ ∑ᵧ adj x y · (f x − f y)²`: each edge counted twice;
* `spread f = ∑ₓ ∑ᵧ (f x − f y)²`: all ordered pairs, equal to `2 · 2ⁿ · ∑ (f − mean)²`.

**Theorem (`gap`).** `2 · spread f ≤ 2ⁿ · energy f`.

Rewritten with the mean, this reads `∑_edges (f x − f y)² ≥ 2 · ∑ (f − mean)²`: the cube's
spectral gap is `2`. The proof is by induction on `n`, cutting along the first coordinate. The
only new ingredient at each step is `cross_le`, whose pointwise core is the square
`((a u − b u) − (a v − b v))² ≥ 0`.

**Cheeger's easy direction on the cube (`cheeger`).** Apply the gap to the indicator of `S`. If
`|S| ≤ 2ⁿ⁻¹`, then at least `|S|` edges leave `S`, i.e. the cut per corner is at least
`gap / 2 = 1`.

**Exactness (`half_exact`).** The half-cube `{x | x 0 = true}` has `2ⁿ` corners and exactly `2ⁿ`
edges leaving it. So the bound from the gap and the cheapest cut are equal on the cube.
-/

open Finset

noncomputable section

namespace CubeCheeger

/-- The `n`-cube. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- `1` if `x` and `y` are adjacent, else `0`. -/
def adj {n : ℕ} (x y : Cube n) : ℝ := if hammingDist x y = 1 then 1 else 0

/-- Dirichlet energy over ordered adjacent pairs. -/
def energy {n : ℕ} (f : Cube n → ℝ) : ℝ := ∑ x, ∑ y, adj x y * (f x - f y) ^ 2

/-- Sum of squared differences over all ordered pairs. -/
def spread {n : ℕ} (f : Cube n → ℝ) : ℝ := ∑ x, ∑ y, (f x - f y) ^ 2

/-! ## Splitting by the first coordinate -/

lemma hammingDist_cons {n : ℕ} (a b : Bool) (u v : Cube n) :
    hammingDist (Fin.cons a u : Cube (n + 1)) (Fin.cons b v)
      = (if a = b then 0 else 1) + hammingDist u v := by
  unfold hammingDist
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  congr 1
  by_cases h : a = b <;> simp [h]

lemma sum_cube_succ {n : ℕ} {M : Type*} [AddCommMonoid M] (g : Cube (n + 1) → M) :
    ∑ x, g x = ∑ u : Cube n, g (Fin.cons true u) + ∑ u : Cube n, g (Fin.cons false u) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp g, Fintype.sum_prod_type, Fintype.sum_bool]
  rfl

lemma adj_comm {n : ℕ} (x y : Cube n) : adj x y = adj y x := by
  unfold adj
  rw [hammingDist_comm]

lemma adj_nonneg {n : ℕ} (x y : Cube n) : 0 ≤ adj x y := by
  unfold adj
  split_ifs <;> norm_num

lemma adj_cons {n : ℕ} (a b : Bool) (u v : Cube n) :
    adj (Fin.cons a u : Cube (n + 1)) (Fin.cons b v)
      = if a = b then adj u v else (if u = v then 1 else 0) := by
  unfold adj
  rw [hammingDist_cons]
  by_cases hab : a = b
  · simp [hab]
  · rw [if_neg hab, if_neg hab]
    have h : (1 + hammingDist u v = 1) ↔ u = v := by
      rw [← hammingDist_eq_zero]
      constructor <;> intro h <;> omega
    simp only [h]

lemma energy_nonneg {n : ℕ} (f : Cube n → ℝ) : 0 ≤ energy f :=
  Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ =>
    mul_nonneg (adj_nonneg x y) (sq_nonneg _)))

lemma card_cube (n : ℕ) : (Fintype.card (Cube n) : ℝ) = 2 ^ n := by
  have h : Fintype.card (Cube n) = 2 ^ n := by simp
  exact_mod_cast h

/-- Energy splits into the two halves plus twice the edges across. -/
lemma energy_succ {n : ℕ} (f : Cube (n + 1) → ℝ) :
    energy f = energy (fun u => f (Fin.cons true u)) + energy (fun u => f (Fin.cons false u))
      + 2 * ∑ u : Cube n, (f (Fin.cons true u) - f (Fin.cons false u)) ^ 2 := by
  have hsplit : energy f
      = (∑ u : Cube n, ∑ v : Cube n, adj (Fin.cons true u : Cube (n + 1)) (Fin.cons true v)
          * (f (Fin.cons true u) - f (Fin.cons true v)) ^ 2)
      + (∑ u : Cube n, ∑ v : Cube n, adj (Fin.cons true u : Cube (n + 1)) (Fin.cons false v)
          * (f (Fin.cons true u) - f (Fin.cons false v)) ^ 2)
      + (∑ u : Cube n, ∑ v : Cube n, adj (Fin.cons false u : Cube (n + 1)) (Fin.cons true v)
          * (f (Fin.cons false u) - f (Fin.cons true v)) ^ 2)
      + (∑ u : Cube n, ∑ v : Cube n, adj (Fin.cons false u : Cube (n + 1)) (Fin.cons false v)
          * (f (Fin.cons false u) - f (Fin.cons false v)) ^ 2) := by
    unfold energy
    simp only [sum_cube_succ, Finset.sum_add_distrib]
    ring
  have hTT : (∑ u : Cube n, ∑ v : Cube n, adj (Fin.cons true u : Cube (n + 1)) (Fin.cons true v)
          * (f (Fin.cons true u) - f (Fin.cons true v)) ^ 2)
      = energy (fun u => f (Fin.cons true u)) := by
    simp [energy, adj_cons]
  have hFF : (∑ u : Cube n, ∑ v : Cube n, adj (Fin.cons false u : Cube (n + 1)) (Fin.cons false v)
          * (f (Fin.cons false u) - f (Fin.cons false v)) ^ 2)
      = energy (fun u => f (Fin.cons false u)) := by
    simp [energy, adj_cons]
  have hTF : (∑ u : Cube n, ∑ v : Cube n, adj (Fin.cons true u : Cube (n + 1)) (Fin.cons false v)
          * (f (Fin.cons true u) - f (Fin.cons false v)) ^ 2)
      = ∑ u : Cube n, (f (Fin.cons true u) - f (Fin.cons false u)) ^ 2 := by
    simp [adj_cons]
  have hFT : (∑ u : Cube n, ∑ v : Cube n, adj (Fin.cons false u : Cube (n + 1)) (Fin.cons true v)
          * (f (Fin.cons false u) - f (Fin.cons true v)) ^ 2)
      = ∑ u : Cube n, (f (Fin.cons false u) - f (Fin.cons true u)) ^ 2 := by
    simp [adj_cons]
  have hsym : ∑ u : Cube n, (f (Fin.cons false u) - f (Fin.cons true u)) ^ 2
      = ∑ u : Cube n, (f (Fin.cons true u) - f (Fin.cons false u)) ^ 2 :=
    Finset.sum_congr rfl (fun u _ => by ring)
  rw [hsplit, hTT, hFF, hTF, hFT, hsym]
  ring

/-- Spread splits into the two halves plus twice the pairs across. -/
lemma spread_succ {n : ℕ} (f : Cube (n + 1) → ℝ) :
    spread f = spread (fun u => f (Fin.cons true u)) + spread (fun u => f (Fin.cons false u))
      + 2 * ∑ u : Cube n, ∑ v : Cube n, (f (Fin.cons true u) - f (Fin.cons false v)) ^ 2 := by
  have hsplit : spread f
      = (∑ u : Cube n, ∑ v : Cube n, (f (Fin.cons true u) - f (Fin.cons true v)) ^ 2)
      + (∑ u : Cube n, ∑ v : Cube n, (f (Fin.cons true u) - f (Fin.cons false v)) ^ 2)
      + (∑ u : Cube n, ∑ v : Cube n, (f (Fin.cons false u) - f (Fin.cons true v)) ^ 2)
      + (∑ u : Cube n, ∑ v : Cube n, (f (Fin.cons false u) - f (Fin.cons false v)) ^ 2) := by
    unfold spread
    simp only [sum_cube_succ, Finset.sum_add_distrib]
    ring
  have hFT : (∑ u : Cube n, ∑ v : Cube n, (f (Fin.cons false u) - f (Fin.cons true v)) ^ 2)
      = ∑ u : Cube n, ∑ v : Cube n, (f (Fin.cons true u) - f (Fin.cons false v)) ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => by ring))
  rw [hsplit, hFT]
  unfold spread
  ring

/-! ## The gap -/

/-- The cross term is controlled by the two halves and the matched pairs. -/
lemma cross_le {n : ℕ} (a b : Cube n → ℝ) :
    2 * ∑ u, ∑ v, (a u - b v) ^ 2
      ≤ spread a + spread b + 2 * (Fintype.card (Cube n) : ℝ) * ∑ u, (a u - b u) ^ 2 := by
  have h0 : 0 ≤ ∑ u : Cube n, ∑ v : Cube n, ((a u - b u) - (a v - b v)) ^ 2 :=
    Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ => sq_nonneg _))
  have hpt : ∀ u v : Cube n, ((a u - b u) - (a v - b v)) ^ 2
      = (a u - a v) ^ 2 + (b u - b v) ^ 2 + (a u - b u) ^ 2 + (a v - b v) ^ 2
        - (a u - b v) ^ 2 - (a v - b u) ^ 2 := fun u v => by ring
  have hid : ∑ u : Cube n, ∑ v : Cube n, ((a u - b u) - (a v - b v)) ^ 2
      = spread a + spread b + ∑ u : Cube n, ∑ v : Cube n, (a u - b u) ^ 2
        + ∑ u : Cube n, ∑ v : Cube n, (a v - b v) ^ 2
        - ∑ u : Cube n, ∑ v : Cube n, (a u - b v) ^ 2
        - ∑ u : Cube n, ∑ v : Cube n, (a v - b u) ^ 2 := by
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, spread]
  have hc1 : ∑ u : Cube n, ∑ v : Cube n, (a u - b u) ^ 2
      = (Fintype.card (Cube n) : ℝ) * ∑ u, (a u - b u) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc2 : ∑ u : Cube n, ∑ v : Cube n, (a v - b v) ^ 2
      = (Fintype.card (Cube n) : ℝ) * ∑ u, (a u - b u) ^ 2 := by
    rw [Finset.sum_comm]
    exact hc1
  have hx : ∑ u : Cube n, ∑ v : Cube n, (a v - b u) ^ 2
      = ∑ u : Cube n, ∑ v : Cube n, (a u - b v) ^ 2 := Finset.sum_comm
  linarith [h0, hid, hc1, hc2, hx]

/-- **The spectral gap of the cube is `2`.** -/
theorem gap (n : ℕ) (f : Cube n → ℝ) : 2 * spread f ≤ 2 ^ n * energy f := by
  induction n with
  | zero =>
    have hs : spread f = 0 := by
      unfold spread
      apply Finset.sum_eq_zero
      intro x _
      apply Finset.sum_eq_zero
      intro y _
      rw [Subsingleton.elim x y, sub_self]
      ring
    rw [hs, pow_zero, one_mul, mul_zero]
    exact energy_nonneg f
  | succ n ih =>
    rw [spread_succ, energy_succ, pow_succ]
    have h1 := ih (fun u => f (Fin.cons true u))
    have h0 := ih (fun u => f (Fin.cons false u))
    have hc := cross_le (fun u => f (Fin.cons true u)) (fun u => f (Fin.cons false u))
    rw [card_cube] at hc
    beta_reduce at hc
    first
    | linarith [h1, h0, hc]
    | nlinarith [h1, h0, hc]

/-! ## Cheeger's easy direction -/

/-- Indicator of `S`. -/
def ind {n : ℕ} (S : Finset (Cube n)) (x : Cube n) : ℝ := if x ∈ S then 1 else 0

/-- Edges leaving `S`: adjacent pairs `(x, y)` with `x ∈ S` and `y ∉ S`. -/
def boundary {n : ℕ} (S : Finset (Cube n)) : ℝ :=
  ∑ x, ∑ y, adj x y * (ind S x * (1 - ind S y))

lemma ind_sq_diff {n : ℕ} (S : Finset (Cube n)) (x y : Cube n) :
    (ind S x - ind S y) ^ 2 = ind S x * (1 - ind S y) + ind S y * (1 - ind S x) := by
  unfold ind
  split_ifs <;> norm_num

lemma sum_ind {n : ℕ} (S : Finset (Cube n)) : ∑ x, ind S x = (S.card : ℝ) := by
  unfold ind
  first
  | rw [Finset.sum_boole, Finset.filter_univ_mem]
  | simp

lemma energy_ind {n : ℕ} (S : Finset (Cube n)) : energy (ind S) = 2 * boundary S := by
  have h : energy (ind S) = boundary S + ∑ x, ∑ y, adj x y * (ind S y * (1 - ind S x)) := by
    unfold energy boundary
    simp only [ind_sq_diff, mul_add, Finset.sum_add_distrib]
  have h2 : ∑ x, ∑ y, adj x y * (ind S y * (1 - ind S x)) = boundary S := by
    unfold boundary
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [adj_comm]
  rw [h, h2]
  ring

lemma spread_ind {n : ℕ} (S : Finset (Cube n)) :
    spread (ind S)
      = 2 * (∑ x, ind S x) * ((Fintype.card (Cube n) : ℝ) - ∑ x, ind S x) := by
  have hone : ∑ y : Cube n, (1 - ind S y) = (Fintype.card (Cube n) : ℝ) - ∑ y, ind S y := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have h1 : ∑ x : Cube n, ∑ y : Cube n, ind S x * (1 - ind S y)
      = (∑ x, ind S x) * ∑ y, (1 - ind S y) := by
    rw [Finset.sum_mul_sum]
  have h2 : ∑ x : Cube n, ∑ y : Cube n, ind S y * (1 - ind S x)
      = (∑ x, ind S x) * ∑ y, (1 - ind S y) := by
    rw [Finset.sum_comm]
    exact h1
  unfold spread
  simp only [ind_sq_diff, Finset.sum_add_distrib]
  rw [h1, h2, hone]
  ring

/-- **Cheeger's easy direction on the cube.** If `S` has at most half the corners, at least
`|S|` edges leave it. -/
theorem cheeger {n : ℕ} (S : Finset (Cube n)) (hS : 2 * S.card ≤ 2 ^ n) :
    (S.card : ℝ) ≤ boundary S := by
  have hg := gap n (ind S)
  rw [spread_ind, energy_ind, sum_ind, card_cube] at hg
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hs0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hS' : 2 * (S.card : ℝ) ≤ 2 ^ n := by exact_mod_cast hS
  have hmul : (2 : ℝ) ^ n * S.card ≤ 2 ^ n * boundary S := by
    nlinarith [mul_nonneg hs0 (sub_nonneg.2 hS')]
  exact le_of_mul_le_mul_left hmul hN

/-! ## The bound is exact -/

/-- The half-cube: first coordinate `true`. -/
def half (n : ℕ) : Finset (Cube (n + 1)) := univ.filter fun x => x 0 = true

/-- **Exactness.** The half-cube has `2ⁿ` corners and exactly `2ⁿ` edges leaving it. -/
theorem half_exact (n : ℕ) :
    ((half n).card : ℝ) = 2 ^ n ∧ boundary (half n) = 2 ^ n := by
  have hind : ∀ (b : Bool) (u : Cube n),
      ind (half n) (Fin.cons b u) = if b = true then 1 else 0 := by
    intro b u
    simp [ind, half]
  constructor
  · rw [← sum_ind, sum_cube_succ]
    simp [hind, card_cube]
  · unfold boundary
    simp only [sum_cube_succ, Finset.sum_add_distrib]
    simp [hind, adj_cons, card_cube]

end CubeCheeger
