import Mathlib

/-!
# The edge-isoperimetric inequality on the hypercube

Vertices of the `n`-cube are `Fin n → Bool`; two vertices are adjacent when their Hamming distance
is `1`. For a vertex set `s` (a predicate), `size s` is its number of vertices and `dir s` the
number of ordered adjacent pairs inside it (twice the number of edges it spans).

**Theorem (`edges_le`).** `dir s * log 2 ≤ size s * log (size s)`, i.e. a set of `m` vertices spans
at most `(m/2) log₂ m` edges. Equivalently, since every vertex has degree `n`, at least
`m (n - log₂ m)` edges leave it. (Harper; Bernstein; Hart.)

Proof: split the cube by the first coordinate. If the halves hold `a` and `b` vertices, the edges
across are at most `min a b`, and the inductive step is the real inequality
`a log a + b log b + 2 b log 2 ≤ (a + b) log (a + b)` for `0 ≤ b ≤ a` (`key`), which follows from the
concavity of binary entropy (`Real.strictConcave_binEntropy`).
-/

open Finset Real

namespace HypercubeIso

/-- The `n`-cube. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- Number of vertices in `s`. -/
def size {n : ℕ} (s : Cube n → Bool) : ℕ := ∑ x, if s x then 1 else 0

/-- `1` if `x` and `y` are adjacent and both in `s`. -/
def w {n : ℕ} (s : Cube n → Bool) (x y : Cube n) : ℕ :=
  if s x ∧ s y ∧ hammingDist x y = 1 then 1 else 0

/-- Ordered adjacent pairs inside `s`: twice the number of edges spanned by `s`. -/
def dir {n : ℕ} (s : Cube n → Bool) : ℕ := ∑ x, ∑ y, w s x y

/-- Vertices whose two lifts (first coordinate `true` and `false`) both lie in `s`. -/
def common {n : ℕ} (s : Cube (n + 1) → Bool) : ℕ :=
  ∑ u : Cube n, if s (Fin.cons true u) ∧ s (Fin.cons false u) then 1 else 0

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

lemma size_succ {n : ℕ} (s : Cube (n + 1) → Bool) :
    size s = size (fun u => s (Fin.cons true u)) + size (fun u => s (Fin.cons false u)) := by
  unfold size
  exact sum_cube_succ (fun x => if s x then 1 else 0)

lemma w_same {n : ℕ} (s : Cube (n + 1) → Bool) (a : Bool) (u v : Cube n) :
    w s (Fin.cons a u) (Fin.cons a v) = w (fun z => s (Fin.cons a z)) u v := by
  simp [w, hammingDist_cons]

lemma w_cross {n : ℕ} (s : Cube (n + 1) → Bool) {a b : Bool} (hab : a ≠ b) (u v : Cube n) :
    w s (Fin.cons a u) (Fin.cons b v)
      = if v = u then (if s (Fin.cons a u) ∧ s (Fin.cons b u) then 1 else 0) else 0 := by
  unfold w
  rw [hammingDist_cons, if_neg hab]
  by_cases h : v = u
  · subst h
    simp
  · have h0 : hammingDist u v ≠ 0 := fun h0 => h (hammingDist_eq_zero.mp h0).symm
    have h' : u ≠ v := fun e => h e.symm
    simp [h, h', h0]

lemma sum_cross {n : ℕ} (s : Cube (n + 1) → Bool) {a b : Bool} (hab : a ≠ b) :
    ∑ u : Cube n, ∑ v : Cube n, w s (Fin.cons a u) (Fin.cons b v)
      = ∑ u : Cube n, if s (Fin.cons a u) ∧ s (Fin.cons b u) then 1 else 0 := by
  refine Finset.sum_congr rfl (fun u _ => ?_)
  simp only [w_cross s hab]
  simp

/-- `dir` of the cube splits into the two halves plus twice the edges across. -/
lemma dir_succ {n : ℕ} (s : Cube (n + 1) → Bool) :
    dir s = dir (fun u => s (Fin.cons true u)) + dir (fun u => s (Fin.cons false u))
      + 2 * common s := by
  have hsplit : dir s = (∑ u : Cube n, ∑ v : Cube n, w s (Fin.cons true u) (Fin.cons true v))
      + (∑ u : Cube n, ∑ v : Cube n, w s (Fin.cons true u) (Fin.cons false v))
      + (∑ u : Cube n, ∑ v : Cube n, w s (Fin.cons false u) (Fin.cons true v))
      + (∑ u : Cube n, ∑ v : Cube n, w s (Fin.cons false u) (Fin.cons false v)) := by
    unfold dir
    simp only [sum_cube_succ, Finset.sum_add_distrib]
    ring
  have hTT : ∑ u : Cube n, ∑ v : Cube n, w s (Fin.cons true u) (Fin.cons true v)
      = dir (fun u => s (Fin.cons true u)) := by
    simp only [w_same]
    rfl
  have hFF : ∑ u : Cube n, ∑ v : Cube n, w s (Fin.cons false u) (Fin.cons false v)
      = dir (fun u => s (Fin.cons false u)) := by
    simp only [w_same]
    rfl
  have hTF := sum_cross s (a := true) (b := false) (by decide)
  have hFT := sum_cross s (a := false) (b := true) (by decide)
  have hsym : (∑ u : Cube n, if s (Fin.cons false u) ∧ s (Fin.cons true u) then 1 else 0)
      = common s := by
    unfold common
    refine Finset.sum_congr rfl (fun u _ => ?_)
    simp only [and_comm]
  rw [hsplit, hTT, hFF, hTF, hFT, hsym]
  unfold common
  ring

lemma common_le_true {n : ℕ} (s : Cube (n + 1) → Bool) :
    common s ≤ size (fun u => s (Fin.cons true u)) := by
  unfold common size
  apply Finset.sum_le_sum
  intro u _
  split_ifs <;> simp_all

lemma common_le_false {n : ℕ} (s : Cube (n + 1) → Bool) :
    common s ≤ size (fun u => s (Fin.cons false u)) := by
  unfold common size
  apply Finset.sum_le_sum
  intro u _
  split_ifs <;> simp_all

/-! ## The base case -/

lemma dir_zero (s : Cube 0 → Bool) : dir s = 0 := by
  unfold dir w
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  have h : hammingDist x y = 0 := hammingDist_eq_zero.mpr (Subsingleton.elim x y)
  simp [h]

lemma natlog_nonneg (m : ℕ) : 0 ≤ (m : ℝ) * Real.log m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · simp [h]
  · exact mul_nonneg (Nat.cast_nonneg m)
      (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h.ne'))

/-! ## The real inequality -/

/-- For `0 ≤ b ≤ a`: `a log a + b log b + 2 b log 2 ≤ (a + b) log (a + b)`. -/
lemma key {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) :
    a * Real.log a + b * Real.log b + 2 * b * Real.log 2 ≤ (a + b) * Real.log (a + b) := by
  rcases hb.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp
  have ha : 0 < a := lt_of_lt_of_le hpos hba
  have hs : 0 < a + b := by linarith
  have hs0 : a + b ≠ 0 := hs.ne'
  have ht1 : 2 * (b / (a + b)) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one hs]
    linarith
  have ht0 : 0 ≤ b / (a + b) := div_nonneg hb hs.le
  have hconc := Real.strictConcave_binEntropy.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    (show (2⁻¹ : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    (show (0 : ℝ) ≤ 1 - 2 * (b / (a + b)) by linarith)
    (show (0 : ℝ) ≤ 2 * (b / (a + b)) by linarith)
    (show (1 - 2 * (b / (a + b))) + 2 * (b / (a + b)) = 1 by ring)
  simp only [smul_eq_mul, Real.binEntropy_zero, Real.binEntropy_two_inv, mul_zero,
    zero_add] at hconc
  rw [show 2 * (b / (a + b)) * 2⁻¹ = b / (a + b) by ring] at hconc
  have hH : Real.binEntropy (b / (a + b)) * (a + b)
      = (a + b) * Real.log (a + b) - a * Real.log a - b * Real.log b := by
    have h1 : 1 - b / (a + b) = a / (a + b) := by
      first
      | (field_simp; ring)
      | field_simp
    rw [Real.binEntropy, h1, inv_div, inv_div, Real.log_div hs.ne' hpos.ne',
      Real.log_div hs.ne' ha.ne']
    first
    | (field_simp; ring)
    | field_simp
  have hL : 2 * (b / (a + b)) * Real.log 2 * (a + b) = 2 * b * Real.log 2 := by
    first
    | (field_simp; ring)
    | field_simp
  have hmul := mul_le_mul_of_nonneg_right hconc hs.le
  rw [hL, hH] at hmul
  linarith

/-! ## The theorem -/

/-- **Edge-isoperimetric inequality on the hypercube.** A set of `m` vertices spans at most
`(m/2) log₂ m` edges: `dir s · log 2 ≤ m log m`. -/
theorem edges_le (n : ℕ) (s : Cube n → Bool) :
    (dir s : ℝ) * Real.log 2 ≤ (size s : ℝ) * Real.log (size s) := by
  induction n with
  | zero =>
    rw [dir_zero, Nat.cast_zero, zero_mul]
    exact natlog_nonneg _
  | succ n ih =>
    have h1 := ih (fun u => s (Fin.cons true u))
    have h0 := ih (fun u => s (Fin.cons false u))
    have hc1 : (common s : ℝ) ≤ size (fun u => s (Fin.cons true u)) := by
      exact_mod_cast common_le_true s
    have hc0 : (common s : ℝ) ≤ size (fun u => s (Fin.cons false u)) := by
      exact_mod_cast common_le_false s
    have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos one_lt_two).le
    rw [dir_succ s, size_succ s]
    push_cast
    rcases le_total (size (fun u => s (Fin.cons false u)))
      (size (fun u => s (Fin.cons true u))) with hle | hle
    · have hk := key (a := (size (fun u => s (Fin.cons true u)) : ℝ))
        (b := (size (fun u => s (Fin.cons false u)) : ℝ)) (by positivity) (by exact_mod_cast hle)
      have hcl := mul_le_mul_of_nonneg_right hc0 hlog2
      nlinarith [hk, h1, h0, hcl]
    · have hk := key (a := (size (fun u => s (Fin.cons false u)) : ℝ))
        (b := (size (fun u => s (Fin.cons true u)) : ℝ)) (by positivity) (by exact_mod_cast hle)
      rw [add_comm (size (fun u => s (Fin.cons false u)) : ℝ)] at hk
      have hcl := mul_le_mul_of_nonneg_right hc1 hlog2
      nlinarith [hk, h1, h0, hcl]

end HypercubeIso
