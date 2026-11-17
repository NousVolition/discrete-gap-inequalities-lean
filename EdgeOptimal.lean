import Isoperimetric

/-!
# Initial segments of the binary order are edge-optimal on the hypercube

A vertex `x : Fin n → Bool` of the `n`-cube is read as the binary number `val x`, where coordinate
`i` carries the bit of weight `2 ^ i` (coordinate `0` is the least significant bit). The set
`bin n m` consists of the vertices with `val x < m`, the first `m` vertices in binary order.

With `ones k` the number of `1` bits of `k` and `h m = ∑ k < m, ones k`:

* `dir_bin` : `dir (bin n m) = 2 * h m` for `m ≤ 2 ^ n`;
* `dir_le_two_mul_h` : `dir s ≤ 2 * h (size s)` for every vertex set `s`;
* `dir_le_dir_bin` : among all sets of `m` vertices, `bin n m` spans the most edges.

The arithmetic input is the binary-sum inequality `h a + h b + min a b ≤ h (a + b)`
(`binary_sum`), proved by strong induction on `a + b` from `h (2x) = 2 h x + x` and
`h (2x + 1) = h x + h (x + 1) + x`. The cube part is induction on `n` through the
first-coordinate split of `Isoperimetric.lean`; splitting `bin (n + 1) m` gives
`bin n (m / 2)` and `bin n ((m + 1) / 2)`, with `m / 2` edges across. (Harper; Bernstein; Hart.)
-/

open Finset

namespace HypercubeEdgeOptimal

open HypercubeIso

/-! ## The binary sum function -/

/-- Number of `1` bits in the binary expansion of `k`. -/
def ones (k : ℕ) : ℕ := (Nat.digits 2 k).sum

/-- `h m = ∑_{k < m} ones k`, the total number of `1` bits in `0, 1, …, m - 1`. -/
def h (m : ℕ) : ℕ := ∑ k ∈ range m, ones k

lemma ones_double (k : ℕ) : ones (2 * k) = ones k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [ones]
  · unfold ones
    rw [Nat.digits_def' (by norm_num) (by omega)]
    simp [Nat.mul_mod_right, Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]

lemma ones_double_add_one (k : ℕ) : ones (2 * k + 1) = ones k + 1 := by
  unfold ones
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  rw [h1, h2, List.sum_cons]
  omega

lemma h_zero : h 0 = 0 := by simp [h]

lemma h_one : h 1 = 0 := by simp [h, ones]

lemma h_succ (m : ℕ) : h (m + 1) = h m + ones m := by
  simp [h, Finset.sum_range_succ]

lemma h_double (x : ℕ) : h (2 * x) = 2 * h x + x := by
  induction x with
  | zero => simp [h]
  | succ x ih =>
    rw [show 2 * (x + 1) = 2 * x + 1 + 1 by ring, h_succ, h_succ, ih, h_succ,
      ones_double, ones_double_add_one]
    ring

lemma h_double_add_one (x : ℕ) : h (2 * x + 1) = h x + h (x + 1) + x := by
  rw [h_succ, h_double, ones_double, h_succ]
  ring

/-- `h m = h (m / 2) + h ((m + 1) / 2) + m / 2`. -/
lemma h_split (m : ℕ) : h m = h (m / 2) + h ((m + 1) / 2) + m / 2 := by
  rcases Nat.even_or_odd' m with ⟨x, rfl | rfl⟩
  · rw [h_double, show (2 * x + 1) / 2 = x by omega, show 2 * x / 2 = x by omega]
    ring
  · rw [h_double_add_one, show (2 * x + 1) / 2 = x by omega,
      show (2 * x + 1 + 1) / 2 = x + 1 by omega]

/-- **Binary-sum inequality.** `h a + h b + min a b ≤ h (a + b)` for all `a b`. -/
theorem binary_sum (a b : ℕ) : h a + h b + min a b ≤ h (a + b) := by
  induction hs : a + b using Nat.strong_induction_on generalizing a b with
  | _ s ih =>
    subst hs
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [h_zero]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [h_zero]
    rcases Nat.even_or_odd' a with ⟨x, rfl | rfl⟩ <;>
      rcases Nat.even_or_odd' b with ⟨y, rfl | rfl⟩
    · -- even, even
      have i1 := ih (x + y) (by omega) x y rfl
      rw [show 2 * x + 2 * y = 2 * (x + y) by ring, h_double, h_double, h_double]
      have : min (2 * x) (2 * y) = 2 * min x y := by omega
      omega
    · -- even, odd
      have i1 := ih (x + y) (by omega) x y rfl
      have i2 := ih (x + (y + 1)) (by omega) x (y + 1) rfl
      rw [show x + (y + 1) = x + y + 1 by ring] at i2
      rw [show 2 * x + (2 * y + 1) = 2 * (x + y) + 1 by ring, h_double, h_double_add_one,
        h_double_add_one]
      have : min (2 * x) (2 * y + 1) ≤ min x y + min x (y + 1) := by omega
      omega
    · -- odd, even
      have i1 := ih (x + y) (by omega) x y rfl
      have i2 := ih (x + 1 + y) (by omega) (x + 1) y rfl
      rw [show x + 1 + y = x + y + 1 by ring] at i2
      rw [show 2 * x + 1 + 2 * y = 2 * (x + y) + 1 by ring, h_double, h_double_add_one,
        h_double_add_one]
      have : min (2 * x + 1) (2 * y) ≤ min x y + min (x + 1) y := by omega
      omega
    · -- odd, odd
      have i1 := ih (x + (y + 1)) (by omega) x (y + 1) rfl
      have i2 := ih (x + 1 + y) (by omega) (x + 1) y rfl
      rw [show x + (y + 1) = x + y + 1 by ring] at i1
      rw [show x + 1 + y = x + y + 1 by ring] at i2
      rw [show 2 * x + 1 + (2 * y + 1) = 2 * (x + y + 1) by ring, h_double, h_double_add_one,
        h_double_add_one]
      have : min (2 * x + 1) (2 * y + 1) ≤ min x (y + 1) + min (x + 1) y + 1 := by omega
      omega

/-! ## Binary value and initial segments -/

/-- Binary value of a vertex: coordinate `i` is the bit of weight `2 ^ i`. -/
def val : {n : ℕ} → Cube n → ℕ
  | 0, _ => 0
  | _ + 1, x => (if x 0 then 1 else 0) + 2 * val (Fin.tail x)

lemma val_cons {n : ℕ} (b : Bool) (u : Cube n) :
    val (Fin.cons b u : Cube (n + 1)) = (if b then 1 else 0) + 2 * val u := by
  simp [val, Fin.tail_cons]

/-- The binary value is `∑ i, [x i] 2 ^ i`. -/
lemma val_eq_sum {n : ℕ} (x : Cube n) : val x = ∑ i, if x i then 2 ^ (i : ℕ) else 0 := by
  induction n with
  | zero => simp [val]
  | succ n ih =>
    rw [val, ih, Fin.sum_univ_succ, Finset.mul_sum]
    have hs : ∀ i : Fin n, 2 * (if Fin.tail x i = true then 2 ^ (i : ℕ) else 0)
        = if x i.succ = true then 2 ^ ((i.succ : Fin (n + 1)) : ℕ) else 0 := by
      intro i
      by_cases hx : x i.succ = true <;> simp [Fin.tail, hx, pow_succ, mul_comm]
    simp only [hs]
    simp

/-- The first `m` vertices in binary order. -/
def bin (n m : ℕ) : Cube n → Bool := fun x => decide (val x < m)

lemma bin_true (n m : ℕ) :
    (fun u => bin (n + 1) m (Fin.cons true u)) = bin n (m / 2) := by
  funext u
  simp only [bin, val_cons, ite_true, decide_eq_decide]
  omega

lemma bin_false (n m : ℕ) :
    (fun u => bin (n + 1) m (Fin.cons false u)) = bin n ((m + 1) / 2) := by
  funext u
  simp only [bin, val_cons]
  simp only [Bool.false_eq_true, ite_false, zero_add, decide_eq_decide]
  omega

lemma common_bin (n m : ℕ) : common (bin (n + 1) m) = size (bin n (m / 2)) := by
  unfold common size
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have ht := congrFun (bin_true n m) u
  have hf := congrFun (bin_false n m) u
  rw [ht, hf]
  simp only [bin, decide_eq_true_eq]
  by_cases hu : val u < m / 2
  · have hu' : val u < (m + 1) / 2 := by omega
    simp [hu, hu']
  · simp [hu]

lemma size_le {n : ℕ} (s : Cube n → Bool) : size s ≤ 2 ^ n := by
  unfold size
  calc ∑ x, (if s x then 1 else 0) ≤ ∑ _x : Cube n, 1 :=
        Finset.sum_le_sum (fun x _ => by split_ifs <;> simp)
    _ = 2 ^ n := by simp

lemma size_bin (n m : ℕ) : size (bin n m) = min m (2 ^ n) := by
  induction n generalizing m with
  | zero =>
    unfold size bin
    by_cases hm : 0 < m <;> simp [val, hm] <;> omega
  | succ n ih =>
    rw [size_succ, bin_true, bin_false, ih, ih, pow_succ]
    omega

/-- `bin n m` has exactly `m` vertices when `m ≤ 2 ^ n`. -/
lemma size_bin_of_le {n m : ℕ} (hm : m ≤ 2 ^ n) : size (bin n m) = m := by
  rw [size_bin]
  omega

/-- **Value of the optimum.** For `m ≤ 2 ^ n`, `dir (bin n m) = 2 * h m`. -/
theorem dir_bin (n m : ℕ) (hm : m ≤ 2 ^ n) : dir (bin n m) = 2 * h m := by
  induction n generalizing m with
  | zero =>
    rw [dir_zero]
    interval_cases m <;> simp [h_zero, h_one]
  | succ n ih =>
    rw [pow_succ] at hm
    rw [dir_succ, bin_true, bin_false, common_bin, ih (m / 2) (by omega),
      ih ((m + 1) / 2) (by omega), size_bin_of_le (by omega), h_split m]
    ring

/-- Every vertex set spans at most `h (size s)` edges: `dir s ≤ 2 * h (size s)`. -/
theorem dir_le_two_mul_h {n : ℕ} (s : Cube n → Bool) : dir s ≤ 2 * h (size s) := by
  induction n with
  | zero => rw [dir_zero]; exact Nat.zero_le _
  | succ n ih =>
    have h1 := ih (fun u => s (Fin.cons true u))
    have h0 := ih (fun u => s (Fin.cons false u))
    have c1 := common_le_true s
    have c0 := common_le_false s
    have hb := binary_sum (size (fun u => s (Fin.cons true u)))
      (size (fun u => s (Fin.cons false u)))
    rw [dir_succ, size_succ]
    have : common s ≤ min (size (fun u => s (Fin.cons true u)))
        (size (fun u => s (Fin.cons false u))) := le_min c1 c0
    omega

/-- **Initial segments of the binary order are edge-optimal.** Among all sets of `m` vertices of the
`n`-cube, the first `m` vertices in binary order span the most edges. -/
theorem dir_le_dir_bin {n m : ℕ} (s : Cube n → Bool) (hs : size s = m) :
    dir s ≤ dir (bin n m) := by
  rw [dir_bin n m (hs ▸ size_le s)]
  exact hs ▸ dir_le_two_mul_h s

/-- The maximum number of ordered adjacent pairs over sets of `m ≤ 2 ^ n` vertices is `2 * h m`,
attained by `bin n m`. -/
theorem max_dir_eq {n m : ℕ} (hm : m ≤ 2 ^ n) :
    size (bin n m) = m ∧ dir (bin n m) = 2 * h m ∧
      ∀ s : Cube n → Bool, size s = m → dir s ≤ 2 * h m :=
  ⟨size_bin_of_le hm, dir_bin n m hm, fun s hs => hs ▸ dir_le_two_mul_h s⟩

end HypercubeEdgeOptimal
