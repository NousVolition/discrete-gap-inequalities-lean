import E8PlumbingBridge
import LeechThreeE8

/-!
# Where the little stick goes, and what cannot hold two plumbings together

The statements in Parts 1–5 come from Claude's draft.
A row of pieces is joined end to end, with one extra piece (the stick) attached to the row.
As in `E8PlumbingBridge`, each diagonal entry is `-2` and each joint has entry `1`.
In Part 1, the stick “fits” when the resulting integer matrix has determinant `1`.

* Part 1. On a row of seven, the stick fits only on the third piece from either end. The
  repository's `E8_matrix` is the stick on piece `4` (counting from `0`).
* Part 2. Mirror: reversing the row sends the stick on piece `p` to the stick on piece `6 - p`.
* Part 3. One more piece on the long end gives determinant `0`, and a second gives `-1`.
* Part 4. The cost of one plumbing: seven squared differences across the joints, plus the three
  loose ends, minus the branch piece. It is positive for every nonzero whole-number assignment.
* Part 5. Two separate plumbings stay positive. Two plumbings tied by ONE ordinary joint do not,
  for any of the 64 choices of where the joint goes.

Reading one Hug as one joint, or a Hug between two whole plumbings as glue, is a comparison.
This file does not prove that reading. The glue construction for three E₈ blocks is in
`LeechThreeE8.lean`.
-/

open Matrix Finset

namespace PlumbingStick

/-! ## Part 1. Where the stick fits -/

/-- A row of `n` pieces with one extra piece, the stick, joined to piece `p`. -/
def rowStick (n : ℕ) (p : Fin n) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j =>
    if i = j then -2
    else if (i.val + 1 = j.val ∧ j.val < n) ∨ (j.val + 1 = i.val ∧ i.val < n)
        ∨ (i.val = p.val ∧ j.val = n) ∨ (j.val = p.val ∧ i.val = n) then 1
    else 0

/-- The repository's E₈ plumbing is a row of seven with the stick on piece `4`. -/
theorem rowStick_seven_four : rowStick 7 4 = E8PlumbingBridge.E8_matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Column operations for a row with a stick. The first `n` columns have entries
`1, …, j+1` above and on the diagonal. The last column cancels the attachment
in every row except the stick's. -/
private def elimination (n : ℕ) (p : Fin n) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j =>
    if j.val < n then
      if i ≤ j then (i.val + 1 : ℕ) else 0
    else if i.val < n then
      ((min i.val p.val + 1) * (n - max i.val p.val) : ℕ)
    else (n + 1 : ℕ)

/-- Multiplying by an upper triangular matrix turns the plumbing matrix into a
lower triangular one. Both determinants on the right can be read off the diagonal. -/
private theorem det_from_elimination {k : ℕ} (A C : Matrix (Fin k) (Fin k) ℤ) (d : ℤ)
    (hC : C.IsUpperTriangular) (hAC : (A * C).IsLowerTriangular)
    (hne : (∏ i, C i i) ≠ 0) (hdiag : (∏ i, (A * C) i i) = d * ∏ i, C i i) :
    A.det = d := by
  apply mul_right_cancel₀ hne
  calc
    A.det * (∏ i, C i i) = A.det * C.det := by rw [det_of_isUpperTriangular hC]
    _ = (A * C).det := (det_mul A C).symm
    _ = d * ∏ i, C i i := (det_of_isLowerTriangular _ hAC).trans hdiag

/-- **The stick's seven possible places.** Ends give `9`, next to the ends `4`, third from
an end `1`, the middle `0`. -/
theorem stick_det :
    ∀ p : Fin 7, (rowStick 7 p).det = (![9, 4, 1, 0, 1, 4, 9] : Fin 7 → ℤ) p := by
  intro p
  apply det_from_elimination _ (elimination 7 p)
  all_goals decide +revert

/-- **The stick fits in exactly two places**, mirror images of each other. -/
theorem stick_det_eq_one_iff (p : Fin 7) : (rowStick 7 p).det = 1 ↔ p = 2 ∨ p = 4 := by
  rw [stick_det]
  decide +revert

/-! ## Part 2. The mirror -/

/-- Reverse the row of seven and leave the stick (piece `7`) where it is. -/
def flipRow (i : Fin 8) : Fin 8 := if h : i.val < 7 then ⟨6 - i.val, by omega⟩ else i

/-- The mirror place for the stick. -/
def rev (p : Fin 7) : Fin 7 := ⟨6 - p.val, by omega⟩

theorem flipRow_flipRow (i : Fin 8) : flipRow (flipRow i) = i := by
  decide +revert

set_option maxHeartbeats 1600000 in
/-- **Mirror.** The stick on piece `6 - p` is the stick on piece `p` with the row reversed. -/
theorem stick_mirror (p : Fin 7) :
    rowStick 7 (rev p) = (rowStick 7 p).submatrix flipRow flipRow := by
  ext i j
  fin_cases p <;> fin_cases i <;> fin_cases j <;> rfl

theorem stick_mirror_det (p : Fin 7) : (rowStick 7 (rev p)).det = (rowStick 7 p).det := by
  let e : Fin 8 ≃ Fin 8 := ⟨flipRow, flipRow, flipRow_flipRow, flipRow_flipRow⟩
  rw [stick_mirror]
  exact det_submatrix_equiv_self e _

/-! ## Part 3. One piece too many -/

/-- Nine pieces: the E₈ shape with one more piece on its long end. Exactly on the edge. -/
theorem nine_det : (rowStick 8 5).det = 0 := by
  apply det_from_elimination _ (elimination 8 5)
  all_goals decide

/-- Ten pieces: one more again. Past the edge. -/
theorem ten_det : (rowStick 9 6).det = -1 := by
  apply det_from_elimination _ (elimination 9 6)
  all_goals decide

/-! ## Part 4. The cost of one plumbing -/

/-- The cost of a whole-number assignment on the E₈ plumbing (positive sign convention). -/
def cost (x : Fin 8 → ℤ) : ℤ := ∑ i, ∑ j, x i * (-E8PlumbingBridge.E8_matrix i j) * x j

/-- **Cost as joints.** Seven squared differences, one per joint, plus the three loose ends
(pieces `0`, `6`, `7`), minus the branch piece (`4`). -/
theorem cost_as_joints (x : Fin 8 → ℤ) :
    cost x = (x 0 - x 1) ^ 2 + (x 1 - x 2) ^ 2 + (x 2 - x 3) ^ 2 + (x 3 - x 4) ^ 2
      + (x 4 - x 5) ^ 2 + (x 5 - x 6) ^ 2 + (x 4 - x 7) ^ 2
      + x 0 ^ 2 - x 4 ^ 2 + x 6 ^ 2 + x 7 ^ 2 := by
  simp [cost, E8PlumbingBridge.E8_matrix, Fin.sum_univ_succ]
  ring

theorem cost_even (x : Fin 8 → ℤ) : Even (cost x) := by
  refine ⟨(∑ i, x i ^ 2) - (x 0 * x 1 + x 1 * x 2 + x 2 * x 3 + x 3 * x 4
    + x 4 * x 5 + x 5 * x 6 + x 4 * x 7), ?_⟩
  rw [cost_as_joints]
  simp [Fin.sum_univ_succ]
  ring

/-- **One plumbing alone is never free.** The existing root Gram identity expresses
sixteen times the cost as a sum of squares. The determinant rules out a nonzero
assignment on which all those squares vanish. -/
theorem cost_pos (x : Fin 8 → ℤ) (hx : x ≠ 0) : 0 < cost x := by
  let B : Matrix (Fin 8) (Fin 8) ℤ := LeechThreeE8.e8Root
  have gram : B * Bᵀ = (-16 : ℤ) • E8PlumbingBridge.E8_matrix := by
    ext i j
    exact LeechThreeE8.e8_gram i j
  have hd : Bᵀ.det ≠ 0 := by
    have h := congrArg Matrix.det gram
    rw [det_mul, det_transpose, det_smul, E8PlumbingBridge.E8_det] at h
    rw [det_transpose]
    intro hz
    norm_num [hz] at h
  have nonzero : Bᵀ *ᵥ x ≠ 0 := fun h => hx (eq_zero_of_mulVec_eq_zero hd h)
  have squared : 0 < (Bᵀ *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ x) :=
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg ((Bᵀ *ᵥ x) i))
      (Ne.symm (mt dotProduct_self_eq_zero.mp nonzero))
  have energy : (Bᵀ *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ x) = 16 * cost x := by
    calc
      _ = x ⬝ᵥ ((B * Bᵀ) *ᵥ x) := by
        rw [← mulVec_mulVec, dotProduct_mulVec x B (Bᵀ *ᵥ x), mulVec_transpose B x]
      _ = 16 * cost x := by
        rw [gram, dot_mulVec_eq_sum_sum, Finset.sum_comm]
        simp only [cost, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [energy] at squared
  omega

/-- Its floor is `2`, reached by one piece alone. -/
theorem cost_ge_two (x : Fin 8 → ℤ) (hx : x ≠ 0) : 2 ≤ cost x := by
  obtain ⟨k, hk⟩ := cost_even x
  have := cost_pos x hx
  omega

theorem cost_single (i : Fin 8) : cost (Pi.single i 1) = 2 := by
  decide +revert

/-! ## Part 5. Two plumbings -/

/-- Two separate plumbings: the costs add, and nothing nonzero is free. -/
theorem two_separate_pos (x y : Fin 8 → ℤ) (h : x ≠ 0 ∨ y ≠ 0) : 0 < cost x + cost y := by
  have nonneg (z : Fin 8 → ℤ) : 0 ≤ cost z := by
    by_cases hz : z = 0
    · simp [hz, cost]
    · exact (cost_pos z hz).le
  rcases h with hx | hy
  · exact add_pos_of_pos_of_nonneg (cost_pos x hx) (nonneg y)
  · exact add_pos_of_nonneg_of_pos (nonneg x) (cost_pos y hy)

/-- **One ordinary joint cannot hold two plumbings.** Tie piece `a` of the first to piece `b`
of the second with a single joint. Then some nonzero assignment has negative cost, wherever
the joint is placed.

The same assignment works at every joint: it has cost `2` in each copy and is at least `2` on every piece. -/
theorem one_joint_breaks (a b : Fin 8) :
    ∃ x y : Fin 8 → ℤ, (x ≠ 0 ∨ y ≠ 0) ∧ cost x + cost y - 2 * (x a * y b) < 0 := by
  let w : Fin 8 → ℤ := ![2, 3, 4, 5, 6, 4, 2, 3]
  have hw : cost w = 2 := by decide
  have lower : ∀ i, 2 ≤ w i := by decide
  refine ⟨w, w, Or.inl ?_, ?_⟩
  · intro hz
    have := congrFun hz 0
    change (2 : ℤ) = 0 at this
    contradiction
  · rw [hw]
    have hab : (2 : ℤ) * 2 ≤ w a * w b :=
      mul_le_mul (lower a) (lower b) (by decide) (by linarith [lower a])
    linarith

end PlumbingStick
