import PlumbingStick

/-!
# Who pays, and how close the help is

The statements in Parts 1–6 come from Claude's draft.

Picture, continuing `PlumbingStick.lean`: a row of `n` pieces with one stick on piece `p`.
Each piece brings 2 shares and each joint takes 1 from each of its two ends. So a loose end has
1 to spare, a piece with two joints is even, and the branch piece is 1 short.

* Part 1. The total spare is always 2, wherever the stick is.
* Part 2. The cost is the squared differences across the joints plus each piece's own share.
* Part 3. One formula gives the determinant for every row length and every stick place.
* Part 4. "Help": the three arms have lengths `p`, `n - 1 - p` and `1`. An arm of length `L`
  helps by `1 / (L + 1)`. The margin is positive exactly when the three helps add to more
  than 1. For the repository's E₈ the integer margin is `1`, and the helps exceed 1 by `1/30`.
* Part 5. The edge and beyond: explicit assignments with cost `0` for the stick in the middle
  of seven and for nine pieces, and with negative cost for ten pieces.
* Part 6. On a row of seven, the plumbing is never free exactly when the stick is not in
  the middle.

The rule in Part 4 is known mathematics. Reading it as "help" for
the Hug is a comparison and is not proved here.
-/

open Matrix Finset

namespace PlumbingHelp

open PlumbingStick

/-! ## Part 1. Shares -/

/-- The number of joints at piece `i`. -/
def joints (n : ℕ) (p : Fin n) (i : Fin (n + 1)) : ℤ :=
  ∑ j, if j ≠ i ∧ rowStick n p i j = 1 then 1 else 0

/-- What piece `i` has left after paying one share into each of its joints. -/
def spare (n : ℕ) (p : Fin n) (i : Fin (n + 1)) : ℤ := 2 - joints n p i

private def bond {n : ℕ} (p : Fin n) (i j : Fin (n + 1)) : ℤ :=
  if j ≠ i ∧ rowStick n p i j = 1 then 1 else 0

private theorem bond_symm {n : ℕ} (p : Fin n) (i j : Fin (n + 1)) : bond p i j = bond p j i := by
  simp only [bond, rowStick, of_apply, Fin.ext_iff]
  split_ifs <;> omega

private theorem entry_eq {n : ℕ} (p : Fin n) (i j : Fin (n + 1)) :
    rowStick n p i j = (if j = i then -2 else 0) + bond p i j := by
  simp only [bond, rowStick, of_apply, Fin.ext_iff]
  split_ifs <;> omega

private theorem bond_path {n : ℕ} (p i j : Fin n) :
    bond p i.castSucc j.castSucc =
      (if j.val + 1 = i.val then 1 else 0) + (if j.val = i.val + 1 then 1 else 0) := by
  have hi := i.isLt
  have hj := j.isLt
  have vi : i.castSucc.val = i.val := rfl
  have vj : j.castSucc.val = j.val := rfl
  simp only [bond, rowStick, of_apply, Fin.ext_iff, Fin.val_castSucc]
  split_ifs <;> omega

private theorem bond_last {n : ℕ} (p i : Fin n) :
    bond p i.castSucc (Fin.last n) = if i = p then 1 else 0 := by
  have hn : ¬ n + 1 = i.val := by omega
  have hi : ¬ i.val = n := by omega
  simp [bond, rowStick, Fin.ext_iff, hn, hi, Ne.symm (Fin.castSucc_ne_last i)]

/-- Sum along the joints of a row piece, including the extra stick at the attachment site. -/
private theorem neighbor_sum {n : ℕ} (p i : Fin n) (x : Fin (n + 1) → ℤ) :
    ∑ j, bond p i.castSucc j * x j =
      (if h : 0 < i.val then x ⟨i.val - 1, by omega⟩ else 0) +
      (if h : i.val + 1 < n then x ⟨i.val + 1, by omega⟩ else 0) +
      (if i = p then x (Fin.last n) else 0) := by
  rw [Fin.sum_univ_castSucc]
  simp_rw [bond_path, add_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_add_distrib, bond_last, ite_mul, one_mul, zero_mul]
  congr 1
  apply congrArg₂ (· + ·)
  · split_ifs with h
    · let k : Fin n := ⟨i.val - 1, by omega⟩
      have he (j : Fin n) : j.val + 1 = i.val ↔ j = k := by simp [k, Fin.ext_iff]; omega
      simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rfl
    · simp [show ∀ j : Fin n, ¬ j.val + 1 = i.val by intro j; omega]
  · split_ifs with h
    · let k : Fin n := ⟨i.val + 1, h⟩
      have he (j : Fin n) : j.val = i.val + 1 ↔ j = k := by simp [k, Fin.ext_iff]
      simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rfl
    · simp [show ∀ j : Fin n, ¬ j.val = i.val + 1 by intro j; omega]

private theorem stick_sum {n : ℕ} (p : Fin n) (x : Fin (n + 1) → ℤ) :
    ∑ j, bond p (Fin.last n) j * x j = x p.castSucc := by
  rw [Fin.sum_univ_castSucc]
  simp_rw [fun (j : Fin n) => bond_symm p (Fin.last n) j.castSucc, bond_last, ite_mul,
    one_mul, zero_mul]
  simp [bond]

/-- **The total spare is always 2.** Nobody underpays overall, wherever the stick is. -/
theorem total_spare (n : ℕ) (p : Fin n) : ∑ i, spare n p i = 2 := by
  cases n with
  | zero => exact p.elim0
  | succ m =>
    have each (i : Fin (m + 1)) : spare (m + 1) p i.castSucc =
        (if i = 0 then 1 else 0) + (if i = Fin.last m then 1 else 0) -
        (if i = p then 1 else 0) := by
      have h := neighbor_sum p i (fun _ => 1)
      simp only [mul_one] at h
      change 2 - (∑ j, bond p i.castSucc j) = _
      rw [h]
      simp only [Fin.ext_iff, Fin.val_zero, Fin.val_last]
      split_ifs <;> omega
    have hlast := stick_sum p (fun _ => 1)
    simp only [mul_one] at hlast
    rw [Fin.sum_univ_castSucc]
    simp_rw [each]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    change _ + (2 - (∑ j, bond p (Fin.last (m + 1)) j)) = 2
    simp [hlast]

/-! ## Part 2. Cost as joints, for every row and every stick place -/

/-- The cost of a whole-number assignment (positive sign convention). -/
def stickCost (n : ℕ) (p : Fin n) (x : Fin (n + 1) → ℤ) : ℤ :=
  ∑ i, ∑ j, x i * (-(rowStick n p) i j) * x j

/-- Twice the cost is twice the own shares plus the squared difference across every joint,
each joint counted once from each end. -/
theorem stickCost_as_joints (n : ℕ) (p : Fin n) (x : Fin (n + 1) → ℤ) :
    2 * stickCost n p x =
      2 * ∑ i, spare n p i * x i ^ 2
        + ∑ i, ∑ j, if j ≠ i ∧ rowStick n p i j = 1 then (x i - x j) ^ 2 else 0 := by
  have cost_row (i : Fin (n + 1)) :
      ∑ j, x i * (-rowStick n p i j) * x j =
        2 * x i ^ 2 - ∑ j, bond p i j * x i * x j := by
    calc
      _ = ∑ j, ((if j = i then 2 * x i ^ 2 else 0) - bond p i j * x i * x j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [entry_eq]
        by_cases h : j = i
        · subst j; simp; ring
        · simp only [h, ite_false, zero_add, zero_sub]
          ring
      _ = _ := by simp [Finset.sum_sub_distrib]
  have out_sq : (∑ i, ∑ j, bond p i j * x i ^ 2) = ∑ i, joints n p i * x i ^ 2 := by
    simp only [joints, ← Finset.sum_mul, bond]
  have in_sq : (∑ i, ∑ j, bond p i j * x j ^ 2) = ∑ i, joints n p i * x i ^ 2 := by
    rw [Finset.sum_comm]
    simpa only [bond_symm p] using out_sq
  have diff (i j : Fin (n + 1)) :
      (if j ≠ i ∧ rowStick n p i j = 1 then (x i - x j)^2 else 0) =
        bond p i j * x i^2 + bond p i j * x j^2 - 2 * (bond p i j * x i * x j) := by
    unfold bond
    split_ifs <;> ring
  simp only [stickCost, cost_row, spare, sub_mul, diff, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, out_sq, in_sq]
  ring

/-- On the repository's E₈ this is the cost already used in `PlumbingStick`. -/
theorem stickCost_seven_four (x : Fin 8 → ℤ) : stickCost 7 4 x = PlumbingStick.cost x := by
  simp only [stickCost, PlumbingStick.cost, rowStick_seven_four]

/-! ## Part 3. One formula for every determinant -/

/-- The margin: positive means the plumbing holds, zero is the edge, negative means it breaks. -/
def margin (n : ℕ) (p : Fin n) : ℤ := 2 * ((n : ℤ) + 1) - ((p.val : ℤ) + 1) * ((n : ℤ) - p.val)

/-- Extend a path column by its value on the stick. The path uses positions 1 through n. -/
private def pathColumn (n : ℕ) (u : ℕ → ℤ) (t : ℤ) (j : Fin (n + 1)) : ℤ :=
  if j.val < n then u (j.val + 1) else t

private theorem matrix_row {n : ℕ} (p : Fin n) (i : Fin (n + 1)) (x : Fin (n + 1) → ℤ) :
    ∑ j, rowStick n p i j * x j = -2 * x i + ∑ j, bond p i j * x j := by
  simp_rw [entry_eq p i, add_mul, ite_mul, zero_mul]
  simp [Finset.sum_add_distrib]

/-- On the row the matrix takes a second difference, with a contribution from the stick at p. -/
private theorem path_action {n : ℕ} (p i : Fin n) (u : ℕ → ℤ) (t : ℤ)
    (h₀ : u 0 = 0) (hₙ : u (n + 1) = 0) :
    ∑ j, rowStick n p i.castSucc j * pathColumn n u t j =
      u i.val - 2 * u (i.val + 1) + u (i.val + 2) + (if i = p then t else 0) := by
  rw [matrix_row, neighbor_sum]
  have left :
      (if h : 0 < i.val then pathColumn n u t ⟨i.val - 1, by omega⟩ else 0) = u i.val := by
    split_ifs with h
    · simp [pathColumn, show i.val - 1 < n by omega, Nat.sub_add_cancel h]
    · simpa [show i.val = 0 by omega] using h₀.symm
  have right :
      (if h : i.val + 1 < n then pathColumn n u t ⟨i.val + 1, by omega⟩ else 0) = u (i.val + 2) := by
    split_ifs with h
    · simp [pathColumn, h]
    · simpa [show i.val + 2 = n + 1 by omega] using hₙ.symm
  rw [left, right]
  simp [pathColumn, i.isLt]
  ring

private def ramp (j k : ℕ) : ℤ := if k ≤ j + 1 then k else 0

/-- A piecewise linear column whose second difference at the attachment cancels the stick. -/
private def green (n p k : ℕ) : ℤ :=
  (k : ℤ) * ((n : ℤ) - p) - ((n : ℤ) + 1) * ((k - (p + 1) : ℕ) : ℤ)

private theorem green_end {n : ℕ} (p : Fin n) : green n p.val (n + 1) = 0 := by
  have h : (((n + 1) - (p.val + 1) : ℕ) : ℤ) = (n : ℤ) - p.val := by omega
  simp only [green, h, Nat.cast_add, Nat.cast_one, sub_self]

private theorem green_jump {n : ℕ} (p i : Fin n) :
    green n p.val i.val - 2 * green n p.val (i.val + 1) + green n p.val (i.val + 2) +
      (if i = p then ((n : ℤ) + 1) else 0) = 0 := by
  have hinge : (((i.val - (p.val + 1) : ℕ) : ℤ) -
      2 * (((i.val + 1) - (p.val + 1) : ℕ) : ℤ) +
      (((i.val + 2) - (p.val + 1) : ℕ) : ℤ)) = if i = p then 1 else 0 := by
    split_ifs <;> simp_all only [Fin.ext_iff] <;> omega
  unfold green
  push_cast at hinge ⊢
  split_ifs at * <;> linear_combination -((n : ℤ) + 1) * hinge

/-- The first n columns are linear ramps. The last column eliminates the attachment. -/
private def columns {n : ℕ} (p : Fin n) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j => if j.val < n then pathColumn n (ramp j.val) 0 i
    else pathColumn n (green n p.val) ((n : ℤ) + 1) i

private theorem columns_upper {n : ℕ} (p : Fin n) : (columns p).IsUpperTriangular := by
  intro i j h
  change j.val < i.val at h
  have hj : j.val < n := by omega
  simp [columns, hj, pathColumn, ramp, show ¬ i ≤ j from not_le_of_gt h]

private theorem path_product {n : ℕ} (p i j : Fin n) :
    (rowStick n p * columns p) i.castSucc j.castSucc =
      ramp j.val i.val - 2 * ramp j.val (i.val + 1) + ramp j.val (i.val + 2) := by
  simpa [Matrix.mul_apply, columns, j.isLt] using
    path_action p i (ramp j.val) 0 (by simp [ramp]) (by simp [ramp, show ¬ n + 1 ≤ j.val + 1 by omega])

private theorem last_column {n : ℕ} (p i : Fin n) :
    (rowStick n p * columns p) i.castSucc (Fin.last n) = 0 := by
  simpa [Matrix.mul_apply, columns] using
    (path_action p i (green n p.val) ((n : ℤ) + 1) (by simp [green]) (green_end p)).trans (green_jump p i)

private theorem product_lower {n : ℕ} (p : Fin n) : (rowStick n p * columns p).IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  obtain ⟨a, rfl⟩ : ∃ a : Fin n, a.castSucc = i := ⟨⟨i.val, by omega⟩, rfl⟩
  by_cases hj : j.val < n
  · let b : Fin n := ⟨j.val, hj⟩
    change (rowStick n p * columns p) a.castSucc b.castSucc = 0
    rw [path_product]
    have hab : a.val < b.val := h
    simp [ramp, show a.val ≤ b.val + 1 by omega, show a.val + 1 ≤ b.val + 1 by omega,
      show a.val + 2 ≤ b.val + 1 by omega]
    ring
  · have e : j = Fin.last n := Fin.ext (by simp; omega)
    subst j
    exact last_column p a

private theorem path_diagonal {n : ℕ} (p i : Fin n) :
    (rowStick n p * columns p) i.castSucc i.castSucc = -((i.val : ℤ) + 2) := by
  rw [path_product]
  simp [ramp]
  ring

private theorem last_diagonal {n : ℕ} (p : Fin n) :
    (rowStick n p * columns p) (Fin.last n) (Fin.last n) = -margin n p := by
  simp only [Matrix.mul_apply, columns, of_apply, Fin.val_last, lt_irrefl, ite_false]
  rw [matrix_row, stick_sum]
  simp [pathColumn, green, margin, p.isLt]
  ring

/-- **Every stick, every row length.** -/
theorem rowStick_det (n : ℕ) (p : Fin n) :
    (rowStick n p).det = (-1) ^ (n + 1) * margin n p := by
  have cd (i : Fin n) : columns p i.castSucc i.castSucc = (i.val : ℤ) + 1 := by
    simp [columns, pathColumn, ramp, i.isLt]
  have cl : columns p (Fin.last n) (Fin.last n) = (n : ℤ) + 1 := by simp [columns, pathColumn]
  have detC : (columns p).det = (∏ i : Fin n, ((i.val : ℤ) + 1)) * ((n : ℤ) + 1) := by
    rw [Matrix.det_of_isUpperTriangular (columns_upper p), Fin.prod_univ_castSucc, cl]
    simp_rw [cd]
  have positive : 0 < (columns p).det := by
    rw [detC]
    exact mul_pos (Finset.prod_pos fun _ _ => by positivity) (by positivity)
  have shift : (∏ i : Fin n, ((i.val : ℤ) + 2)) = (columns p).det := by
    rw [detC]
    let f (i : Fin (n + 1)) : ℤ := (i.val : ℤ) + 1
    simpa [f, add_assoc] using (Fin.prod_univ_succ f).symm.trans (Fin.prod_univ_castSucc f)
  apply mul_right_cancel₀ positive.ne'
  rw [← Matrix.det_mul, Matrix.det_of_isLowerTriangular _ (product_lower p), Fin.prod_univ_castSucc,
    last_diagonal]
  simp_rw [path_diagonal]
  rw [Finset.prod_neg, shift, Finset.card_univ, Fintype.card_fin, pow_succ]
  ring

/-! ## Part 4. Help from the three arms -/

/-- The three helps: the arm before the branch piece, the arm after it, and the stick. -/
def help (n : ℕ) (p : Fin n) : ℚ := 1 / ((p.val : ℚ) + 1) + 1 / ((n : ℚ) - p.val) + 1 / 2

/-- The margin written with the helps. -/
theorem margin_eq_help (n : ℕ) (p : Fin n) :
    (margin n p : ℚ) = 2 * ((p.val : ℚ) + 1) * ((n : ℚ) - p.val) * (help n p - 1) := by
  have hp : (p.val : ℚ) < n := by exact_mod_cast p.isLt
  have h₁ : (p.val : ℚ) + 1 ≠ 0 := by positivity
  have h₂ : (n : ℚ) - p.val ≠ 0 := (sub_pos.mpr hp).ne'
  unfold margin help
  push_cast
  field_simp
  ring

/-- **The plumbing holds exactly when the three helps add to more than 1.** -/
theorem margin_pos_iff_help (n : ℕ) (p : Fin n) : 0 < margin n p ↔ 1 < help n p := by
  have hp : (p.val : ℚ) < n := by exact_mod_cast p.isLt
  have positive : 0 < 2 * ((p.val : ℚ) + 1) * ((n : ℚ) - p.val) :=
    mul_pos (by positivity) (sub_pos.mpr hp)
  have h : (0 : ℚ) < (margin n p : ℚ) ↔ 1 < help n p := by
    rw [margin_eq_help, mul_pos_iff_of_pos_left positive, sub_pos]
  exact_mod_cast h

/-- The edge: the helps add to exactly 1. -/
theorem margin_zero_iff_help (n : ℕ) (p : Fin n) : margin n p = 0 ↔ help n p = 1 := by
  have hp : (p.val : ℚ) < n := by exact_mod_cast p.isLt
  have positive : 0 < 2 * ((p.val : ℚ) + 1) * ((n : ℚ) - p.val) :=
    mul_pos (by positivity) (sub_pos.mpr hp)
  have h : (margin n p : ℚ) = 0 ↔ help n p = 1 := by
    rw [margin_eq_help, mul_eq_zero, or_iff_right positive.ne', sub_eq_zero]
  exact_mod_cast h

/-- **E₈ holds by one thirtieth.** Its helps are `1/5`, `1/3` and `1/2`. -/
theorem e8_help : help 7 4 - 1 = 1 / 30 := by norm_num [help, Fin.isValue]

/-! ## Part 5. The edge and beyond -/

/-- Stick in the middle of seven: a nonzero assignment that costs nothing. -/
theorem free_ride_middle : stickCost 7 3 ![1, 2, 3, 4, 3, 2, 1, 2] = 0 := by decide

/-- Nine pieces: a nonzero assignment that costs nothing. -/
theorem free_ride_nine : stickCost 8 5 ![1, 2, 3, 4, 5, 6, 4, 2, 3] = 0 := by decide

/-- Ten pieces: an assignment with negative cost. -/
theorem ten_breaks : stickCost 9 6 ![1, 2, 4, 6, 8, 10, 12, 8, 4, 6] = -2 := by decide

/-! ## Part 6. Seven in a row -/

/-- In the first seven rows, completing a square clears the next joint and the stick.
The eighth row keeps the value on the stick. -/
private def squareRows (p : Fin 7) : Matrix (Fin 8) (Fin 8) ℤ := Matrix.of fun i j =>
  if i = j then (if i.val < 7 then (i.val : ℤ) + 2 else 1)
  else if j.val < 7 ∧ j.val = i.val + 1 then -((i.val : ℤ) + 1)
  else if j.val = 7 ∧ p.val ≤ i.val then -((p.val : ℤ) + 1)
  else 0

/-- Multiplication by 840 clears the denominators of the eight square coefficients. -/
private def squareWeight (p : Fin 7) : Fin 8 → ℤ :=
  ![420, 140, 70, 42, 28, 20, 15, 105 * margin 7 p]

private theorem squareWeight_pos : ∀ p : Fin 7, p ≠ 3 → ∀ i, 0 < squareWeight p i := by
  decide

private theorem seven_gram (p : Fin 7) :
    (squareRows p)ᵀ * (diagonal (squareWeight p) * squareRows p) = (-840 : ℤ) • rowStick 7 p := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  decide +revert

private theorem seven_pos {p : Fin 7} (hp : p ≠ 3) (x : Fin 8 → ℤ) (hx : x ≠ 0) :
    0 < stickCost 7 p x := by
  let B := squareRows p
  let d := squareWeight p
  have hB : B.IsUpperTriangular := by decide +revert
  have hdB : B.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hB]
    decide +revert
  have dw : ∀ i, 0 < d i := squareWeight_pos p hp
  have gram : Bᵀ * (diagonal d * B) = (-840 : ℤ) • rowStick 7 p := seven_gram p
  let y := B *ᵥ x
  have hy : y ≠ 0 := fun h => hx (Matrix.eq_zero_of_mulVec_eq_zero hdB h)
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra! all
    exact hy (funext all)
  have energy : 0 < ∑ i, d i * (y i)^2 :=
    Finset.sum_pos' (fun j _ => mul_nonneg (dw j).le (sq_nonneg _))
      ⟨i, Finset.mem_univ _, mul_pos (dw i) (sq_pos_of_ne_zero hi)⟩
  have identity : (∑ i, d i * (y i)^2) = 840 * stickCost 7 p x := by
    calc
      _ = y ⬝ᵥ (diagonal d *ᵥ y) := by
        simp only [dotProduct, Matrix.mulVec_diagonal]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = x ⬝ᵥ ((Bᵀ * (diagonal d * B)) *ᵥ x) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec x Bᵀ, Matrix.vecMul_transpose]
      _ = 840 * stickCost 7 p x := by
        rw [gram, dot_mulVec_eq_sum_sum, Finset.sum_comm]
        simp only [stickCost, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [identity] at energy
  omega

/-- **On a row of seven, the plumbing is never free exactly when the stick is not in the
middle.** -/
theorem seven_never_free_iff (p : Fin 7) :
    (∀ x : Fin 8 → ℤ, x ≠ 0 → 0 < stickCost 7 p x) ↔ p ≠ 3 := by
  refine ⟨?_, seven_pos⟩
  intro h e
  subst p
  have hx : (![1, 2, 3, 4, 3, 2, 1, 2] : Fin 8 → ℤ) ≠ 0 := by decide
  have pos := h _ hx
  rw [free_ride_middle] at pos
  exact (lt_irrefl _ pos)

end PlumbingHelp
