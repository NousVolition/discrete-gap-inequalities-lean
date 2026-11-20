import ConwayPairs

/-! # Coordinate moments of finite Leech lattice shells

For the shortest axis (4, −4, 0, …), the dot product with x is four times
the difference of its first two coordinates. -/
namespace LeechShellMoments

open LeechLattice LeechMinimal LeechSymmetry ConwayMoves ConwayIncidence GolayMathieu Finset

abbrev Shell (m : ℤ) := {x : Lattice // normSq x.val = m}

def onShell {m : ℤ} (g : Aut) : Shell m ≃ Shell m :=
  Equiv.subtypeEquiv g.val fun x => by
    change normSq x.val = m ↔ normSq (g x).val = m
    rw [map_norm]

abbrev coord {m : ℤ} (x : Shell m) (i : Point) : ℤ := x.val.val i

def diff {m : ℤ} (x : Shell m) : ℤ := coord x 0 - coord x 1

variable (m : ℤ) [Fintype (Shell m)]

private noncomputable def powerSum (n : ℕ) (i : Point) : ℤ := ∑ x : Shell m, coord x i ^ n

private noncomputable def mixed (i j : Point) : ℤ := ∑ x : Shell m, coord x i ^ 2 * coord x j ^ 2

private theorem sum_power (n : ℕ) (i : Point) :
    (∑ x : Shell m, coord x i ^ n) = powerSum m n i := rfl

private theorem sum_mixed (i j : Point) :
    (∑ x : Shell m, coord x i ^ 2 * coord x j ^ 2) = mixed m i j := rfl

private theorem same_power (n : ℕ) (i : Point) : powerSum m n i = powerSum m n 0 := by
  obtain ⟨j, hj⟩ := exists_ne i
  obtain ⟨g, hg⟩ := move_indices i j hj false
  let f := fun x : Shell m => coord x 0 ^ n
  calc
    _ = ∑ x : Shell m, f (onShell g x) := by
      apply sum_congr rfl
      intro x _
      change coord x i ^ n = (g x.val).val 0 ^ n
      rw [(hg x.val).1]
    _ = _ := Equiv.sum_comp (onShell g) f

private theorem same_mixed (i j : Point) (h : j ≠ i) : mixed m i j = mixed m 0 1 := by
  obtain ⟨g, hg⟩ := move_indices i j h false
  let f := fun x : Shell m => coord x 0 ^ 2 * coord x 1 ^ 2
  calc
    _ = ∑ x : Shell m, f (onShell g x) := by
      apply sum_congr rfl
      intro x _
      change _ = (g x.val).val 0 ^ 2 * (g x.val).val 1 ^ 2
      rw [(hg x.val).1, (hg x.val).2]
      rfl
    _ = _ := Equiv.sum_comp (onShell g) f

private theorem one_square : 24 * powerSum m 2 0 = m * Fintype.card (Shell m) := by
  have all : (∑ i : Point, powerSum m 2 i) = m * Fintype.card (Shell m) := by
    unfold powerSum
    rw [sum_comm]
    have hn (x : Shell m) : ∑ i, coord x i ^ 2 = m := x.property
    simp [hn, mul_comm]
  have he : (∑ i : Point, powerSum m 2 i) = 24 * powerSum m 2 0 := by
    calc
      _ = ∑ _ : Point, powerSum m 2 0 := sum_congr rfl fun i _ => same_power m 2 i
      _ = _ := by simp
  omega

private theorem mixed_row : powerSum m 4 0 + 23 * mixed m 0 1 = m * powerSum m 2 0 := by
  have diag : mixed m 0 0 = powerSum m 4 0 := by
    apply sum_congr rfl
    intro x _
    ring
  have entry (j : Point) : mixed m 0 j =
      (if j = 0 then powerSum m 4 0 - mixed m 0 1 else 0) + mixed m 0 1 := by
    by_cases hj : j = 0
    · simp [hj, diag]
    · simp [hj, same_mixed m 0 j hj]
  have row : (∑ j : Point, mixed m 0 j) = powerSum m 4 0 + 23 * mixed m 0 1 := by
    rw [sum_congr rfl (fun j _ => entry j)]
    simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [← row]
  unfold mixed
  rw [sum_comm]
  have hn (x : Shell m) : (∑ j, coord x j ^ 2) = m := x.property
  simp only [← mul_sum, hn, ← sum_mul, powerSum]
  ring

private def signedFour (b c d : Bool) (x : Shell m) : ℤ :=
  coord x 0 - twoSign b (coord x 1) - twoSign c (coord x 2) - twoSign d (coord x 3)

-- The four-coordinate lattice move turns this signed sum into twice one coordinate.
private theorem signed_fourth (b c d : Bool) :
    (∑ x : Shell m, signedFour m b c d x ^ 4) = 16 * powerSum m 4 0 := by
  obtain ⟨w, hw⟩ := four_signs ![false, b, c, d]
  let g := LeechSextet.symmetry * signAut w
  have at0 : w.val 0 = false := hw 0
  have at1 : w.val 1 = b := hw 1
  have at2 : w.val 2 = c := hw 2
  have at3 : w.val 3 = d := hw 3
  have twice (x : Shell m) : 2 * coord (onShell g x) 0 = signedFour m b c d x := by
    have h := first_norm_move (signAut w x.val) 0
    rw [Fin.sum_univ_four] at h
    change 2 * coord (onShell g x) 0 =
      2 * signFlip w.val x.val.val 0 - (signFlip w.val x.val.val 0 + signFlip w.val x.val.val 1 +
        signFlip w.val x.val.val 2 + signFlip w.val x.val.val 3) at h
    rw [h]
    simp only [signFlip, at0, at1, at2, at3, Bool.false_eq_true, ite_false, signedFour, twoSign, coord]
    ring
  have reindex := Equiv.sum_comp (onShell g) (fun x : Shell m => coord x 0 ^ 4)
  calc
    _ = ∑ x : Shell m, 16 * coord (onShell g x) 0 ^ 4 := by
      apply sum_congr rfl
      intro x _
      rw [← twice]
      ring
    _ = _ := by rw [← mul_sum, reindex]; rfl

-- Averaging the eight sign choices cancels the terms with odd exponents.
private theorem fourth_ratio : powerSum m 4 0 = 3 * mixed m 0 1 := by
  have expand (x : Shell m) :
      (∑ b : Bool, ∑ c : Bool, ∑ d : Bool, signedFour m b c d x ^ 4) =
      8 * (coord x 0 ^ 4 + coord x 1 ^ 4 + coord x 2 ^ 4 + coord x 3 ^ 4 +
        6 * (coord x 0 ^ 2 * coord x 1 ^ 2 + coord x 0 ^ 2 * coord x 2 ^ 2 +
             coord x 0 ^ 2 * coord x 3 ^ 2 + coord x 1 ^ 2 * coord x 2 ^ 2 +
             coord x 1 ^ 2 * coord x 3 ^ 2 + coord x 2 ^ 2 * coord x 3 ^ 2)) := by
    simp only [Fintype.sum_bool, signedFour, twoSign, Bool.false_eq_true, ite_false, ite_true]
    ring
  have h := congrArg (fun f : Shell m → ℤ => ∑ x, f x) (funext expand)
  simp only [Fintype.sum_bool, sum_add_distrib, signed_fourth, ← mul_sum,
    sum_power, sum_mixed] at h
  rw [same_power m 4 1, same_power m 4 2, same_power m 4 3, same_mixed m 0 2 (by decide),
    same_mixed m 0 3 (by decide), same_mixed m 1 2 (by decide), same_mixed m 1 3 (by decide),
    same_mixed m 2 3 (by decide)] at h
  omega

private theorem swap_sign (n : ℕ) :
    (∑ x : Shell m, (coord x 0 + coord x 1) ^ n) = ∑ x : Shell m, diff x ^ n := by
  obtain ⟨g, hg⟩ := move_indices 0 1 (by decide) true
  let f := fun x : Shell m => diff x ^ n
  calc
    _ = ∑ x : Shell m, f (onShell g x) := by
      apply sum_congr rfl
      intro x _
      change _ = ((g x.val).val 0 - (g x.val).val 1) ^ n
      rw [(hg x.val).1, (hg x.val).2]
      simp [twoSign]
    _ = _ := Equiv.sum_comp (onShell g) f

/-- The second and fourth powers of the first coordinate difference, summed over a finite shell. -/
theorem diff_moments :
    12 * (∑ x : Shell m, diff x ^ 2) = m * Fintype.card (Shell m) ∧
    52 * (∑ x : Shell m, diff x ^ 4) = m ^ 2 * Fintype.card (Shell m) := by
  have ratio := fourth_ratio m
  have row := mixed_row m
  have square := one_square m
  have expand2 (x : Shell m) :
      (coord x 0 + coord x 1)^2 + diff x ^ 2 = 2 * (coord x 0 ^ 2 + coord x 1 ^ 2) := by
    unfold diff; ring
  have expand4 (x : Shell m) :
      (coord x 0 + coord x 1)^4 + diff x ^ 4 =
      2 * (coord x 0 ^ 4 + coord x 1 ^ 4 + 6 * (coord x 0 ^ 2 * coord x 1 ^ 2)) := by
    unfold diff; ring
  have h2 := congrArg (fun f : Shell m → ℤ => ∑ x, f x) (funext expand2)
  have h4 := congrArg (fun f : Shell m → ℤ => ∑ x, f x) (funext expand4)
  simp only [sum_add_distrib, ← mul_sum, swap_sign, sum_power, sum_mixed] at h2 h4
  rw [same_power m 2 1] at h2
  rw [same_power m 4 1] at h4
  constructor
  · omega
  · have fourth : (∑ x : Shell m, diff x ^ 4) = 12 * mixed m 0 1 := by omega
    have mixed_eq : 26 * mixed m 0 1 = m * powerSum m 2 0 := by omega
    calc
      _ = 24 * (26 * mixed m 0 1) := by rw [fourth]; ring
      _ = m * (24 * powerSum m 2 0) := by rw [mixed_eq]; ring
      _ = _ := by rw [square]; ring

end LeechShellMoments
