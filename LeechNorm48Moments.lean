import LeechNorm48
import ConwayPairs

/-! # Second and fourth powers on the squared-length-48 shell

For the shortest axis (4, −4, 0, …), the dot product with x is four times
the difference of its first two coordinates.
-/
namespace LeechNorm48Layers

open LeechLattice LeechMinimal LeechSymmetry ConwayMoves ConwayIncidence GolayMathieu Finset

abbrev Shell := {x : Lattice // normSq x.val = 48}

noncomputable instance : Fintype Shell := by
  have : Finite Shell := (Nat.card_pos_iff.mp
    (show 0 < Nat.card Shell by rw [LeechNorm48.card_norm48_vectors]; decide)).2
  exact Fintype.ofFinite _

theorem shell_card : Fintype.card Shell = 16773120 :=
  Nat.card_eq_fintype_card.symm.trans LeechNorm48.card_norm48_vectors

def onShell (g : Aut) : Shell ≃ Shell :=
  Equiv.subtypeEquiv g.val fun x => by change normSq x.val = 48 ↔ normSq (g x).val = 48; rw [map_norm]

abbrev coord (x : Shell) (i : Point) : ℤ := x.val.val i

def diff (x : Shell) : ℤ := coord x 0 - coord x 1

private noncomputable def powerSum (n : ℕ) (i : Point) : ℤ := ∑ x : Shell, coord x i ^ n

private noncomputable def mixed (i j : Point) : ℤ := ∑ x : Shell, coord x i ^ 2 * coord x j ^ 2

private theorem sum_power (n : ℕ) (i : Point) :
    (∑ x : Shell, coord x i ^ n) = powerSum n i := rfl

private theorem sum_mixed (i j : Point) :
    (∑ x : Shell, coord x i ^ 2 * coord x j ^ 2) = mixed i j := rfl

private theorem same_power (n : ℕ) (i : Point) : powerSum n i = powerSum n 0 := by
  obtain ⟨j, hj⟩ := exists_ne i
  obtain ⟨g, hg⟩ := move_indices i j hj false
  let f := fun x : Shell => coord x 0 ^ n
  calc
    _ = ∑ x : Shell, f (onShell g x) := by
      apply sum_congr rfl
      intro x _
      change coord x i ^ n = (g x.val).val 0 ^ n
      rw [(hg x.val).1]
    _ = _ := Equiv.sum_comp (onShell g) f

private theorem same_mixed (i j : Point) (h : j ≠ i) : mixed i j = mixed 0 1 := by
  obtain ⟨g, hg⟩ := move_indices i j h false
  let f := fun x : Shell => coord x 0 ^ 2 * coord x 1 ^ 2
  calc
    _ = ∑ x : Shell, f (onShell g x) := by
      apply sum_congr rfl
      intro x _
      change _ = (g x.val).val 0 ^ 2 * (g x.val).val 1 ^ 2
      rw [(hg x.val).1, (hg x.val).2]
      rfl
    _ = _ := Equiv.sum_comp (onShell g) f

private theorem one_square : powerSum 2 0 = 33546240 := by
  have all : (∑ i : Point, powerSum 2 i) = 48 * 16773120 := by
    unfold powerSum
    rw [sum_comm]
    have hn (x : Shell) : ∑ i, coord x i ^ 2 = 48 := x.property
    simp [hn, shell_card]
  have he : (∑ i : Point, powerSum 2 i) = 24 * powerSum 2 0 := by
    calc
      _ = ∑ _ : Point, powerSum 2 0 := sum_congr rfl fun i _ => same_power 2 i
      _ = _ := by simp
  omega

private theorem mixed_row : powerSum 4 0 + 23 * mixed 0 1 = 48 * powerSum 2 0 := by
  have diag : mixed 0 0 = powerSum 4 0 := by
    apply sum_congr rfl
    intro x _
    ring
  have entry (j : Point) : mixed 0 j =
      (if j = 0 then powerSum 4 0 - mixed 0 1 else 0) + mixed 0 1 := by
    by_cases hj : j = 0
    · simp [hj, diag]
    · simp [hj, same_mixed 0 j hj]
  have row : (∑ j : Point, mixed 0 j) = powerSum 4 0 + 23 * mixed 0 1 := by
    rw [sum_congr rfl (fun j _ => entry j)]
    simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [← row]
  unfold mixed
  rw [sum_comm]
  have hn (x : Shell) : (∑ j, coord x j ^ 2) = 48 := x.property
  simp only [← mul_sum, hn, ← sum_mul, powerSum]
  ring

private def signedFour (b c d : Bool) (x : Shell) : ℤ :=
  coord x 0 - twoSign b (coord x 1) - twoSign c (coord x 2) - twoSign d (coord x 3)

-- The four-coordinate lattice move turns this signed sum into twice one coordinate.
private theorem signed_fourth (b c d : Bool) :
    (∑ x : Shell, signedFour b c d x ^ 4) = 16 * powerSum 4 0 := by
  obtain ⟨w, hw⟩ := four_signs ![false, b, c, d]
  let g := LeechSextet.symmetry * signAut w
  have at0 : w.val 0 = false := hw 0
  have at1 : w.val 1 = b := hw 1
  have at2 : w.val 2 = c := hw 2
  have at3 : w.val 3 = d := hw 3
  have twice (x : Shell) : 2 * coord (onShell g x) 0 = signedFour b c d x := by
    have h := first_norm_move (signAut w x.val) 0
    rw [Fin.sum_univ_four] at h
    change 2 * coord (onShell g x) 0 =
      2 * signFlip w.val x.val.val 0 - (signFlip w.val x.val.val 0 + signFlip w.val x.val.val 1 +
        signFlip w.val x.val.val 2 + signFlip w.val x.val.val 3) at h
    rw [h]
    simp only [signFlip, at0, at1, at2, at3, Bool.false_eq_true, ite_false, signedFour, twoSign, coord]
    ring
  have reindex := Equiv.sum_comp (onShell g) (fun x : Shell => coord x 0 ^ 4)
  calc
    _ = ∑ x : Shell, 16 * coord (onShell g x) 0 ^ 4 := by
      apply sum_congr rfl
      intro x _
      rw [← twice]
      ring
    _ = _ := by rw [← mul_sum, reindex]; rfl

-- Averaging the eight sign choices cancels the terms with odd exponents.
private theorem fourth_ratio : powerSum 4 0 = 3 * mixed 0 1 := by
  have expand (x : Shell) :
      (∑ b : Bool, ∑ c : Bool, ∑ d : Bool, signedFour b c d x ^ 4) =
      8 * (coord x 0 ^ 4 + coord x 1 ^ 4 + coord x 2 ^ 4 + coord x 3 ^ 4 +
        6 * (coord x 0 ^ 2 * coord x 1 ^ 2 + coord x 0 ^ 2 * coord x 2 ^ 2 +
             coord x 0 ^ 2 * coord x 3 ^ 2 + coord x 1 ^ 2 * coord x 2 ^ 2 +
             coord x 1 ^ 2 * coord x 3 ^ 2 + coord x 2 ^ 2 * coord x 3 ^ 2)) := by
    simp only [Fintype.sum_bool, signedFour, twoSign, Bool.false_eq_true, ite_false, ite_true]
    ring
  have h := congrArg (fun f : Shell → ℤ => ∑ x, f x) (funext expand)
  simp only [Fintype.sum_bool, sum_add_distrib, signed_fourth, ← mul_sum,
    sum_power, sum_mixed] at h
  rw [same_power 4 1, same_power 4 2, same_power 4 3, same_mixed 0 2 (by decide),
    same_mixed 0 3 (by decide), same_mixed 1 2 (by decide), same_mixed 1 3 (by decide),
    same_mixed 2 3 (by decide)] at h
  omega

private theorem swap_sign (n : ℕ) :
    (∑ x : Shell, (coord x 0 + coord x 1) ^ n) = ∑ x : Shell, diff x ^ n := by
  obtain ⟨g, hg⟩ := move_indices 0 1 (by decide) true
  let f := fun x : Shell => diff x ^ n
  calc
    _ = ∑ x : Shell, f (onShell g x) := by
      apply sum_congr rfl
      intro x _
      change _ = ((g x.val).val 0 - (g x.val).val 1) ^ n
      rw [(hg x.val).1, (hg x.val).2]
      simp [twoSign]
    _ = _ := Equiv.sum_comp (onShell g) f

/-- Sum (x₀ − x₁)² and (x₀ − x₁)⁴ over the vectors of squared length 48. -/
theorem diff_moments :
    (∑ x : Shell, diff x ^ 2) = 67092480 ∧ (∑ x : Shell, diff x ^ 4) = 743178240 := by
  have p4 := fourth_ratio
  have row := mixed_row
  rw [one_square] at row
  have expand2 (x : Shell) :
      (coord x 0 + coord x 1)^2 + diff x ^ 2 = 2 * (coord x 0 ^ 2 + coord x 1 ^ 2) := by
    unfold diff; ring
  have expand4 (x : Shell) :
      (coord x 0 + coord x 1)^4 + diff x ^ 4 =
      2 * (coord x 0 ^ 4 + coord x 1 ^ 4 + 6 * (coord x 0 ^ 2 * coord x 1 ^ 2)) := by
    unfold diff; ring
  have h2 := congrArg (fun f : Shell → ℤ => ∑ x, f x) (funext expand2)
  have h4 := congrArg (fun f : Shell → ℤ => ∑ x, f x) (funext expand4)
  simp only [sum_add_distrib, ← mul_sum, swap_sign, sum_power, sum_mixed] at h2 h4
  rw [same_power 2 1, one_square] at h2
  rw [same_power 4 1] at h4
  constructor <;> omega

end LeechNorm48Layers
