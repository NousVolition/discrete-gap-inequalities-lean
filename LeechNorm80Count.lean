import LeechNorm48Count
import Mathlib.Tactic.Eval

/-! # Coordinate choices at squared lengths 80, 96 and 112

The rows count the choices left after fixing a Golay residue word. Each column
records a squared-length budget from zero to fourteen, in units of eight. Its two
entries count the choices for each parity of the coordinate sum. -/
namespace LeechNorm80Count

open LeechNorm48Count
open LeechCoordinateChoices (Labels charge labelFlag)

private abbrev Row := List (ℕ × ℕ)

private def readRow (row : Row) (e : ℤ) (odd : Bool) : ℕ :=
  if e < 0 then 0 else
    let counts := row[e.toNat]?.getD (0, 0)
    if odd then counts.2 else counts.1

private def start (e : ℤ) (odd : Bool) : ℕ := if e = 0 ∧ odd = false then 1 else 0

private def parityBit (r : ℤ) : Bool := decide (r % 2 = 1)

private def addCoord (five p b : Bool) (prev : Row) (e : ℤ) (r : Bool) : ℕ :=
  ∑ a : Labels five, readRow prev (e - charge five p b a)
    (parityBit ((if r then 1 else 0) - labelFlag five a))

private def makeRow (f : ℤ → Bool → ℕ) : Row :=
  (List.range 15).map fun e => (f e false, f e true)

private def makeRows (five p : Bool) : List Bool → List Row
  | [] => [makeRow start]
  | b :: bs =>
    let rest := makeRows five p bs
    makeRow (addCoord five p b (rest.headD [])) :: rest

private def checkRow (row : Row) (f : ℤ → Bool → ℕ) : Bool :=
  decide (∀ e : Fin 15, ∀ r : Bool, readRow row e.val r = f e.val r)

private def checkRows (five p : Bool) : List Bool → List Row → Bool
  | [], [row] => checkRow row start
  | b :: bs, row :: rest => checkRow row (addCoord five p b (rest.headD [])) && checkRows five p bs rest
  | _, _ => false

private theorem checked_at {row : Row} {f : ℤ → Bool → ℕ} (h : checkRow row f = true)
    {e : ℤ} (lo : 0 ≤ e) (hi : e ≤ 14) (r : Bool) : readRow row e r = f e r := by
  have h' := of_decide_eq_true h
  simpa [Int.toNat_of_nonneg lo] using h' (⟨e.toNat, by omega⟩ : Fin 15) r

private theorem parity_sub (r z : ℤ) :
    parityBit (r - z) = parityBit ((if parityBit r then 1 else 0) - z) := by
  have h : (if parityBit r then 1 else 0 : ℤ) = r % 2 := by
    unfold parityBit
    by_cases hr : r % 2 = 1
    · simp [hr]
    · simp [show r % 2 = 0 by omega]
  rw [h]
  unfold parityBit
  rw [show (r - z) % 2 = (r % 2 - z) % 2 by omega]

private theorem checked_rows_count (five p : Bool) (bs : List Bool) (rows : List Row)
    (h : checkRows five p bs rows = true) (e r : ℤ) (he : e ≤ 14) :
    LeechCoordinateTally.fold (charge five p) (labelFlag five) bs e r =
      readRow (rows.headD []) e (parityBit r) := by
  induction bs generalizing rows e r with
  | nil =>
    cases rows with
    | nil => contradiction
    | cons row rest =>
      cases rest with
      | cons => contradiction
      | nil =>
        change (if 0 = e ∧ 0 = r % 2 then 1 else 0) = readRow row e (parityBit r)
        by_cases neg : e < 0
        · simp [readRow, neg, show 0 ≠ e by omega]
        · rw [checked_at h (by omega) he]
          have eq : (0 = e ∧ 0 = r % 2) = (e = 0 ∧ parityBit r = false) := by
            apply propext
            simp only [parityBit, decide_eq_false_iff_not]
            omega
          simp only [eq, start]
  | cons b bs ih =>
    cases rows with
    | nil => contradiction
    | cons row rest =>
      obtain ⟨hc, ht⟩ := Bool.and_eq_true_iff.mp h
      change _ = readRow row e (parityBit r)
      by_cases neg : e < 0
      · rw [LeechCoordinateTally.fold_negative _ _ (LeechCoordinateChoices.charge_nonneg five p) _ _ _ neg]
        simp [readRow, neg]
      rw [checked_at hc (by omega) he]
      simp only [LeechCoordinateTally.fold, LeechCoordinateTally.step, addCoord]
      apply Finset.sum_congr rfl
      intro a _
      have hn := LeechCoordinateChoices.charge_nonneg five p b a
      rw [ih rest ht _ _ (by omega), parity_sub]

private def casesToCheck : Fin 6 → Bool × ℕ :=
  ![(true, 0), (false, 0), (false, 8), (false, 12), (false, 16), (false, 24)]

private def wordBits (k : ℕ) : List Bool := List.replicate (24 - k) false ++ List.replicate k true

-- The evaluator supplies the rows. Lean's kernel checks the starting row and every entry thereafter.
private def certificates : List (List (List Row)) := eval% [false, true].map fun five =>
  List.ofFn (fun i : Fin 6 => makeRows five (casesToCheck i).1 (wordBits (casesToCheck i).2))

private def rowsFor (five : Bool) (i : Fin 6) := (certificates[if five then 1 else 0]?.getD [])[i.val]?.getD []

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem valid_rows (five : Bool) (i : Fin 6) :
    checkRows five (casesToCheck i).1 (wordBits (casesToCheck i).2) (rowsFor five i) = true := by
  cases five <;> fin_cases i <;> decide +kernel

private theorem from_row (five : Bool) (i : Fin 6) (e r : ℤ) (he : e ≤ 14) :
    LeechCoordinateChoices.tally five (casesToCheck i).1 (24 - (casesToCheck i).2) (casesToCheck i).2 e r =
      readRow ((rowsFor five i).headD []) e (parityBit r) := by
  unfold LeechCoordinateChoices.tally
  rw [LeechCoordinateTally.tally_eq_fold]
  exact checked_rows_count _ _ _ _ (valid_rows five i) e r he

/-- Number of even-coordinate vectors for a word of weight `k`. -/
def evenPerWord (k : ℕ) : ℕ :=
  if k = 8 then 606208 else if k = 12 then 565248 else if k = 16 then 524288 else 0

theorem odd_choices (k : ℕ) (hk : k ≤ 24) : tally true (24 - k) k 7 1 = 565248 := by
  rw [odd_tally, Nat.sub_add_cancel hk]
  exact (from_row false 0 7 1 (by decide)).trans (by decide +kernel)

theorem even_choices {k : ℕ} (hk : k = 0 ∨ k = 8 ∨ k = 12 ∨ k = 16 ∨ k = 24) :
    tally false (24 - k) k (10 - (k : ℤ) / 2) 0 = evenPerWord k := by
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact (from_row false 1 10 0 (by decide)).trans (by decide +kernel)
  · exact (from_row false 2 6 0 (by decide)).trans (by decide +kernel)
  · exact (from_row false 3 4 0 (by decide)).trans (by decide +kernel)
  · exact (from_row false 4 2 0 (by decide)).trans (by decide +kernel)
  · rw [tally_eval]
    rfl

/-- Choices in the box from −8 to 7 at squared length 96, for one Golay word. -/
theorem choices96 (p : Bool) {k : ℕ} (hk : k = 0 ∨ k = 8 ∨ k = 12 ∨ k = 16 ∨ k = 24) :
    tally p (24 - k) k (if p then 12 - 3 else 12 - (k : ℤ) / 2) (if p then 1 else 0) =
      if p then 4200352 else if k = 0 then 8638432 else if k = 8 then 4224512
      else if k = 24 then 8388608 else 4194304 := by
  cases p with
  | true =>
    have le : k ≤ 24 := by omega
    rw [odd_tally, Nat.sub_add_cancel le]
    exact (from_row false 0 9 1 (by decide)).trans (by change _ = 4200352; decide +kernel)
  | false =>
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact (from_row false 1 12 0 (by decide)).trans (by decide +kernel)
    · exact (from_row false 2 8 0 (by decide)).trans (by decide +kernel)
    · exact (from_row false 3 6 0 (by decide)).trans (by decide +kernel)
    · exact (from_row false 4 4 0 (by decide)).trans (by decide +kernel)
    · exact (from_row false 5 0 0 (by decide)).trans (by decide +kernel)

/-- Choices for one Golay word at squared length 112. -/
theorem choices112 (p : Bool) {k : ℕ} (hk : k = 0 ∨ k = 8 ∨ k = 12 ∨ k = 16 ∨ k = 24) :
    LeechCoordinateChoices.tally true p (24 - k) k
      (if p then 14 - 3 else 14 - (k : ℤ) / 2) (if p then 1 else 0) =
      if p then 22892544 else if k = 8 then 22716416 else if k = 12 then 22892544
      else if k = 16 then 23068672 else 0 := by
  cases p with
  | true =>
    have le : k ≤ 24 := by omega
    rw [LeechCoordinateChoices.odd_tally, Nat.sub_add_cancel le]
    exact (from_row true 0 11 1 (by decide)).trans (by change _ = 22892544; decide +kernel)
  | false =>
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact (from_row true 1 14 0 (by decide)).trans (by decide +kernel)
    · exact (from_row true 2 10 0 (by decide)).trans (by decide +kernel)
    · exact (from_row true 3 8 0 (by decide)).trans (by decide +kernel)
    · exact (from_row true 4 6 0 (by decide)).trans (by decide +kernel)
    · exact (from_row true 5 2 0 (by decide)).trans (by decide +kernel)

end LeechNorm80Count
