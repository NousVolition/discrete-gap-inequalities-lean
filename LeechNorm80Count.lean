import LeechNorm48Count
import Mathlib.Tactic.Eval

/-! # Coordinate choices at squared lengths 80 and 96

The rows count the choices left after fixing a Golay residue word. Each column
records a squared-length budget from zero to twelve, in units of eight. Its two
entries count the choices for each parity of the coordinate sum. -/
namespace LeechNorm80Count

open LeechNorm48Count

private abbrev Row := List (ℕ × ℕ)

private def readRow (row : Row) (e : ℤ) (odd : Bool) : ℕ :=
  if e < 0 then 0 else
    let counts := row[e.toNat]?.getD (0, 0)
    if odd then counts.2 else counts.1

private def start (e : ℤ) (odd : Bool) : ℕ := if e = 0 ∧ odd = false then 1 else 0

private def addCoord (p b : Bool) (prev : Row) (e : ℤ) (r : Bool) : ℕ :=
  readRow prev (e - cost p b 0) r + readRow prev (e - cost p b 1) (!r) +
  readRow prev (e - cost p b 2) r + readRow prev (e - cost p b 3) (!r)

private def makeRow (f : ℤ → Bool → ℕ) : Row :=
  (List.range 13).map fun e => (f e false, f e true)

private def makeRows (p : Bool) : List Bool → List Row
  | [] => [makeRow start]
  | b :: bs =>
    let rest := makeRows p bs
    makeRow (addCoord p b (rest.headD [])) :: rest

private def checkRow (row : Row) (f : ℤ → Bool → ℕ) : Bool :=
  decide (∀ e : Fin 13, ∀ r : Bool, readRow row e.val r = f e.val r)

private def checkRows (p : Bool) : List Bool → List Row → Bool
  | [], [row] => checkRow row start
  | b :: bs, row :: rest => checkRow row (addCoord p b (rest.headD [])) && checkRows p bs rest
  | _, _ => false

private theorem checked_at {row : Row} {f : ℤ → Bool → ℕ} (h : checkRow row f = true)
    {e : ℤ} (lo : 0 ≤ e) (hi : e ≤ 12) (r : Bool) : readRow row e r = f e r := by
  have h' := of_decide_eq_true h
  simpa [Int.toNat_of_nonneg lo] using h' (⟨e.toNat, by omega⟩ : Fin 13) r

private def parityBit (r : ℤ) : Bool := decide (r % 2 = 1)

private theorem toggle (r : ℤ) : parityBit (r - 1) = !parityBit r := by
  unfold parityBit
  by_cases h : r % 2 = 1
  · simp [h, show (r - 1) % 2 ≠ 1 by omega]
  · simp [h, show (r - 1) % 2 = 1 by omega]

private theorem checked_rows_count (p : Bool) (bs : List Bool) (rows : List Row)
    (h : checkRows p bs rows = true) (e r : ℤ) (he : e ≤ 12) :
    evaluate p bs e r = readRow (rows.headD []) e (parityBit r) := by
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
      change evaluate p (b :: bs) e r = readRow row e (parityBit r)
      by_cases neg : e < 0
      · simp [evaluate, readRow, neg]
      rw [checked_at hc (by omega) he]
      have smaller (a : Label) (s : ℤ) := ih rest ht (e - cost p b a) s (by
        have hn : 0 ≤ cost p b a := by cases p <;> cases b <;> fin_cases a <;> decide
        omega)
      simp only [evaluate, ite_eq_right neg, smaller, toggle, addCoord]

private def casesToCheck : Fin 6 → Bool × ℕ :=
  ![(true, 0), (false, 0), (false, 8), (false, 12), (false, 16), (false, 24)]

private def wordBits (k : ℕ) : List Bool := List.replicate (24 - k) false ++ List.replicate k true

-- The evaluator supplies the rows. Lean's kernel checks the starting row and every entry thereafter.
private def certificates : List (List Row) := eval% List.ofFn (fun i : Fin 6 =>
  makeRows (casesToCheck i).1 (wordBits (casesToCheck i).2))

private def rowsFor (i : Fin 6) := certificates[i.val]?.getD []

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem valid_rows (i : Fin 6) :
    checkRows (casesToCheck i).1 (wordBits (casesToCheck i).2) (rowsFor i) = true := by
  fin_cases i <;> decide +kernel

private theorem from_row (i : Fin 6) (e r : ℤ) (he : e ≤ 12) :
    tally (casesToCheck i).1 (24 - (casesToCheck i).2) (casesToCheck i).2 e r =
      readRow ((rowsFor i).headD []) e (parityBit r) := by
  rw [tally_eval]
  exact checked_rows_count _ _ _ (valid_rows i) e r he

/-- Number of even-coordinate vectors for a word of weight `k`. -/
def evenPerWord (k : ℕ) : ℕ :=
  if k = 8 then 606208 else if k = 12 then 565248 else if k = 16 then 524288 else 0

theorem odd_choices (k : ℕ) (hk : k ≤ 24) : tally true (24 - k) k 7 1 = 565248 := by
  rw [odd_tally, Nat.sub_add_cancel hk]
  exact (from_row 0 7 1 (by decide)).trans (by decide +kernel)

theorem even_choices {k : ℕ} (hk : k = 0 ∨ k = 8 ∨ k = 12 ∨ k = 16 ∨ k = 24) :
    tally false (24 - k) k (10 - (k : ℤ) / 2) 0 = evenPerWord k := by
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact (from_row 1 10 0 (by decide)).trans (by decide +kernel)
  · exact (from_row 2 6 0 (by decide)).trans (by decide +kernel)
  · exact (from_row 3 4 0 (by decide)).trans (by decide +kernel)
  · exact (from_row 4 2 0 (by decide)).trans (by decide +kernel)
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
    exact (from_row 0 9 1 (by decide)).trans (by change _ = 4200352; decide +kernel)
  | false =>
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact (from_row 1 12 0 (by decide)).trans (by decide +kernel)
    · exact (from_row 2 8 0 (by decide)).trans (by decide +kernel)
    · exact (from_row 3 6 0 (by decide)).trans (by decide +kernel)
    · exact (from_row 4 4 0 (by decide)).trans (by decide +kernel)
    · exact (from_row 5 0 0 (by decide)).trans (by decide +kernel)

end LeechNorm80Count
