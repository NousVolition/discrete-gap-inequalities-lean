import LeechCoordinateAlphabet
import Mathlib.Tactic.Eval

/-! # Coordinate choices at squared lengths 80, 96, 112, 128, 144, 160, 176, 192, 208 and 224

The rows count the choices left after fixing a Golay residue word. Each column
records a squared-length budget from zero to twenty-eight, in units of eight. Its two
entries count the choices for each parity of the coordinate sum. -/
namespace LeechNorm80Count

open LeechNorm48Count
open LeechCoordinateAlphabet (Width Labels charge labelFlag)

private abbrev maxBudget : ℕ := 28

private abbrev Row := List (ℕ × ℕ)

private def readRow (row : Row) (e : ℤ) (odd : Bool) : ℕ :=
  if e < 0 then 0 else
    let counts := row[e.toNat]?.getD (0, 0)
    if odd then counts.2 else counts.1

private def start (e : ℤ) (odd : Bool) : ℕ := if e = 0 ∧ odd = false then 1 else 0

private def parityBit (r : ℤ) : Bool := decide (r % 2 = 1)

private def addCoord (width : Width) (p b : Bool) (prev : Row) (e : ℤ) (r : Bool) : ℕ :=
  ∑ a : Labels width, readRow prev (e - charge width p b a)
    (parityBit ((if r then 1 else 0) - labelFlag width a))

private def makeRow (f : ℤ → Bool → ℕ) : Row :=
  (List.range (maxBudget + 1)).map fun e => (f e false, f e true)

private def makeRows (width : Width) (p : Bool) : List Bool → List Row
  | [] => [makeRow start]
  | b :: bs =>
    let rest := makeRows width p bs
    makeRow (addCoord width p b (rest.headD [])) :: rest

private def checkRow (row : Row) (f : ℤ → Bool → ℕ) : Bool :=
  decide (∀ e : Fin (maxBudget + 1), ∀ r : Bool, readRow row e.val r = f e.val r)

private def checkRows (width : Width) (p : Bool) : List Bool → List Row → Bool
  | [], [row] => checkRow row start
  | b :: bs, row :: rest => checkRow row (addCoord width p b (rest.headD [])) && checkRows width p bs rest
  | _, _ => false

private theorem checked_at {row : Row} {f : ℤ → Bool → ℕ} (h : checkRow row f = true)
    {e : ℤ} (lo : 0 ≤ e) (hi : e ≤ maxBudget) (r : Bool) : readRow row e r = f e r := by
  have h' := of_decide_eq_true h
  simpa [Int.toNat_of_nonneg lo] using h' (⟨e.toNat, by omega⟩ : Fin (maxBudget + 1)) r

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

private theorem checked_rows_count (width : Width) (p : Bool) (bs : List Bool) (rows : List Row)
    (h : checkRows width p bs rows = true) (e r : ℤ) (he : e ≤ maxBudget) :
    LeechCoordinateTally.fold (charge width p) (labelFlag width) bs e r =
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
      · rw [LeechCoordinateTally.fold_negative _ _ (LeechCoordinateAlphabet.charge_nonneg width p) _ _ _ neg]
        simp [readRow, neg]
      rw [checked_at hc (by omega) he]
      simp only [LeechCoordinateTally.fold, LeechCoordinateTally.step, addCoord]
      apply Finset.sum_congr rfl
      intro a _
      have hn := LeechCoordinateAlphabet.charge_nonneg width p b a
      rw [ih rest ht _ _ (by omega), parity_sub]

private def casesToCheck : Fin 6 → Bool × ℕ :=
  ![(true, 0), (false, 0), (false, 8), (false, 12), (false, 16), (false, 24)]

private def wordBits (k : ℕ) : List Bool := List.replicate (24 - k) false ++ List.replicate k true

private def buildCases (width : Width) : List (List Row) :=
  List.ofFn (fun i : Fin 6 => makeRows width (casesToCheck i).1 (wordBits (casesToCheck i).2))

-- Each set of rows is stored separately. The kernel checks every entry below.
private noncomputable def fourRows : List (List Row) := eval% buildCases .four
private noncomputable def fiveRows : List (List Row) := eval% buildCases .five
private noncomputable def sixRows : List (List Row) := eval% buildCases .six
private noncomputable def eightRows : List (List Row) := eval% buildCases .eight

private noncomputable def rowsFor (width : Width) (i : Fin 6) :=
  let rows := match width with
    | .four => fourRows
    | .five => fiveRows
    | .six => sixRows
    | .eight => eightRows
  rows[i.val]?.getD []

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem valid_rows (width : Width) (i : Fin 6) :
    checkRows width (casesToCheck i).1 (wordBits (casesToCheck i).2) (rowsFor width i) = true := by
  cases width <;> fin_cases i <;> decide +kernel

private theorem from_row (width : Width) (i : Fin 6) (e r : ℤ) (he : e ≤ maxBudget) :
    LeechCoordinateAlphabet.tally width (casesToCheck i).1 (24 - (casesToCheck i).2) (casesToCheck i).2 e r =
      readRow ((rowsFor width i).headD []) e (parityBit r) := by
  unfold LeechCoordinateAlphabet.tally
  rw [LeechCoordinateTally.tally_eq_fold]
  exact checked_rows_count _ _ _ _ (valid_rows width i) e r he

/-- Number of even-coordinate vectors for a word of weight `k`. -/
def evenPerWord (k : ℕ) : ℕ :=
  if k = 8 then 606208 else if k = 12 then 565248 else if k = 16 then 524288 else 0

theorem odd_choices (k : ℕ) (hk : k ≤ 24) : tally true (24 - k) k 7 1 = 565248 := by
  rw [odd_tally, Nat.sub_add_cancel hk]
  exact (from_row .four 0 7 1 (by decide)).trans (by decide +kernel)

theorem even_choices {k : ℕ} (hk : k = 0 ∨ k = 8 ∨ k = 12 ∨ k = 16 ∨ k = 24) :
    tally false (24 - k) k (10 - (k : ℤ) / 2) 0 = evenPerWord k := by
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact (from_row .four 1 10 0 (by decide)).trans (by decide +kernel)
  · exact (from_row .four 2 6 0 (by decide)).trans (by decide +kernel)
  · exact (from_row .four 3 4 0 (by decide)).trans (by decide +kernel)
  · exact (from_row .four 4 2 0 (by decide)).trans (by decide +kernel)
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
    exact (from_row .four 0 9 1 (by decide)).trans (by change _ = 4200352; decide +kernel)
  | false =>
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact (from_row .four 1 12 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .four 2 8 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .four 3 6 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .four 4 4 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .four 5 0 0 (by decide)).trans (by decide +kernel)

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
    exact (from_row .five 0 11 1 (by decide)).trans (by change _ = 22892544; decide +kernel)
  | false =>
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact (from_row .five 1 14 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .five 2 10 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .five 3 8 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .five 4 6 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .five 5 2 0 (by decide)).trans (by decide +kernel)

/-- Choices for one Golay word at squared length 128. -/
theorem choices128 (p : Bool) {k : ℕ} (hk : k = 0 ∨ k = 8 ∨ k = 12 ∨ k = 16 ∨ k = 24) :
    LeechCoordinateAlphabet.tally .six p (24 - k) k
      (if p then 16 - 3 else 16 - (k : ℤ) / 2) (if p then 1 else 0) =
      if p then 99448320 else if k = 0 then 195082320 else if k = 8 then 98902016
      else if k = 12 then 99483648 else if k = 16 then 99876864 else if k = 24 then 201326592 else 0 := by
  cases p with
  | true =>
    have le : k ≤ 24 := by omega
    rw [LeechCoordinateAlphabet.odd_tally, Nat.sub_add_cancel le]
    exact (from_row .six 0 13 1 (by decide)).trans (by change _ = 99448320; decide +kernel)
  | false =>
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact (from_row .six 1 16 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .six 2 12 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .six 3 10 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .six 4 8 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .six 5 4 0 (by decide)).trans (by decide +kernel)

/-- Choices for one Golay word at squared length 144. -/
theorem choices144 (p : Bool) {k : ℕ} (hk : k = 0 ∨ k = 8 ∨ k = 12 ∨ k = 16 ∨ k = 24) :
    LeechCoordinateAlphabet.tally .six p (24 - k) k
      (if p then 18 - 3 else 18 - (k : ℤ) / 2) (if p then 1 else 0) =
      if p then 363315200 else if k = 8 then 362774528 else if k = 12 then 363315200
      else if k = 16 then 363855872 else 0 := by
  cases p with
  | true =>
    have le : k ≤ 24 := by omega
    rw [LeechCoordinateAlphabet.odd_tally, Nat.sub_add_cancel le]
    exact (from_row .six 0 15 1 (by decide)).trans (by change _ = 363315200; decide +kernel)
  | false =>
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact (from_row .six 1 18 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .six 2 14 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .six 3 12 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .six 4 10 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .six 5 6 0 (by decide)).trans (by decide +kernel)

/-- Choices for one Golay word at squared length 160. -/
theorem choices160 (p : Bool) {k : ℕ} (hk : k = 0 ∨ k = 8 ∨ k = 12 ∨ k = 16 ∨ k = 24) :
    LeechCoordinateAlphabet.tally .eight p (24 - k) k
      (if p then 20 - 3 else 20 - (k : ℤ) / 2) (if p then 1 else 0) =
      if p then 1157743824 else if k = 0 then 2319457632 else if k = 8 then 1158246144
      else if k = 12 ∨ k = 16 then 1157627904 else if k = 24 then 2315255808 else 0 := by
  cases p with
  | true =>
    have le : k ≤ 24 := by omega
    rw [LeechCoordinateAlphabet.odd_tally, Nat.sub_add_cancel le]
    exact (from_row .eight 0 17 1 (by decide)).trans (by change _ = 1157743824; decide +kernel)
  | false =>
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact (from_row .eight 1 20 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 2 16 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 3 14 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 4 12 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 5 8 0 (by decide)).trans (by decide +kernel)

/-- Choices for one Golay word at squared length 176. -/
theorem choices176 (p : Bool) {k : ℕ} (hk : k = 0 ∨ k = 8 ∨ k = 12 ∨ k = 16 ∨ k = 24) :
    LeechCoordinateAlphabet.tally .eight p (24 - k) k
      (if p then 22 - 3 else 22 - (k : ℤ) / 2) (if p then 1 else 0) =
      if p then 3303168000 else if k = 8 then 3305418752 else if k = 12 then 3303168000
      else if k = 16 then 3300917248 else 0 := by
  cases p with
  | true =>
    have le : k ≤ 24 := by omega
    rw [LeechCoordinateAlphabet.odd_tally, Nat.sub_add_cancel le]
    exact (from_row .eight 0 19 1 (by decide)).trans (by change _ = 3303168000; decide +kernel)
  | false =>
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact (from_row .eight 1 22 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 2 18 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 3 16 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 4 14 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 5 10 0 (by decide)).trans (by decide +kernel)

/-- The number of coordinate choices for one Golay word at squared length 192. -/
theorem choices192 (p : Bool) {k : ℕ} (hk : k = 0 ∨ k = 8 ∨ k = 12 ∨ k = 16 ∨ k = 24) :
    LeechCoordinateAlphabet.tally .eight p (24 - k) k
      (if p then 24 - 3 else 24 - (k : ℤ) / 2) (if p then 1 else 0) =
      if p then 8602175744
      else if k = 0 then 17231109824 else if k = 8 then 8605675520 else if k = 12 then 8602320896
      else if k = 16 then 8598192128 else if k = 24 then 17179869184 else 0 := by
  cases p with
  | true =>
    have le : k ≤ 24 := by omega
    rw [LeechCoordinateAlphabet.odd_tally, Nat.sub_add_cancel le]
    exact (from_row .eight 0 21 1 (by decide)).trans (by change _ = 8602175744; decide +kernel)
  | false =>
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact (from_row .eight 1 24 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 2 20 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 3 18 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 4 16 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 5 12 0 (by decide)).trans (by decide +kernel)

/-- The number of coordinate choices for one Golay word at squared length 208. -/
theorem choices208 (p : Bool) {k : ℕ} (hk : k = 0 ∨ k = 8 ∨ k = 12 ∨ k = 16 ∨ k = 24) :
    LeechCoordinateAlphabet.tally .eight p (24 - k) k
      (if p then 26 - 3 else 26 - (k : ℤ) / 2) (if p then 1 else 0) =
      if p then 20748607488 else if k = 8 then 20751663104 else if k = 12 then 20748607488
      else if k = 16 then 20745551872 else 0 := by
  cases p with
  | true =>
    have le : k ≤ 24 := by omega
    rw [LeechCoordinateAlphabet.odd_tally, Nat.sub_add_cancel le]
    exact (from_row .eight 0 23 1 (by decide)).trans (by change _ = 20748607488; decide +kernel)
  | false =>
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact (from_row .eight 1 26 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 2 22 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 3 20 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 4 18 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 5 14 0 (by decide)).trans (by decide +kernel)

/-- The number of coordinate choices for one Golay word at squared length 224. -/
theorem choices224 (p : Bool) {k : ℕ} (hk : k = 0 ∨ k = 8 ∨ k = 12 ∨ k = 16 ∨ k = 24) :
    LeechCoordinateAlphabet.tally .eight p (24 - k) k
      (if p then 28 - 3 else 28 - (k : ℤ) / 2) (if p then 1 else 0) =
      if p then 46883528256 else if k = 0 then 93703589760 else if k = 8 then 46881786880
      else if k = 12 then 46883930112 else if k = 16 then 46883930112
      else if k = 24 then 93767860224 else 0 := by
  cases p with
  | true =>
    have le : k ≤ 24 := by omega
    rw [LeechCoordinateAlphabet.odd_tally, Nat.sub_add_cancel le]
    exact (from_row .eight 0 25 1 (by decide)).trans (by change _ = 46883528256; decide +kernel)
  | false =>
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact (from_row .eight 1 28 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 2 24 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 3 22 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 4 20 0 (by decide)).trans (by decide +kernel)
    · exact (from_row .eight 5 16 0 (by decide)).trans (by decide +kernel)

end LeechNorm80Count
