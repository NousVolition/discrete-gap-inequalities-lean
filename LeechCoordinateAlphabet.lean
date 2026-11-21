import LeechNorm48Count

/-! # Coordinate choices for the Leech shell counts

A residue modulo four has four, five or six labels in the counting tables.
Each label records a squared-length cost and a contribution to the sum modulo eight. -/
namespace LeechCoordinateAlphabet

inductive Width where
  | four | five | six

def Width.size : Width → ℕ
  | .four => 4
  | .five => 5
  | .six => 6

abbrev Labels (width : Width) := Fin width.size

def charge (width : Width) (odd bit : Bool) : Labels width → ℤ :=
  match width with
  | .four => LeechNorm48Count.cost odd bit
  | .five => LeechCoordinateChoices.charge true odd bit
  | .six =>
    let c := LeechCoordinateChoices.charge true odd bit
    ![c 0, c 1, c 2, c 3, c 4, if odd then 15 else if bit then 12 else 18]

def labelFlag (width : Width) (a : Labels width) : ℤ := (a.val : ℤ) % 2

abbrev tally (width : Width) (p : Bool) :=
  LeechCoordinateTally.tally (charge width p) (labelFlag width)

theorem charge_nonneg (width : Width) (p b : Bool) (a : Labels width) : 0 ≤ charge width p b a := by
  cases width <;> cases p <;> cases b <;> fin_cases a <;> decide

theorem odd_tally (width : Width) (z o : ℕ) : tally width true z o = tally width true (z + o) 0 := by
  have same : charge width true true = charge width true false := by cases width <;> rfl
  have steps : LeechCoordinateTally.step (charge width true) (labelFlag width) true =
      LeechCoordinateTally.step (charge width true) (labelFlag width) false := by
    funext f e r
    simp only [LeechCoordinateTally.step, same]
  simp [tally, LeechCoordinateTally.tally, steps, Function.iterate_add_apply]

end LeechCoordinateAlphabet
