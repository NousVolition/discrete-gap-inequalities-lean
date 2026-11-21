import LeechCoordinateTally

/-! # Counting coordinate choices with a fixed Golay residue word

Each coordinate has four labels. The cost records its excess squared length in
units of eight. The parity of the label records whether it changes the coordinate
sum by four modulo eight. -/
namespace LeechNorm48Count

open Finset
abbrev Label := Fin 4
abbrev Table := ℤ → ℤ → ℕ

def cost (odd bit : Bool) : Label → ℤ :=
  if odd then ![6, 1, 0, 3] else if bit then ![4, 0, 0, 4] else ![8, 2, 0, 2]

def flag (a : Label) : ℤ := (a.val : ℤ) % 2

abbrev Picks {n} (p : Bool) (w : Fin n → Bool) (e r : ℤ) :=
  LeechCoordinateTally.Picks (cost p) flag w e r

private abbrev step (p b : Bool) := LeechCoordinateTally.step (cost p) flag b
private abbrev emptyTable := LeechCoordinateTally.emptyTable

abbrev tally (p : Bool) := LeechCoordinateTally.tally (cost p) flag
abbrev bits {n} (w : Fin n → Bool) := LeechCoordinateTally.bits w

theorem card_picks {n} (p) (w : Fin n → Bool) (e r : ℤ) :
    Fintype.card (Picks p w e r) = tally p (bits w false) (bits w true) e r :=
  LeechCoordinateTally.card_picks (cost p) flag w e r

private theorem cost_nonneg (p b : Bool) (a : Label) : 0 ≤ cost p b a := by
  cases p <;> cases b <;> fin_cases a <;> decide

private def NoNegative (f : Table) : Prop := ∀ e r, e < 0 → f e r = 0

private theorem step_nonneg (p b) {f : Table} (hf : NoNegative f) : NoNegative (step p b f) := by
  intro e r he
  apply sum_eq_zero
  intro a _
  exact hf _ _ (by have := cost_nonneg p b a; omega)

/-- Evaluate a row of coordinate choices, dropping a branch once its budget is negative. -/
def evaluate (p : Bool) : List Bool → Table
  | [] => emptyTable
  | b :: bs => fun e r =>
    if e < 0 then 0 else
      evaluate p bs (e - cost p b 0) r +
      evaluate p bs (e - cost p b 1) (r - 1) +
      evaluate p bs (e - cost p b 2) r +
      evaluate p bs (e - cost p b 3) (r - 1)

private theorem eval_negative (p bs) : NoNegative (evaluate p bs) := by
  intro e r he
  cases bs with
  | nil => simp [evaluate, emptyTable, LeechCoordinateTally.emptyTable, show ¬ 0 = e by omega]
  | cons b bs => simp [evaluate, he]

private theorem eval_cons (p b bs) : evaluate p (b :: bs) = step p b (evaluate p bs) := by
  funext e r
  by_cases he : e < 0
  · exact (eval_negative _ _ _ _ he).trans ((step_nonneg _ _ (eval_negative p bs) _ _ he).symm)
  · simp [evaluate, he, step, LeechCoordinateTally.step, Fin.sum_univ_four, flag, add_assoc]

private theorem eval_replicate (p b bs n) :
    evaluate p (List.replicate n b ++ bs) = (step p b)^[n] (evaluate p bs) := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.cons_append, eval_cons, ih, Function.iterate_succ_apply']

theorem tally_eval (p z o) :
    tally p z o = evaluate p (List.replicate z false ++ List.replicate o true) := by
  rw [eval_replicate, ← List.append_nil (List.replicate o true), eval_replicate]
  rfl

private theorem odd_step : step true true = step true false := rfl

theorem odd_tally (z o) : tally true z o = tally true (z+o) 0 := by
  change (step true false)^[z] ((step true true)^[o] emptyTable) = (step true false)^[z+o] emptyTable
  rw [odd_step, Function.iterate_add_apply]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem odd_value : tally true 24 0 3 1 = 2048 := by
  rw [tally_eval]; decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem even_values :
    tally false 24 0 6 0 = 0 ∧ tally false 16 8 2 0 = 4096 ∧
      tally false 12 12 0 0 = 2048 := by
  simp only [tally_eval]; decide +kernel

theorem odd_choices (z o : ℕ) (h : z + o = 24) : tally true z o 3 1 = 2048 := by
  rw [odd_tally, h, odd_value]

theorem even_choices (z o : ℕ) (h : z + o = 24) (hw : o % 4 = 0) (hmin : o = 0 ∨ 8 ≤ o) :
    tally false z o (6 - (o : ℤ) / 2) 0 =
      (if o = 8 then 4096 else if o = 12 then 2048 else 0) := by
  by_cases hbig : 12 < o
  · rw [tally_eval, eval_negative _ _ _ _ (by omega)]
    simp [show o ≠ 8 by omega, show o ≠ 12 by omega]
  · have ho : o = 0 ∨ o = 8 ∨ o = 12 := by omega
    rcases ho with rfl | rfl | rfl
    · have : z = 24 := by omega
      subst z; exact even_values.1
    · have : z = 16 := by omega
      subst z; exact even_values.2.1
    · have : z = 12 := by omega
      subst z; exact even_values.2.2


end LeechNorm48Count

namespace LeechCoordinateChoices

open LeechNorm48Count

/-- A fifth label adds the next integer in the same residue class. -/
abbrev Labels (five : Bool) := Fin (if five then 5 else 4)

def charge (five p b : Bool) : Labels five → ℤ :=
  match five with
  | false => cost p b
  | true => ![cost p b 0, cost p b 1, cost p b 2, cost p b 3, if p then 10 else if b then 12 else 8]

def labelFlag (five : Bool) (a : Labels five) : ℤ := (a.val : ℤ) % 2

abbrev tally (five p : Bool) := LeechCoordinateTally.tally (charge five p) (labelFlag five)

theorem charge_nonneg (five p b : Bool) (a : Labels five) : 0 ≤ charge five p b a := by
  cases five <;> cases p <;> cases b <;> fin_cases a <;> decide

theorem odd_tally (five : Bool) (z o : ℕ) : tally five true z o = tally five true (z + o) 0 := by
  have same : charge five true true = charge five true false := by cases five <;> rfl
  have steps : LeechCoordinateTally.step (charge five true) (labelFlag five) true =
      LeechCoordinateTally.step (charge five true) (labelFlag five) false := by
    funext f e r
    simp only [LeechCoordinateTally.step, same]
  simp [tally, LeechCoordinateTally.tally, steps, Function.iterate_add_apply]

end LeechCoordinateChoices
