import Mathlib

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

def Picks {n : ℕ} (odd : Bool) (w : Fin n → Bool) (e r : ℤ) :=
  {a : Fin n → Label // (∑ i, cost odd (w i) (a i)) = e ∧
                          (∑ i, flag (a i)) % 2 = r % 2}

instance {n} (p) (w : Fin n → Bool) (e r) : Fintype (Picks p w e r) :=
  inferInstanceAs (Fintype (Subtype _))

private def splitFirst {n} (p) (w : Fin (n+1) → Bool) (e r : ℤ) :
    Picks p w e r ≃ Σ a : Label, Picks p (fun i => w i.succ)
      (e - cost p (w 0) a) (r - flag a) where
  toFun x := ⟨x.val 0, fun i => x.val i.succ, by
    obtain ⟨he, hr⟩ := x.property
    rw [Fin.sum_univ_succ] at he hr
    dsimp only
    constructor <;> omega⟩
  invFun := fun ⟨a, x⟩ => ⟨Fin.cons a x.val, by
    obtain ⟨he, hr⟩ := x.property
    dsimp only at he hr
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    constructor <;> omega⟩
  left_inv x := by apply Subtype.ext; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv := by rintro ⟨a, x⟩; rfl

private def step (p b : Bool) (f : Table) : Table :=
  fun e r => ∑ a : Label, f (e - cost p b a) (r - flag a)

private theorem commute (p : Bool) : Function.Commute (step p true) (step p false) := by
  intro f
  funext e r
  unfold step
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  congr 1 <;> ring

private def emptyTable : Table := fun e r => if 0 = e ∧ 0 = r % 2 then 1 else 0

def tally (p : Bool) (z o : ℕ) : Table :=
  (step p false)^[z] ((step p true)^[o] emptyTable)

private theorem tally_false (p z o) : tally p (z+1) o = step p false (tally p z o) := by
  simp [tally, Function.iterate_succ_apply']

private theorem tally_true (p z o) : tally p z (o+1) = step p true (tally p z o) := by
  unfold tally
  rw [Function.iterate_succ_apply']
  exact ((commute p).iterate_right z _).symm

def bits {n} (w : Fin n → Bool) (b : Bool) : ℕ := ∑ i, if w i = b then 1 else 0

theorem card_picks {n} (p) (w : Fin n → Bool) (e r : ℤ) :
    Fintype.card (Picks p w e r) = tally p (bits w false) (bits w true) e r := by
  induction n generalizing e r with
  | zero =>
    let a : Fin 0 → Label := Fin.elim0
    by_cases h : 0 = e ∧ 0 = r % 2
    · simp only [bits, Finset.univ_eq_empty, Finset.sum_empty, tally, Function.iterate_zero,
        id_eq, emptyTable, ite_eq_left h]
      apply Fintype.card_eq_one_iff.mpr
      exact ⟨⟨a, by simpa using h⟩, fun y => Subtype.ext (Subsingleton.elim _ _)⟩
    · simp [bits, tally, emptyTable, h]
      apply Fintype.card_eq_zero_iff.mpr
      exact ⟨fun y => h (by simpa using y.property)⟩
  | succ n ih =>
    rw [Fintype.card_congr (splitFirst p w e r), Fintype.card_sigma]
    simp_rw [ih]
    have hb (b : Bool) : bits w b = (if w 0 = b then 1 else 0) + bits (fun i => w i.succ) b := by
      unfold bits; rw [Fin.sum_univ_succ]
    cases hw : w 0 <;> simp [hb, hw, Nat.one_add, tally_true, tally_false, step]

private theorem cost_nonneg (p b : Bool) (a : Label) : 0 ≤ cost p b a := by
  cases p <;> cases b <;> fin_cases a <;> decide

private def NoNegative (f : Table) : Prop := ∀ e r, e < 0 → f e r = 0

private theorem step_nonneg (p b) {f : Table} (hf : NoNegative f) : NoNegative (step p b f) := by
  intro e r he
  apply sum_eq_zero
  intro a _
  exact hf _ _ (by have := cost_nonneg p b a; omega)

/-- Evaluate a row of coordinate choices, dropping a branch once its budget is negative. -/
private def evaluate (p : Bool) : List Bool → Table
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
  | nil => simp [evaluate, emptyTable, show ¬ 0 = e by omega]
  | cons b bs => simp [evaluate, he]

private theorem eval_cons (p b bs) : evaluate p (b :: bs) = step p b (evaluate p bs) := by
  funext e r
  by_cases he : e < 0
  · exact (eval_negative _ _ _ _ he).trans ((step_nonneg _ _ (eval_negative p bs) _ _ he).symm)
  · simp [evaluate, he, step, Fin.sum_univ_four, flag, add_assoc]

private theorem eval_replicate (p b bs n) :
    evaluate p (List.replicate n b ++ bs) = (step p b)^[n] (evaluate p bs) := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.cons_append, eval_cons, ih, Function.iterate_succ_apply']

private theorem tally_eval (p z o) :
    tally p z o = evaluate p (List.replicate z false ++ List.replicate o true) := by
  rw [eval_replicate, ← List.append_nil (List.replicate o true), eval_replicate]
  rfl

private theorem odd_step : step true true = step true false := rfl

private theorem odd_tally (z o) : tally true z o = tally true (z+o) 0 := by
  simp [tally, odd_step, Function.iterate_add_apply]

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
