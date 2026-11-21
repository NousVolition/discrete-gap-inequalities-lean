import Mathlib

/-! # Counting coordinate choices

A label contributes a cost and a change to the parity of the coordinate sum.
The two Golay bit values can be processed in either order. -/
namespace LeechCoordinateTally

open Finset
abbrev Table := ℤ → ℤ → ℕ

variable {α : Type} [Fintype α] (cost : Bool → α → ℤ) (flag : α → ℤ)

def Picks {n : ℕ} (w : Fin n → Bool) (e r : ℤ) :=
  {a : Fin n → α // (∑ i, cost (w i) (a i)) = e ∧
                          (∑ i, flag (a i)) % 2 = r % 2}

instance {n} (w : Fin n → Bool) (e r) : Fintype (Picks cost flag w e r) :=
  inferInstanceAs (Fintype (Subtype _))

private def splitFirst {n} (w : Fin (n+1) → Bool) (e r : ℤ) :
    Picks cost flag w e r ≃ Σ a : α, Picks cost flag (fun i => w i.succ)
      (e - cost (w 0) a) (r - flag a) where
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

def step (b : Bool) (f : Table) : Table :=
  fun e r => ∑ a : α, f (e - cost b a) (r - flag a)

private theorem commute : Function.Commute (step cost flag true) (step cost flag false) := by
  intro f
  funext e r
  unfold step
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  congr 1 <;> ring

def emptyTable : Table := fun e r => if 0 = e ∧ 0 = r % 2 then 1 else 0

def tally (z o : ℕ) : Table :=
  (step cost flag false)^[z] ((step cost flag true)^[o] emptyTable)

private theorem tally_false (z o) : tally cost flag (z+1) o = step cost flag false (tally cost flag z o) := by
  simp [tally, Function.iterate_succ_apply']

private theorem tally_true (z o) : tally cost flag z (o+1) = step cost flag true (tally cost flag z o) := by
  unfold tally
  rw [Function.iterate_succ_apply']
  exact ((commute cost flag).iterate_right z _).symm

def bits {n} (w : Fin n → Bool) (b : Bool) : ℕ := ∑ i, if w i = b then 1 else 0

theorem card_picks {n} (w : Fin n → Bool) (e r : ℤ) :
    Fintype.card (Picks cost flag w e r) = tally cost flag (bits w false) (bits w true) e r := by
  induction n generalizing e r with
  | zero =>
    let a : Fin 0 → α := Fin.elim0
    by_cases h : 0 = e ∧ 0 = r % 2
    · simp only [bits, Finset.univ_eq_empty, Finset.sum_empty, tally, Function.iterate_zero,
        id_eq, emptyTable, ite_eq_left h]
      apply Fintype.card_eq_one_iff.mpr
      exact ⟨⟨a, by simpa using h⟩, fun y => Subtype.ext (Subsingleton.elim _ _)⟩
    · simp [bits, tally, emptyTable, h]
      apply Fintype.card_eq_zero_iff.mpr
      exact ⟨fun y => h (by simpa using y.property)⟩
  | succ n ih =>
    rw [Fintype.card_congr (splitFirst cost flag w e r), Fintype.card_sigma]
    simp_rw [ih]
    have hb (b : Bool) : bits w b = (if w 0 = b then 1 else 0) + bits (fun i => w i.succ) b := by
      unfold bits; rw [Fin.sum_univ_succ]
    cases hw : w 0 <;> simp [hb, hw, Nat.one_add, tally_true, tally_false, step]

def fold : List Bool → Table
  | [] => emptyTable
  | b :: bs => step cost flag b (fold bs)

private theorem fold_replicate (b : Bool) (bs : List Bool) (n : ℕ) :
    fold cost flag (List.replicate n b ++ bs) = (step cost flag b)^[n] (fold cost flag bs) := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.cons_append, fold, ih, Function.iterate_succ_apply']

theorem tally_eq_fold (z o : ℕ) :
    tally cost flag z o = fold cost flag (List.replicate z false ++ List.replicate o true) := by
  rw [fold_replicate, ← List.append_nil (List.replicate o true), fold_replicate]
  rfl

theorem fold_negative (hn : ∀ b a, 0 ≤ cost b a) (bs : List Bool) (e r : ℤ) (he : e < 0) :
    fold cost flag bs e r = 0 := by
  induction bs generalizing e r with
  | nil => simp [fold, emptyTable, show ¬ 0 = e by omega]
  | cons b bs ih =>
    apply sum_eq_zero
    intro a _
    exact ih _ _ (by have := hn b a; omega)

end LeechCoordinateTally
