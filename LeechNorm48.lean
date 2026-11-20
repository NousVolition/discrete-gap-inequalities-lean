import LeechShellCoordinates
import LeechDodecadCount

/-! # Vectors of squared length 48 in the Leech lattice -/
namespace LeechNorm48

open LeechLattice LeechMinimal LeechCodeCounts LeechSymmetry LeechNorm48Count Finset

private theorem per_word (p : Bool) (w : Codeword) :
    tally p (24 - weight w.val) (weight w.val)
      (if p then 6 - 3 else 6 - (weight w.val : ℤ) / 2) (if p then 1 else 0) =
      if p then 2048 else if weight w.val = 8 then 4096 else if weight w.val = 12 then 2048 else 0 := by
  have hle : weight w.val ≤ 24 := by simpa [weight] using (card_filter_le univ (fun i => w.val i = true))
  have hz : 24 - weight w.val + weight w.val = 24 := by omega
  have hm : weight w.val = 0 ∨ 8 ≤ weight w.val := by
    by_cases h : ∃ i, w.val i = true
    · exact Or.inr (golay_weight_ge_eight w.property h)
    · left; simp [weight, show ∀ i, w.val i ≠ true by simpa using h]
  cases p with
  | true => exact odd_choices _ _ hz
  | false => exact even_choices _ _ hz (golay_weight_mod_four w.property) hm

/-- There are 16,773,120 vectors of squared length 48 in the integer coordinates. -/
theorem card_norm48_vectors : Nat.card {x : Lattice // normSq x.val = 48} = 16773120 := by
  classical
  have bound (x : Lattice) (hx : normSq x.val = 8 * 6) (i : Fin 24) :
      -7 ≤ x.val i ∧ x.val i ≤ 7 := by
    have hs : x.val i ^ 2 ≤ normSq x.val :=
      single_le_sum (fun j _ => sq_nonneg (x.val j)) (mem_univ i)
    rw [hx] at hs
    constructor <;> by_contra! h <;> nlinarith
  change Nat.card {x : Lattice // normSq x.val = 8 * 6} = _
  rw [LeechShellCoordinates.card_vectors_from_choices 6 bound]
  simp_rw [per_word]
  rw [Fintype.sum_bool]
  have hterm (w : Codeword) :
      (if weight w.val = 8 then 4096 else if weight w.val = 12 then 2048 else 0) =
        (if weight w.val = 8 then 1 else 0) * 4096 + (if weight w.val = 12 then 1 else 0) * 2048 := by
    split_ifs <;> omega
  simp only [Bool.false_eq_true, ite_false, ite_true, hterm, sum_add_distrib, ← sum_mul,
    sum_boole, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id]
  have h8 := Fintype.card_subtype (fun w : Codeword => weight w.val = 8)
  have h12 := Fintype.card_subtype (fun w : Codeword => weight w.val = 12)
  rw [← h8, ← h12, card_octad, card_dodecad, card_codeword]
  decide

end LeechNorm48
