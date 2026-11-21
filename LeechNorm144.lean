import LeechNorm96

/-! # Leech lattice vectors of squared length 144

A vector of squared length 144 has every coordinate between −11 and 11.
For each Golay word we count the coordinate choices with the required length and sum modulo 8.
-/
open LeechLattice LeechMinimal LeechCodeCounts LeechSymmetry Finset

namespace LeechCodeCounts

private theorem sum_five_weights {α : Type} [Fintype α] (wgt : α → ℕ) (f : ℕ → ℕ)
    (allowed : ∀ w, wgt w = 0 ∨ wgt w = 8 ∨ wgt w = 12 ∨ wgt w = 16 ∨ wgt w = 24)
    (zero : Nat.card {w // wgt w = 0} = 1) (eight : Nat.card {w // wgt w = 8} = 759)
    (twelve : Nat.card {w // wgt w = 12} = 2576) (sixteen : Nat.card {w // wgt w = 16} = 759)
    (full : Nat.card {w // wgt w = 24} = 1) :
    ∑ w, f (wgt w) = f 0 + 759 * f 8 + 2576 * f 12 + 759 * f 16 + f 24 := by
  have term (w : α) : f (wgt w) =
      (if wgt w = 0 then 1 else 0) * f 0 + (if wgt w = 8 then 1 else 0) * f 8 +
      (if wgt w = 12 then 1 else 0) * f 12 + (if wgt w = 16 then 1 else 0) * f 16 +
      (if wgt w = 24 then 1 else 0) * f 24 := by
    rcases allowed w with h | h | h | h | h <;> norm_num [h]
  simp only [term, sum_add_distrib, ← sum_mul, sum_boole]
  have card (k : ℕ) := (Nat.card_eq_fintype_card (α := {w // wgt w = k})).trans
    (Fintype.card_subtype (fun w : α => wgt w = k))
  rw [← card 0, ← card 8, ← card 12, ← card 16, ← card 24, zero, eight, twelve, sixteen, full]
  simp

/-- Sum a function of the weight over all Golay words. -/
theorem sum_by_weight (f : ℕ → ℕ) :
    ∑ w : Codeword, f (weight w.val) = f 0 + 759 * f 8 + 2576 * f 12 + 759 * f 16 + f 24 := by
  have eight : Nat.card Octad = 759 := Nat.card_eq_fintype_card.trans card_octad
  have twelve : Nat.card Dodecad = 2576 := Nat.card_eq_fintype_card.trans card_dodecad
  exact sum_five_weights _ f LeechNorm80.word_weights (Nat.card_eq_fintype_card.trans LeechNorm96.weight_zero)
    eight twelve (Nat.card_eq_fintype_card.trans LeechNorm80.card_weight_sixteen)
    (Nat.card_eq_fintype_card.trans LeechNorm96.weight_full)

end LeechCodeCounts

namespace LeechNorm144

private theorem coord_upper (x : Lattice) (hx : normSq x.val = 144) (i : Fin 24) : x.val i ≤ 11 := by
  have nz : x.val - axis i ≠ 0 := by
    intro h
    have he := congrArg normSq (sub_eq_zero.mp h)
    rw [hx, axis_norm] at he
    omega
  have h := leech_norm_ge_32 _ (leechLattice.sub_mem x.property (axis_mem i)) nz
  change 32 ≤ normSq (x.val - axis i) at h
  rw [normSq_sub, hx, axis_norm, dot_axis] at h
  omega

private theorem bounds (x : Lattice) (hx : normSq x.val = 144) (i : Fin 24) :
    -11 ≤ x.val i ∧ x.val i ≤ 11 := by
  have hn := coord_upper (-x) ((normSq_neg x.val).trans hx) i
  change -(x.val i) ≤ 11 at hn
  exact ⟨by omega, coord_upper x hx i⟩

private def perWord (p : Bool) (k : ℕ) : ℕ :=
  if p then 363315200 else if k = 8 then 362774528 else if k = 12 then 363315200
  else if k = 16 then 363855872 else 0

/-- There are 2,975,551,488,000 Leech lattice vectors of squared length 144. -/
theorem card_norm144_vectors : Nat.card {x : Lattice // normSq x.val = 144} = 2975551488000 := by
  have cover (x : Lattice) (hx : normSq x.val = 8 * 18) (i : Fin 24) :
      -11 ≤ x.val i ∧ x.val i ≤ 12 := by
    have := bounds x hx i
    omega
  apply (LeechShellCoordinates.card_vectors_in_six_choice_range 18 cover).trans
  calc
    _ = ∑ p : Bool, ∑ w : Codeword, perWord p (weight w.val) := by
      apply sum_congr rfl
      intro p _
      apply sum_congr rfl
      intro w _
      exact LeechNorm80Count.choices144 p (LeechNorm80.word_weights w)
    _ = 2975551488000 := by
      rw [Fintype.sum_bool, sum_by_weight (perWord true), sum_by_weight (perWord false)]
      decide

end LeechNorm144
