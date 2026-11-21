import LeechNorm96

/-! # Leech lattice vectors of squared length 128

Every coordinate lies between −10 and 10. Six choices per Golay residue cover
this range. The coordinate count checks the squared length and the sum modulo 8.
-/
namespace LeechNorm128

open LeechLattice LeechMinimal LeechCodeCounts LeechSymmetry Finset

private theorem coord_upper (x : Lattice) (hx : normSq x.val = 128) (i : Fin 24) : x.val i ≤ 10 := by
  have nz : x.val - axis i ≠ 0 := by
    intro h
    have he := congrArg normSq (sub_eq_zero.mp h)
    rw [hx, axis_norm] at he
    omega
  have h := leech_norm_ge_32 _ (leechLattice.sub_mem x.property (axis_mem i)) nz
  change 32 ≤ normSq (x.val - axis i) at h
  rw [normSq_sub, hx, axis_norm, dot_axis] at h
  omega

private theorem bounds (x : Lattice) (hx : normSq x.val = 128) (i : Fin 24) :
    -10 ≤ x.val i ∧ x.val i ≤ 10 := by
  have hn := coord_upper (-x) ((normSq_neg x.val).trans hx) i
  change -(x.val i) ≤ 10 at hn
  exact ⟨by omega, coord_upper x hx i⟩

private def perWord (p : Bool) (k : ℕ) : ℕ :=
  if p then 99448320 else if k = 0 then 195082320 else if k = 8 then 98902016
  else if k = 12 then 99483648 else if k = 16 then 99876864 else if k = 24 then 201326592 else 0

set_option maxRecDepth 8192 in
private theorem sum_words {α : Type} [Fintype α] (wgt : α → ℕ) (words : Fintype.card α = 4096)
    (zero : Nat.card {w // wgt w = 0} = 1) (eight : Nat.card {w // wgt w = 8} = 759)
    (twelve : Nat.card {w // wgt w = 12} = 2576) (sixteen : Nat.card {w // wgt w = 16} = 759)
    (full : Nat.card {w // wgt w = 24} = 1) :
    (∑ p : Bool, ∑ w : α, perWord p (wgt w)) = 814879774800 := by
  have term (k : ℕ) : perWord false k =
      (if k = 0 then 1 else 0) * 195082320 + (if k = 8 then 1 else 0) * 98902016 +
      (if k = 12 then 1 else 0) * 99483648 + (if k = 16 then 1 else 0) * 99876864 +
      (if k = 24 then 1 else 0) * 201326592 := by
    simp only [perWord, Bool.false_eq_true, ite_false]
    split_ifs <;> omega
  have odd (k : ℕ) : perWord true k = 99448320 := rfl
  rw [Fintype.sum_bool]
  simp only [odd, term, sum_add_distrib, ← sum_mul, sum_boole, sum_const, card_univ,
    nsmul_eq_mul, Nat.cast_id]
  have card (k : ℕ) := (Nat.card_eq_fintype_card (α := {w // wgt w = k})).trans
    (Fintype.card_subtype (fun w : α => wgt w = k))
  rw [← card 0, ← card 8, ← card 12, ← card 16, ← card 24, zero, eight, twelve, sixteen, full, words]
  decide

/-- There are 814,879,774,800 Leech lattice vectors of squared length 128. -/
theorem card_norm128_vectors : Nat.card {x : Lattice // normSq x.val = 128} = 814879774800 := by
  apply (LeechShellCoordinates.card_vectors_six_choices 16 bounds).trans
  have zero := Nat.card_eq_fintype_card.trans LeechNorm96.weight_zero
  have eight : Nat.card Octad = 759 := Nat.card_eq_fintype_card.trans card_octad
  have twelve : Nat.card Dodecad = 2576 := Nat.card_eq_fintype_card.trans card_dodecad
  have sixteen := Nat.card_eq_fintype_card.trans LeechNorm80.card_weight_sixteen
  have full := Nat.card_eq_fintype_card.trans LeechNorm96.weight_full
  refine Eq.trans ?_ (sum_words (fun w : Codeword => weight w.val) card_codeword zero eight twelve sixteen full)
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro w _
  exact LeechNorm80Count.choices128 p (LeechNorm80.word_weights w)

end LeechNorm128
