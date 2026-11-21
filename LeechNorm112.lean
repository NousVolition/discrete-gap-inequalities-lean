import LeechNorm80

/-! # Leech lattice vectors of squared length 112

Every coordinate lies between −9 and 9. Five choices per Golay residue cover
this range. The coordinate count checks the squared length and the sum modulo 8.
-/
namespace LeechNorm112

open LeechLattice LeechMinimal LeechCodeCounts LeechSymmetry Finset

private theorem coord_upper (x : Lattice) (hx : normSq x.val = 112) (i : Fin 24) : x.val i ≤ 9 := by
  have nz : x.val - axis i ≠ 0 := by
    intro h
    have he := congrArg normSq (sub_eq_zero.mp h)
    rw [hx, axis_norm] at he
    omega
  have h := leech_norm_ge_32 _ (leechLattice.sub_mem x.property (axis_mem i)) nz
  change 32 ≤ normSq (x.val - axis i) at h
  rw [normSq_sub, hx, axis_norm, dot_axis] at h
  omega

private theorem bounds (x : Lattice) (hx : normSq x.val = 112) (i : Fin 24) :
    -9 ≤ x.val i ∧ x.val i ≤ 9 := by
  have hn := coord_upper (-x) ((normSq_neg x.val).trans hx) i
  change -(x.val i) ≤ 9 at hn
  exact ⟨by omega, coord_upper x hx i⟩

private def perWord (p : Bool) (k : ℕ) : ℕ :=
  if p then 22892544 else if k = 8 then 22716416 else if k = 12 then 22892544
  else if k = 16 then 23068672 else 0

private theorem sum_words {α : Type} [Fintype α] (wgt : α → ℕ)
    (words : Fintype.card α = 4096) (eight : Nat.card {w // wgt w = 8} = 759)
    (twelve : Nat.card {w // wgt w = 12} = 2576) (sixteen : Nat.card {w // wgt w = 16} = 759) :
    (∑ p : Bool, ∑ w : α, perWord p (wgt w)) = 187489935360 := by
  have term (k : ℕ) : perWord false k =
      (if k = 8 then 1 else 0) * 22716416 + (if k = 12 then 1 else 0) * 22892544 +
      (if k = 16 then 1 else 0) * 23068672 := by
    simp only [perWord, Bool.false_eq_true, ite_false]
    split_ifs <;> omega
  have odd (k : ℕ) : perWord true k = 22892544 := rfl
  rw [Fintype.sum_bool]
  simp only [odd, term, sum_add_distrib, ← sum_mul, sum_boole, sum_const, card_univ,
    nsmul_eq_mul, Nat.cast_id]
  have card (k : ℕ) := (Nat.card_eq_fintype_card (α := {w // wgt w = k})).trans
    (Fintype.card_subtype (fun w : α => wgt w = k))
  rw [← card 8, ← card 12, ← card 16, eight, twelve, sixteen, words]
  decide

/-- There are 187,489,935,360 Leech lattice vectors of squared length 112. -/
theorem card_norm112_vectors : Nat.card {x : Lattice // normSq x.val = 112} = 187489935360 := by
  apply (LeechShellCoordinates.card_vectors_five_choices 14 bounds).trans
  have eight : Nat.card Octad = 759 := Nat.card_eq_fintype_card.trans card_octad
  have twelve : Nat.card Dodecad = 2576 := Nat.card_eq_fintype_card.trans card_dodecad
  have sixteen := Nat.card_eq_fintype_card.trans LeechNorm80.card_weight_sixteen
  refine Eq.trans ?_ (sum_words (fun w : Codeword => weight w.val) card_codeword eight twelve sixteen)
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro w _
  exact LeechNorm80Count.choices112 p (LeechNorm80.word_weights w)

end LeechNorm112
