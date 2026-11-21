import LeechShellCoordinates
import LeechDodecadCount
import LeechNorm80Count
import LeechOppositePairs

/-! # Leech lattice vectors and opposite pairs at squared length 80

The coordinates are integers in the project's scaling. Their squared length 80
corresponds to squared length 10 in the usual normalization. -/
namespace LeechNorm80

open LeechLattice LeechMinimal LeechCodeCounts LeechSymmetry Finset

private theorem coord_le_seven (x : Lattice) (hx : normSq x.val = 80) (i : Fin 24) :
    x.val i ≤ 7 := by
  have hs : x.val i ^ 2 ≤ normSq x.val :=
    single_le_sum (fun j _ => sq_nonneg (x.val j)) (mem_univ i)
  rw [hx] at hs
  by_contra! h
  have hi : x.val i = 8 := by
    have : x.val i ≤ 8 := by by_contra! h'; nlinarith
    omega
  have hn : normSq (x.val - axis i) = 16 := by
    norm_num [normSq_sub, hx, axis_norm, dot_axis, hi]
  have hnz : x.val - axis i ≠ 0 := by
    intro hz
    rw [hz] at hn
    norm_num [normSq] at hn
  have hl := leech_norm_ge_32 _ (leechLattice.sub_mem x.property (axis_mem i)) hnz
  change 32 ≤ normSq (x.val - axis i) at hl
  omega

/-- Each coordinate lies between −7 and 7. Removing an entry of magnitude 8 would leave squared length 16. -/
theorem coordinate_bounds (x : Lattice) (hx : normSq x.val = 80) (i : Fin 24) :
    -7 ≤ x.val i ∧ x.val i ≤ 7 := by
  have hn : normSq (-x).val = 80 := (normSq_neg x.val).trans hx
  have h := coord_le_seven (-x) hn i
  change -(x.val i) ≤ 7 at h
  exact ⟨by omega, coord_le_seven x hx i⟩

private def flip : Codeword ≃ Codeword where
  toFun w := ⟨fun i => !w.val i, isGolayWord_not w.property⟩
  invFun w := ⟨fun i => !w.val i, isGolayWord_not w.property⟩
  left_inv w := Subtype.ext (funext fun i => Bool.not_not (w.val i))
  right_inv w := Subtype.ext (funext fun i => Bool.not_not (w.val i))

private theorem flip_weight (w : Codeword) : weight (flip w).val = 24 - weight w.val := by
  have hc : (univ.filter fun i => (!w.val i) = true) = (univ.filter fun i => w.val i = true)ᶜ := by
    ext i
    simp
  change (univ.filter fun i => (!w.val i) = true).card = 24 - _
  rw [hc, card_compl]
  rfl

private theorem weight_le (w : Codeword) : weight w.val ≤ 24 := by
  simpa [weight] using (card_filter_le univ (fun i => w.val i = true))

theorem word_weights (w : Codeword) :
    weight w.val = 0 ∨ weight w.val = 8 ∨ weight w.val = 12 ∨ weight w.val = 16 ∨ weight w.val = 24 := by
  have lower (v : Codeword) : weight v.val = 0 ∨ 8 ≤ weight v.val := by
    by_cases h : ∃ i, v.val i = true
    · exact Or.inr (golay_weight_ge_eight v.property h)
    · left; simp [weight, show ∀ i, v.val i ≠ true by simpa using h]
  have hf := lower (flip w)
  rw [flip_weight] at hf
  have hmin := lower w
  have h4 : weight w.val % 4 = 0 := golay_weight_mod_four w.property
  have hle := weight_le w
  omega

/-- Flipping all 24 bits pairs the words of weight 16 with the 759 octads. -/
theorem card_weight_sixteen : Fintype.card {w : Codeword // weight w.val = 16} = 759 := by
  let e : {w : Codeword // weight w.val = 16} ≃ Octad :=
    Equiv.subtypeEquiv flip (fun w => by
      rw [flip_weight]
      omega)
  exact (Fintype.card_congr e).trans card_octad

private theorem per_word (p : Bool) (w : Codeword) :
    LeechNorm48Count.tally p (24 - weight w.val) (weight w.val)
      (if p then 10 - 3 else 10 - (weight w.val : ℤ) / 2) (if p then 1 else 0) =
      if p then 565248 else LeechNorm80Count.evenPerWord (weight w.val) := by
  cases p with
  | false => exact LeechNorm80Count.even_choices (word_weights w)
  | true => exact LeechNorm80Count.odd_choices _ (weight_le w)

/-- The Leech lattice has 4,629,381,120 vectors of squared length 80. -/
theorem card_norm80_vectors : Nat.card {x : Lattice // normSq x.val = 80} = 4629381120 := by
  classical
  change Nat.card {x : Lattice // normSq x.val = 8 * 10} = _
  rw [LeechShellCoordinates.card_vectors_from_choices 10 coordinate_bounds]
  simp_rw [per_word]
  rw [Fintype.sum_bool]
  have hterm (w : Codeword) : LeechNorm80Count.evenPerWord (weight w.val) =
      (if weight w.val = 8 then 1 else 0) * 606208 +
      (if weight w.val = 12 then 1 else 0) * 565248 +
      (if weight w.val = 16 then 1 else 0) * 524288 := by
    unfold LeechNorm80Count.evenPerWord
    split_ifs <;> omega
  simp only [Bool.false_eq_true, ite_false, ite_true, hterm, sum_add_distrib, ← sum_mul,
    sum_boole, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id]
  have h8 := Fintype.card_subtype (fun w : Codeword => weight w.val = 8)
  have h12 := Fintype.card_subtype (fun w : Codeword => weight w.val = 12)
  have h16 := Fintype.card_subtype (fun w : Codeword => weight w.val = 16)
  rw [← h8, ← h12, ← h16, card_octad, card_dodecad, card_weight_sixteen, card_codeword]
  decide

/-- Counting each vector and its negative together gives 2,314,690,560 pairs. -/
theorem card_norm80_opposite_pairs :
    Nat.card {s : Finset Lattice // LeechOppositePairs.IsOppositePair 80 s} = 2314690560 := by
  rw [LeechOppositePairs.card_opposite_pairs (by decide : (0 : ℤ) < 80), card_norm80_vectors]

end LeechNorm80
