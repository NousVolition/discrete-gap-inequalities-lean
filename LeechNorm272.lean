import LeechNorm144

/-! # Leech lattice vectors of squared length 272

Each coordinate lies between −16 and 16. Count its possible values for each
Golay residue word, then sum over the five word weights.
-/
namespace LeechNorm272

open LeechLattice LeechMinimal LeechCodeCounts LeechSymmetry Finset

private theorem bounds (x : Lattice) (hx : normSq x.val = 272) (i : Fin 24) :
    -16 ≤ x.val i ∧ x.val i ≤ 16 := by
  have h := single_le_sum (f := fun j => x.val j ^ 2) (fun j _ => sq_nonneg (x.val j)) (mem_univ i)
  change x.val i ^ 2 ≤ normSq x.val at h
  rw [hx] at h
  have := abs_lt_of_sq_lt_sq' (h.trans_lt (by decide : (272 : ℤ) < 17 ^ 2)) (by decide : (0 : ℤ) ≤ 17)
  omega

/-- There are 3,249,631,112,232,960 Leech lattice vectors of squared length 272. -/
theorem card_norm272_vectors : Nat.card {x : Lattice // normSq x.val = 272} = 3249631112232960 := by
  apply (LeechShellCoordinates.card_vectors_nine_choices 34 (fun x hx i => by
    have := bounds x hx i
    omega)).trans
  let count (p : Bool) (k : ℕ) := LeechCoordinateAlphabet.tally .nine p (24 - k) k
    (if p then 34 - 3 else 34 - (k : ℤ) / 2) (if p then 1 else 0)
  change (∑ p : Bool, ∑ w : Codeword, count p (weight w.val)) = _
  rw [Fintype.sum_bool, sum_by_weight (count true), sum_by_weight (count false)]
  simp (disch := decide) only [count, LeechNorm80Count.choices272]
  decide

end LeechNorm272
