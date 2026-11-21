import LeechNorm144

/-! # Leech lattice vectors of squared length 288

Each coordinate lies between −16 and 16. Count its possible values for each
Golay residue word, then sum over the five word weights.
-/
namespace LeechNorm288

open LeechLattice LeechMinimal LeechCodeCounts LeechSymmetry Finset

private theorem bounds (x : Lattice) (hx : normSq x.val = 288) (i : Fin 24) :
    -16 ≤ x.val i ∧ x.val i ≤ 16 := by
  have h := single_le_sum (f := fun j => x.val j ^ 2) (fun j _ => sq_nonneg (x.val j)) (mem_univ i)
  change x.val i ^ 2 ≤ normSq x.val at h
  rw [hx] at h
  have := abs_lt_of_sq_lt_sq' (h.trans_lt (by decide : (288 : ℤ) < 17 ^ 2)) (by decide : (0 : ℤ) ≤ 17)
  omega

/-- There are 6,096,882,661,243,920 Leech lattice vectors of squared length 288. -/
theorem card_norm288_vectors : Nat.card {x : Lattice // normSq x.val = 288} = 6096882661243920 := by
  apply (LeechShellCoordinates.card_vectors_nine_choices 36 (fun x hx i => by
    have := bounds x hx i
    omega)).trans
  let count (p : Bool) (k : ℕ) := LeechCoordinateAlphabet.tally .nine p (24 - k) k
    (if p then 36 - 3 else 36 - (k : ℤ) / 2) (if p then 1 else 0)
  change (∑ p : Bool, ∑ w : Codeword, count p (weight w.val)) = _
  rw [Fintype.sum_bool, sum_by_weight (count true), sum_by_weight (count false)]
  simp (disch := decide) only [count, LeechNorm80Count.choices288]
  decide

end LeechNorm288
