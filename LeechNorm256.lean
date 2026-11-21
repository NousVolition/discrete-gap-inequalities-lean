import LeechNorm144

/-! # Leech lattice vectors of squared length 256

Each coordinate lies between −16 and 16. The ninth choice for residue zero
includes +16 alongside −16. Sum the coordinate counts over the five Golay weights.
-/
namespace LeechNorm256

open LeechLattice LeechMinimal LeechCodeCounts LeechSymmetry Finset

private theorem bounds (x : Lattice) (hx : normSq x.val = 256) (i : Fin 24) :
    -16 ≤ x.val i ∧ x.val i ≤ 16 := by
  have h := single_le_sum (f := fun j => x.val j ^ 2) (fun j _ => sq_nonneg (x.val j)) (mem_univ i)
  change x.val i ^ 2 ≤ normSq x.val at h
  rw [hx] at h
  have := abs_lt_of_sq_lt_sq' (h.trans_lt (by decide : (256 : ℤ) < 17 ^ 2)) (by decide : (0 : ℤ) ≤ 17)
  omega

/-- There are 1,668,890,090,322,000 Leech lattice vectors of squared length 256. -/
theorem card_norm256_vectors : Nat.card {x : Lattice // normSq x.val = 256} = 1668890090322000 := by
  apply (LeechShellCoordinates.card_vectors_nine_choices 32 (fun x hx i => by
    have := bounds x hx i
    omega)).trans
  let count (p : Bool) (k : ℕ) := LeechCoordinateAlphabet.tally .nine p (24 - k) k
    (if p then 32 - 3 else 32 - (k : ℤ) / 2) (if p then 1 else 0)
  change (∑ p : Bool, ∑ w : Codeword, count p (weight w.val)) = _
  rw [Fintype.sum_bool, sum_by_weight (count true), sum_by_weight (count false)]
  simp (disch := decide) only [count, LeechNorm80Count.choices256]
  decide

end LeechNorm256
