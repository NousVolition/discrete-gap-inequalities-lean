import LeechNorm144

/-! # Leech lattice vectors of squared length 304

Each coordinate lies between −17 and 17. Count its possible values for each
Golay residue word, then sum over the five word weights.
-/
namespace LeechNorm304

open LeechLattice LeechMinimal LeechCodeCounts LeechSymmetry Finset

private theorem bounds (x : Lattice) (hx : normSq x.val = 304) (i : Fin 24) :
    -17 ≤ x.val i ∧ x.val i ≤ 17 := by
  have h := single_le_sum (f := fun j => x.val j ^ 2) (fun j _ => sq_nonneg (x.val j)) (mem_univ i)
  change x.val i ^ 2 ≤ normSq x.val at h
  rw [hx] at h
  have := abs_lt_of_sq_lt_sq' (h.trans_lt (by decide : (304 : ℤ) < 18 ^ 2)) (by decide : (0 : ℤ) ≤ 18)
  omega

/-- There are 11,045,500,816,896,000 Leech lattice vectors of squared length 304. -/
theorem card_norm304_vectors : Nat.card {x : Lattice // normSq x.val = 304} = 11045500816896000 := by
  apply (LeechShellCoordinates.card_vectors_nine_choices 38 (fun x hx i => by
    have := bounds x hx i
    omega)).trans
  let count (p : Bool) (k : ℕ) := LeechCoordinateAlphabet.tally .nine p (24 - k) k
    (if p then 38 - 3 else 38 - (k : ℤ) / 2) (if p then 1 else 0)
  change (∑ p : Bool, ∑ w : Codeword, count p (weight w.val)) = _
  rw [Fintype.sum_bool, sum_by_weight (count true), sum_by_weight (count false)]
  simp (disch := decide) only [count, LeechNorm80Count.choices304]
  decide

end LeechNorm304
