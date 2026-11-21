import LeechNorm144

/-! # Leech lattice vectors of squared length 320

Each coordinate lies between −17 and 17. Count its possible values for each
Golay residue word, then sum over the five word weights.
-/
namespace LeechNorm320

open LeechLattice LeechMinimal LeechCodeCounts LeechSymmetry Finset

private theorem bounds (x : Lattice) (hx : normSq x.val = 320) (i : Fin 24) :
    -17 ≤ x.val i ∧ x.val i ≤ 17 := by
  have h := single_le_sum (f := fun j => x.val j ^ 2) (fun j _ => sq_nonneg (x.val j)) (mem_univ i)
  change x.val i ^ 2 ≤ normSq x.val at h
  rw [hx] at h
  have := abs_lt_of_sq_lt_sq' (h.trans_lt (by decide : (320 : ℤ) < 18 ^ 2)) (by decide : (0 : ℤ) ≤ 18)
  omega

/-- There are 19,428,439,855,275,360 Leech lattice vectors of squared length 320. -/
theorem card_norm320_vectors : Nat.card {x : Lattice // normSq x.val = 320} = 19428439855275360 := by
  apply (LeechShellCoordinates.card_vectors_nine_choices 40 (fun x hx i => by
    have := bounds x hx i
    omega)).trans
  let count (p : Bool) (k : ℕ) := LeechCoordinateAlphabet.tally .nine p (24 - k) k
    (if p then 40 - 3 else 40 - (k : ℤ) / 2) (if p then 1 else 0)
  change (∑ p : Bool, ∑ w : Codeword, count p (weight w.val)) = _
  rw [Fintype.sum_bool, sum_by_weight (count true), sum_by_weight (count false)]
  simp (disch := decide) only [count, LeechNorm80Count.choices320]
  decide

end LeechNorm320
