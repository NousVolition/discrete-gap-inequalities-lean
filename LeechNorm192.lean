import LeechNorm144

/-! # Leech lattice vectors of squared length 192

Each coordinate lies between −13 and 13. For each Golay weight, count the
coordinate choices of that squared length with the required sum modulo eight.
-/
namespace LeechNorm192

open LeechLattice LeechMinimal LeechCodeCounts LeechSymmetry Finset

private theorem bounds (x : Lattice) (hx : normSq x.val = 192) (i : Fin 24) :
    -13 ≤ x.val i ∧ x.val i ≤ 13 := by
  have h := single_le_sum (f := fun j => x.val j ^ 2) (fun j _ => sq_nonneg (x.val j)) (mem_univ i)
  change x.val i ^ 2 ≤ normSq x.val at h
  rw [hx] at h
  have := abs_lt_of_sq_lt_sq' (h.trans_lt (by decide : (192 : ℤ) < 14 ^ 2)) (by decide : (0 : ℤ) ≤ 14)
  omega

/-- There are 70,486,236,999,360 Leech lattice vectors of squared length 192. -/
theorem card_norm192_vectors : Nat.card {x : Lattice // normSq x.val = 192} = 70486236999360 := by
  apply (LeechShellCoordinates.card_vectors_eight_choices 24 (fun x hx i => by
    have := bounds x hx i
    omega)).trans
  let count (p : Bool) (k : ℕ) := LeechCoordinateAlphabet.tally .eight p (24 - k) k
    (if p then 24 - 3 else 24 - (k : ℤ) / 2) (if p then 1 else 0)
  change (∑ p : Bool, ∑ w : Codeword, count p (weight w.val)) = _
  rw [Fintype.sum_bool, sum_by_weight (count true), sum_by_weight (count false)]
  simp (disch := decide) only [count, LeechNorm80Count.choices192]
  decide

end LeechNorm192
