import LeechNorm144

/-! # Leech lattice vectors of squared length 240

Each coordinate lies between −15 and 15. For each Golay weight, count the
coordinate choices of that squared length with the required sum modulo eight.
-/
namespace LeechNorm240

open LeechLattice LeechMinimal LeechCodeCounts LeechSymmetry Finset

private theorem bounds (x : Lattice) (hx : normSq x.val = 240) (i : Fin 24) :
    -15 ≤ x.val i ∧ x.val i ≤ 15 := by
  have h := single_le_sum (f := fun j => x.val j ^ 2) (fun j _ => sq_nonneg (x.val j)) (mem_univ i)
  change x.val i ^ 2 ≤ normSq x.val at h
  rw [hx] at h
  have := abs_lt_of_sq_lt_sq' (h.trans_lt (by decide : (240 : ℤ) < 16 ^ 2)) (by decide : (0 : ℤ) ≤ 16)
  omega

/-- There are 820,166,620,815,360 Leech lattice vectors of squared length 240. -/
theorem card_norm240_vectors : Nat.card {x : Lattice // normSq x.val = 240} = 820166620815360 := by
  apply (LeechShellCoordinates.card_vectors_eight_choices 30 (fun x hx i => by
    have := bounds x hx i
    omega)).trans
  let count (p : Bool) (k : ℕ) := LeechCoordinateAlphabet.tally .eight p (24 - k) k
    (if p then 30 - 3 else 30 - (k : ℤ) / 2) (if p then 1 else 0)
  change (∑ p : Bool, ∑ w : Codeword, count p (weight w.val)) = _
  rw [Fintype.sum_bool, sum_by_weight (count true), sum_by_weight (count false)]
  simp (disch := decide) only [count, LeechNorm80Count.choices240]
  decide

end LeechNorm240
