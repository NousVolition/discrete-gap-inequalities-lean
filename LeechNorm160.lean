import LeechNorm144

/-! # Leech lattice vectors of squared length 160

The coordinates lie between −12 and 12. In the residue class zero modulo four
both −12 and 12 can occur. The coordinate count includes both signs.
-/
namespace LeechNorm160

open LeechLattice LeechMinimal LeechCodeCounts LeechSymmetry Finset

private theorem bounds (x : Lattice) (hx : normSq x.val = 160) (i : Fin 24) :
    -12 ≤ x.val i ∧ x.val i ≤ 12 := by
  have h := single_le_sum (f := fun j => x.val j ^ 2) (fun j _ => sq_nonneg (x.val j)) (mem_univ i)
  change x.val i ^ 2 ≤ normSq x.val at h
  rw [hx] at h
  have := abs_lt_of_sq_lt_sq' (h.trans_lt (by decide : (160 : ℤ) < 13 ^ 2)) (by decide : (0 : ℤ) ≤ 13)
  omega

/-- There are 9,486,551,299,680 Leech lattice vectors of squared length 160. -/
theorem card_norm160_vectors : Nat.card {x : Lattice // normSq x.val = 160} = 9486551299680 := by
  apply (LeechShellCoordinates.card_vectors_eight_choices 20 (fun x hx i => by
    have := bounds x hx i
    omega)).trans
  let count (p : Bool) (k : ℕ) := LeechCoordinateAlphabet.tally .eight p (24 - k) k
    (if p then 20 - 3 else 20 - (k : ℤ) / 2) (if p then 1 else 0)
  change (∑ p : Bool, ∑ w : Codeword, count p (weight w.val)) = _
  rw [Fintype.sum_bool, sum_by_weight (count true), sum_by_weight (count false)]
  simp (disch := decide) only [count, LeechNorm80Count.choices160]
  decide

end LeechNorm160
