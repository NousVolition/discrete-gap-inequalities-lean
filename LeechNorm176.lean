import LeechNorm144

/-! # Leech lattice vectors of squared length 176

Each coordinate has square at most 176. The eight choices for each residue
class modulo four cover all the coordinates that can occur.
-/
namespace LeechNorm176

open LeechLattice LeechMinimal LeechCodeCounts LeechSymmetry Finset

private theorem bounds (x : Lattice) (hx : normSq x.val = 176) (i : Fin 24) :
    -13 ≤ x.val i ∧ x.val i ≤ 13 := by
  have h := single_le_sum (f := fun j => x.val j ^ 2) (fun j _ => sq_nonneg (x.val j)) (mem_univ i)
  change x.val i ^ 2 ≤ normSq x.val at h
  rw [hx] at h
  have := abs_lt_of_sq_lt_sq' (h.trans_lt (by decide : (176 : ℤ) < 14 ^ 2)) (by decide : (0 : ℤ) ≤ 14)
  omega

/-- There are 27,052,945,920,000 Leech lattice vectors of squared length 176. -/
theorem card_norm176_vectors : Nat.card {x : Lattice // normSq x.val = 176} = 27052945920000 := by
  apply (LeechShellCoordinates.card_vectors_eight_choices 22 (fun x hx i => by
    have := bounds x hx i
    omega)).trans
  let count (p : Bool) (k : ℕ) := LeechCoordinateAlphabet.tally .eight p (24 - k) k
    (if p then 22 - 3 else 22 - (k : ℤ) / 2) (if p then 1 else 0)
  change (∑ p : Bool, ∑ w : Codeword, count p (weight w.val)) = _
  rw [Fintype.sum_bool, sum_by_weight (count true), sum_by_weight (count false)]
  simp (disch := decide) only [count, LeechNorm80Count.choices176]
  decide

end LeechNorm176
