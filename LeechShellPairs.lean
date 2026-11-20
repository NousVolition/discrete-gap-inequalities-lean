import LeechOppositePairs
import LeechCoordinateFrames

/-! # Opposite pairs at squared lengths 32 and 64 in the Leech lattice -/

namespace LeechOppositePairs

open LeechLattice LeechMinimal LeechSymmetry

/-- The 196,560 shortest vectors form 98,280 opposite pairs. -/
theorem card_norm32_opposite_pairs :
    Nat.card {s : Finset Lattice // IsOppositePair 32 s} = 98280 := by
  let e : {x : Lattice // normSq x.val = 32} ≃ MinimalVectors :=
    Equiv.subtypeSubtypeEquivSubtypeInter InLeech (fun x => normSq x = 32)
  rw [card_opposite_pairs (by decide : (0 : ℤ) < 32), Nat.card_congr e,
    Nat.card_eq_fintype_card, leech_kissing_number]

/-- The 398,034,000 vectors of squared length 64 form 199,017,000 opposite pairs. -/
theorem card_norm64_opposite_pairs :
    Nat.card {s : Finset Lattice // IsOppositePair 64 s} = 199017000 := by
  rw [card_opposite_pairs (by decide : (0 : ℤ) < 64), LeechCoordinateFrames.card_norm64_vectors]

end LeechOppositePairs
