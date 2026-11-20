import LeechOctadCount

namespace LeechCodeCounts

open GolayMatrixDistance LeechLattice Finset

/-- Golay codewords with twelve ones. -/
abbrev Dodecad := {w : Codeword // weight w.val = 12}

/-- The weight-twelve messages of the existing encoder count distinct dodecads. -/
theorem card_dodecad : Fintype.card Dodecad = 2576 := by
  let e : {m : Fin 4096 // popcount24 (encodeNat m.val) = 12} ≃ Dodecad :=
    Equiv.subtypeEquiv codeEquiv (fun m => by
      change popcount24 (encodeNat m.val) = 12 ↔ weight (word (encodeNat m.val)) = 12
      rw [weight, ← popcount24_eq_card])
  rw [← Fintype.card_congr e, Fintype.card_subtype]
  set_option maxRecDepth 65536 in
  set_option maxHeartbeats 4000000 in
    decide +kernel

end LeechCodeCounts
