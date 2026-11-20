import ConwayOrder
import PlaygroundLeech

/-! # Layers perpendicular to a shortest vector in playground coordinates -/
namespace LeechLayers

open PlaygroundGolay PlaygroundLeech LeechLattice LeechMinimal LeechSymmetry

private theorem dot_toLean (s v : Vec) : dot (toLean s) (toLean v) = dot s v := by
  apply Fintype.sum_equiv coordinateEquiv.symm
  intro i
  rfl

private def toMinimal : PlayShortestVectors ≃ MinimalVectors :=
  Equiv.subtypeEquiv vectorEquiv (fun x => (shortest_correspondence x).trans (shortest_iff_norm32 _))

/-- Any shortest vector in the playground coordinates has 93,150 perpendicular shortest vectors. -/
theorem card_perpendicular (s : PlayShortestVectors) :
    Nat.card {v : PlayShortestVectors // dot s.val v.val = 0} = 93150 := by
  let e : {v : PlayShortestVectors // dot s.val v.val = 0} ≃ ConwayPairs.Partner (toMinimal s) :=
    Equiv.subtypeEquiv toMinimal (fun v => by
      change dot s.val v.val = 0 ↔ dot (toLean s.val) (toLean v.val) = 0
      rw [dot_toLean])
  exact (Nat.card_congr e).trans (ConwayOrder.card_partner _)

/-- A dot product of 24 or −24 would give a nonzero difference or sum of squared length 16. -/
theorem no_dot_twenty_four (s v : PlayShortestVectors) :
    dot s.val v.val ≠ 24 ∧ dot s.val v.val ≠ -24 := by
  obtain ⟨hs, ns⟩ := (play_shortest_iff_norm32 _).mp s.property
  obtain ⟨hv, nv⟩ := (play_shortest_iff_norm32 _).mp v.property
  have exclude (x : Vec) (hm : InPlayLeech x) (hn : normSq x = 16) : False := by
    have nz : x ≠ 0 := by intro h; simp [h, normSq] at hn
    have := play_norm_ge_32 x hm nz
    omega
  have sm := (lattice_correspondence _).mp hs
  have vm := (lattice_correspondence _).mp hv
  constructor
  · intro h
    apply exclude (s.val - v.val) ((lattice_correspondence _).mpr (leechLattice.sub_mem sm vm))
    rw [normSq_sub, ns, nv, h]
    decide
  · intro h
    apply exclude (s.val + v.val) ((lattice_correspondence _).mpr (leechLattice.add_mem sm vm))
    rw [normSq_add, ns, nv, h]
    decide

end LeechLayers
