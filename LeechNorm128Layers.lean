import LeechNorm128
import LeechNorm112Layers

/-! # Squared-length-128 layers along a shortest vector

Six positive layers come from earlier shells. The total and two coordinate
moments determine the inner layers. Negating a vector gives the other sign.
-/
namespace LeechLayers

open PlaygroundGolay PlaygroundLeech LeechLattice LeechSymmetry Finset
open LeechShellMoments (Shell diff)

abbrev PlayNorm128Vectors := PlayShell 128

private noncomputable instance : Fintype (Shell 128) := by
  have : Finite (Shell 128) := (Nat.card_pos_iff.mp
    (show 0 < Nat.card (Shell 128) by rw [LeechNorm128.card_norm128_vectors]; decide)).2
  exact Fintype.ofFinite _

private theorem shell_card128 : Fintype.card (Shell 128) = 814879774800 :=
  Nat.card_eq_fintype_card.symm.trans LeechNorm128.card_norm128_vectors

private def products128 : Finset ℤ := {0, 8, -8, 16, -16, 24, -24, 32, -32, 40, -40, 48, -48, 56, -56, 64, -64}

private theorem allowed128 (x : Shell 128) : 4 * diff x ∈ products128 := by
  obtain ⟨⟨q,hq⟩,lo,hi⟩ := reference_dot_bounds (by decide : (128 : ℤ) ≠ 32) x
  simp only [products128, mem_insert, mem_singleton]
  omega

private theorem outer_counts128 (s : PlayShortestVectors) :
    layerCount s 128 24 = 39253082112 ∧ layerCount s 128 32 = 9403968600 ∧
    layerCount s 128 40 = 1062195200 ∧ layerCount s 128 48 = 32788800 ∧
    layerCount s 128 56 = 47104 ∧ layerCount s 128 64 = 1 := by
  have h24 : Nat.card (PlayLayer s 128 24) = 39253082112 := by
    rw [Nat.card_congr (subtractAxis s 128 24 112 8 (by decide) (by decide))]
    simpa using card_norm112_dot_layer s 8
  have h32 : Nat.card (PlayLayer s 128 32) = 9403968600 := by
    rw [Nat.card_congr (subtractAxis s 128 32 96 0 (by decide) (by decide))]
    simpa using card_norm96_dot_layer s 0
  have h40 : Nat.card (PlayLayer s 128 40) = 1062195200 := by
    rw [Nat.card_congr (subtractAxis s 128 40 80 (-8) (by decide) (by decide))]
    simpa using card_norm80_dot_layer s (-8)
  have h48 : Nat.card (PlayLayer s 128 48) = 32788800 := by
    rw [Nat.card_congr (subtractAxis s 128 48 64 (-16) (by decide) (by decide))]
    simpa using card_norm64_dot_layer s (-16)
  have h56 : Nat.card (PlayLayer s 128 56) = 47104 := by
    rw [Nat.card_congr (subtractAxis s 128 56 48 (-24) (by decide) (by decide))]
    simpa using card_norm48_dot_layer s (-24)
  have h64 : Nat.card (PlayLayer s 128 64) = 1 := by
    let e : PlayShell 32 ≃ PlayShortestVectors :=
      Equiv.subtypeEquivRight fun v => (play_shortest_iff_norm32 v).symm
    let layer : PlayLayer s 32 (-32) ≃ {v : PlayShortestVectors // dot s.val v.val = -32} :=
      Equiv.subtypeEquiv e fun _ => Iff.rfl
    rw [Nat.card_congr (subtractAxis s 128 64 32 (-32) (by decide) (by decide)), Nat.card_congr layer]
    exact card_dot_neg_thirty_two s
  let cast := fun n : ℕ => (n : ℤ)
  exact ⟨congrArg cast h24, congrArg cast h32, congrArg cast h40,
    congrArg cast h48, congrArg cast h56, congrArg cast h64⟩

private theorem inner_counts128 (s : PlayShortestVectors) :
    layerCount s 128 0 = 192825064350 ∧ layerCount s 128 8 = 163357849600 ∧ layerCount s 128 16 = 97917423808 := by
  obtain ⟨h24, h32, h40, h48, h56, h64⟩ := outer_counts128 s
  obtain ⟨h2, h4⟩ := LeechShellMoments.diff_moments 128
  rw [shell_card128] at h2 h4
  have total := sum_by_layers 128 products128 allowed128 s (fun _ => 1)
  have second := sum_by_layers 128 products128 allowed128 s (fun k => (k / 4) ^ 2)
  have fourth := sum_by_layers 128 products128 allowed128 s (fun k => (k / 4) ^ 4)
  have cancel (d : ℤ) : 4*d/4 = d := by omega
  simp only [cancel] at second fourth
  norm_num [products128, sum_insert, opposite_layer_count, h24, h32, h40, h48, h56, h64, shell_card128] at total second fourth
  omega

/-- Count the vectors of squared length 128 at every integer dot product with any shortest vector. -/
theorem card_norm128_dot_layer (s : PlayShortestVectors) (k : ℤ) :
    Nat.card {v : PlayNorm128Vectors // dot s.val v.val = k} =
      if k = 0 then 192825064350
      else if k = 8 ∨ k = -8 then 163357849600
      else if k = 16 ∨ k = -16 then 97917423808
      else if k = 24 ∨ k = -24 then 39253082112
      else if k = 32 ∨ k = -32 then 9403968600
      else if k = 40 ∨ k = -40 then 1062195200
      else if k = 48 ∨ k = -48 then 32788800
      else if k = 56 ∨ k = -56 then 47104
      else if k = 64 ∨ k = -64 then 1
      else 0 := by
  classical
  apply Int.ofNat_inj.mp
  change layerCount s 128 k = _
  by_cases hk : k ∈ products128
  · obtain ⟨h0, h8, h16⟩ := inner_counts128 s
    obtain ⟨h24, h32, h40, h48, h56, h64⟩ := outer_counts128 s
    simp only [products128, mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [opposite_layer_count, h0, h8, h16, h24, h32, h40, h48, h56, h64]
  · have noHits : (univ : Finset (Shell 128)).filter (fun x => 4 * diff x = k) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x _ hx
      exact hk (hx ▸ allowed128 x)
    rw [← reference_layer_card, noHits]
    simp only [products128, mem_insert, mem_singleton, not_or] at hk
    obtain ⟨h0,h8,hn8,h16,hn16,h24,hn24,h32,hn32,h40,hn40,h48,hn48,h56,hn56,h64,hn64⟩ := hk
    simp [h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48, h56, hn56, h64, hn64]

end LeechLayers
