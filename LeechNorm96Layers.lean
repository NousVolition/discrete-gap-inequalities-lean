import LeechNorm96
import LeechNorm80Layers

/-! # Squared-length-96 layers along a shortest vector

Four positive layers come from earlier shells. The total and two coordinate
moments determine the inner layers. Negating a vector gives the other sign.
-/
namespace LeechLayers

open PlaygroundGolay PlaygroundLeech LeechLattice LeechSymmetry Finset
open LeechShellMoments (Shell diff)

abbrev PlayNorm96Vectors := PlayShell 96

private noncomputable instance : Fintype (Shell 96) := by
  have : Finite (Shell 96) := (Nat.card_pos_iff.mp
    (show 0 < Nat.card (Shell 96) by rw [LeechNorm96.card_norm96_vectors]; decide)).2
  exact Fintype.ofFinite _

private theorem shell_card96 : Fintype.card (Shell 96) = 34417656000 :=
  Nat.card_eq_fintype_card.symm.trans LeechNorm96.card_norm96_vectors

private def products96 : Finset ℤ := {0, 8, -8, 16, -16, 24, -24, 32, -32, 40, -40, 48, -48}

private theorem allowed96 (x : Shell 96) : 4 * diff x ∈ products96 := by
  obtain ⟨⟨q,hq⟩,lo,hi⟩ := reference_dot_bounds (by decide : (96 : ℤ) ≠ 32) x
  simp only [products96, mem_insert, mem_singleton]
  omega

private theorem outer_counts96 (s : PlayShortestVectors) :
    layerCount s 96 24 = 1062195200 ∧ layerCount s 96 32 = 133204500 ∧
    layerCount s 96 40 = 4147200 ∧ layerCount s 96 48 = 4600 := by
  have a : Nat.card (PlayLayer s 96 24) = 1062195200 := by
    rw [Nat.card_congr (subtractAxis s 96 24 80 8 (by decide) (by decide))]
    simpa using card_norm80_dot_layer s 8
  have b : Nat.card (PlayLayer s 96 32) = 133204500 := by
    rw [Nat.card_congr (subtractAxis s 96 32 64 0 (by decide) (by decide))]
    simpa using card_norm64_dot_layer s 0
  have c : Nat.card (PlayLayer s 96 40) = 4147200 := by
    rw [Nat.card_congr (subtractAxis s 96 40 48 (-8) (by decide) (by decide))]
    simpa using card_norm48_dot_layer s (-8)
  have d : Nat.card (PlayLayer s 96 48) = 4600 := by
    let e : PlayShell 32 ≃ PlayShortestVectors :=
      Equiv.subtypeEquivRight fun v => (play_shortest_iff_norm32 v).symm
    let layer : PlayLayer s 32 (-16) ≃ {v : PlayShortestVectors // dot s.val v.val = -16} :=
      Equiv.subtypeEquiv e fun _ => Iff.rfl
    rw [Nat.card_congr (subtractAxis s 96 48 32 (-16) (by decide) (by decide)), Nat.card_congr layer]
    exact card_dot_neg_sixteen s
  exact ⟨congrArg (fun n : ℕ => (n : ℤ)) a, congrArg (fun n : ℕ => (n : ℤ)) b,
    congrArg (fun n : ℕ => (n : ℤ)) c, congrArg (fun n : ℕ => (n : ℤ)) d⟩

private theorem inner_counts96 (s : PlayShortestVectors) :
    layerCount s 96 0 = 9403968600 ∧ layerCount s 96 8 = 7535462400 ∧ layerCount s 96 16 = 3771829800 := by
  obtain ⟨h24, h32, h40, h48⟩ := outer_counts96 s
  obtain ⟨h2, h4⟩ := LeechShellMoments.diff_moments 96
  rw [shell_card96] at h2 h4
  have total := sum_by_layers 96 products96 allowed96 s (fun _ => 1)
  have second := sum_by_layers 96 products96 allowed96 s (fun k => (k / 4) ^ 2)
  have fourth := sum_by_layers 96 products96 allowed96 s (fun k => (k / 4) ^ 4)
  have cancel (d : ℤ) : 4*d/4 = d := by omega
  simp only [cancel] at second fourth
  norm_num [products96, sum_insert, opposite_layer_count, h24, h32, h40, h48, shell_card96] at total second fourth
  omega

/-- Count the vectors of squared length 96 at every integer dot product with any shortest vector. -/
theorem card_norm96_dot_layer (s : PlayShortestVectors) (k : ℤ) :
    Nat.card {v : PlayNorm96Vectors // dot s.val v.val = k} =
      if k = 0 then 9403968600
      else if k = 8 ∨ k = -8 then 7535462400
      else if k = 16 ∨ k = -16 then 3771829800
      else if k = 24 ∨ k = -24 then 1062195200
      else if k = 32 ∨ k = -32 then 133204500
      else if k = 40 ∨ k = -40 then 4147200
      else if k = 48 ∨ k = -48 then 4600
      else 0 := by
  classical
  apply Int.ofNat_inj.mp
  change layerCount s 96 k = _
  by_cases hk : k ∈ products96
  · obtain ⟨h0, h8, h16⟩ := inner_counts96 s
    obtain ⟨h24, h32, h40, h48⟩ := outer_counts96 s
    simp only [products96, mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [opposite_layer_count, h0, h8, h16, h24, h32, h40, h48]
  · have noHits : (univ : Finset (Shell 96)).filter (fun x => 4 * diff x = k) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x _ hx
      exact hk (hx ▸ allowed96 x)
    rw [← reference_layer_card, noHits]
    simp only [products96, mem_insert, mem_singleton, not_or] at hk
    obtain ⟨h0,h8,hn8,h16,hn16,h24,hn24,h32,hn32,h40,hn40,h48,hn48⟩ := hk
    simp [h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48]

end LeechLayers
