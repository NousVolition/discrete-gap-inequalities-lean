import LeechNorm288
import LeechNorm272Layers

/-! # Squared-length-288 layers along a shortest vector

Subtracting from the axis gives the outer layers from smaller shells.
The +96 layer maps to the −64 layer at squared length 128, which has one vector.
The shell total and two coordinate moments give the counts at 0, ±8 and ±16.
-/
namespace LeechLayers

open PlaygroundGolay PlaygroundLeech LeechLattice LeechSymmetry Finset
open LeechShellMoments (Shell diff)

abbrev PlayNorm288Vectors := PlayShell 288

private noncomputable instance : Fintype (Shell 288) := by
  have : Finite (Shell 288) := (Nat.card_pos_iff.mp
    (show 0 < Nat.card (Shell 288) by rw [LeechNorm288.card_norm288_vectors]; decide)).2
  exact Fintype.ofFinite _

private theorem shell_card288 : Fintype.card (Shell 288) = 6096882661243920 :=
  Nat.card_eq_fintype_card.symm.trans LeechNorm288.card_norm288_vectors

private def products288 : Finset ℤ :=
  {0, 8, -8, 16, -16, 24, -24, 32, -32, 40, -40, 48, -48, 56, -56, 64, -64,
    72, -72, 80, -80, 88, -88, 96, -96}

private theorem allowed288 (x : Shell 288) : 4 * diff x ∈ products288 := by
  obtain ⟨lo, hi⟩ := reference_double_dot_bounds (by decide : (288 : ℤ) ≠ 128) x
  obtain ⟨⟨q, hq⟩, _, _⟩ := reference_dot_bounds (by decide : (288 : ℤ) ≠ 32) x
  simp only [products288, mem_insert, mem_singleton]
  omega

private theorem outer_counts288 (s : PlayShortestVectors) :
    layerCount s 288 24 = 488171450607616 ∧
    layerCount s 288 32 = 279245882826900 ∧
    layerCount s 288 40 = 129811503052800 ∧
    layerCount s 288 48 = 46906043912800 ∧
    layerCount s 288 56 = 12194621632512 ∧
    layerCount s 288 64 = 2007834672456 ∧
    layerCount s 288 72 = 163357849600 ∧
    layerCount s 288 80 = 3771829800 ∧
    layerCount s 288 88 = 4147200 ∧
    layerCount s 288 96 = 1 := by
  have transfer {k m j : ℤ} {n : ℕ} (e : PlayLayer s 288 k ≃ PlayLayer s m j)
      (h : Nat.card (PlayLayer s m j) = n) : layerCount s 288 k = (n : ℤ) :=
    congrArg (fun a : ℕ => (a : ℤ)) ((Nat.card_congr e).trans h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply transfer (subtractAxis s 288 24 272 8 (by decide) (by decide))
    simpa using card_norm272_dot_layer s 8
  · apply transfer (subtractAxis s 288 32 256 0 (by decide) (by decide))
    simpa using card_norm256_dot_layer s 0
  · apply transfer (subtractAxis s 288 40 240 (-8) (by decide) (by decide))
    simpa using card_norm240_dot_layer s (-8)
  · apply transfer (subtractAxis s 288 48 224 (-16) (by decide) (by decide))
    simpa using card_norm224_dot_layer s (-16)
  · apply transfer (subtractAxis s 288 56 208 (-24) (by decide) (by decide))
    simpa using card_norm208_dot_layer s (-24)
  · apply transfer (subtractAxis s 288 64 192 (-32) (by decide) (by decide))
    simpa using card_norm192_dot_layer s (-32)
  · apply transfer (subtractAxis s 288 72 176 (-40) (by decide) (by decide))
    simpa using card_norm176_dot_layer s (-40)
  · apply transfer (subtractAxis s 288 80 160 (-48) (by decide) (by decide))
    simpa using card_norm160_dot_layer s (-48)
  · apply transfer (subtractAxis s 288 88 144 (-56) (by decide) (by decide))
    simpa using card_norm144_dot_layer s (-56)
  · apply transfer (subtractAxis s 288 96 128 (-64) (by decide) (by decide))
    simpa using card_norm128_dot_layer s (-64)

private theorem inner_counts288 (s : PlayShortestVectors) :
    layerCount s 288 0 = 961802512637350 ∧
    layerCount s 288 8 = 893508106291200 ∧
    layerCount s 288 16 = 715527497480400 := by
  obtain ⟨h24, h32, h40, h48, h56, h64, h72, h80, h88, h96⟩ := outer_counts288 s
  obtain ⟨h2, h4⟩ := LeechShellMoments.diff_moments 288
  rw [shell_card288] at h2 h4
  have total := sum_by_layers 288 products288 allowed288 s (fun _ => 1)
  have second := sum_by_layers 288 products288 allowed288 s (fun k => (k / 4) ^ 2)
  have fourth := sum_by_layers 288 products288 allowed288 s (fun k => (k / 4) ^ 4)
  have cancel (d : ℤ) : 4 * d / 4 = d := by omega
  simp only [cancel] at second fourth
  norm_num [products288, sum_insert, opposite_layer_count, h24, h32, h40, h48, h56, h64,
    h72, h80, h88, h96, shell_card288] at total second fourth
  omega

/-- For any shortest axis, count the vectors of squared length 288 at each integer dot product. -/
theorem card_norm288_dot_layer (s : PlayShortestVectors) (k : ℤ) :
    Nat.card {v : PlayNorm288Vectors // dot s.val v.val = k} =
      if k = 0 then 961802512637350
      else if k = 8 ∨ k = -8 then 893508106291200
      else if k = 16 ∨ k = -16 then 715527497480400
      else if k = 24 ∨ k = -24 then 488171450607616
      else if k = 32 ∨ k = -32 then 279245882826900
      else if k = 40 ∨ k = -40 then 129811503052800
      else if k = 48 ∨ k = -48 then 46906043912800
      else if k = 56 ∨ k = -56 then 12194621632512
      else if k = 64 ∨ k = -64 then 2007834672456
      else if k = 72 ∨ k = -72 then 163357849600
      else if k = 80 ∨ k = -80 then 3771829800
      else if k = 88 ∨ k = -88 then 4147200
      else if k = 96 ∨ k = -96 then 1
      else 0 := by
  classical
  apply Int.ofNat_inj.mp
  change layerCount s 288 k = _
  by_cases hk : k ∈ products288
  · obtain ⟨h0, h8, h16⟩ := inner_counts288 s
    obtain ⟨h24, h32, h40, h48, h56, h64, h72, h80, h88, h96⟩ := outer_counts288 s
    simp only [products288, mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;>
      norm_num [opposite_layer_count, h0, h8, h16, h24, h32, h40, h48, h56, h64,
        h72, h80, h88, h96]
  · have emptyLayer : (univ : Finset (Shell 288)).filter (fun x => 4 * diff x = k) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x _ hx
      exact hk (hx ▸ allowed288 x)
    rw [← reference_layer_card, emptyLayer]
    simp only [products288, mem_insert, mem_singleton, not_or] at hk
    obtain ⟨h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48, h56, hn56,
      h64, hn64, h72, hn72, h80, hn80, h88, hn88, h96, hn96⟩ := hk
    simp [h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48, h56, hn56,
      h64, hn64, h72, hn72, h80, hn80, h88, hn88, h96, hn96]

end LeechLayers
