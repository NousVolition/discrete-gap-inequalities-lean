import LeechNorm320
import LeechNorm304Layers

/-! # Squared-length-320 layers along a shortest vector

Subtracting from the axis gives the outer layers from smaller shells.
At +96 the target is the −64 layer at squared length 160. At +104 the target is empty.
The shell total and two coordinate moments give the counts at 0, ±8 and ±16.
-/
namespace LeechLayers

open PlaygroundGolay PlaygroundLeech LeechLattice LeechSymmetry Finset
open LeechShellMoments (Shell diff)

abbrev PlayNorm320Vectors := PlayShell 320

private noncomputable instance : Fintype (Shell 320) := by
  have : Finite (Shell 320) := (Nat.card_pos_iff.mp
    (show 0 < Nat.card (Shell 320) by rw [LeechNorm320.card_norm320_vectors]; decide)).2
  exact Fintype.ofFinite _

private theorem shell_card320 : Fintype.card (Shell 320) = 19428439855275360 :=
  Nat.card_eq_fintype_card.symm.trans LeechNorm320.card_norm320_vectors

private def products320 : Finset ℤ :=
  {0, 8, -8, 16, -16, 24, -24, 32, -32, 40, -40, 48, -48, 56, -56, 64, -64,
    72, -72, 80, -80, 88, -88, 96, -96, 104, -104}

private theorem allowed320 (x : Shell 320) : 4 * diff x ∈ products320 := by
  obtain ⟨lo, hi⟩ := reference_double_dot_bounds (by decide : (320 : ℤ) ≠ 128) x
  obtain ⟨⟨q, hq⟩, _, _⟩ := reference_dot_bounds (by decide : (320 : ℤ) ≠ 32) x
  simp only [products320, mem_insert, mem_singleton]
  omega

private theorem outer_counts320 (s : PlayShortestVectors) :
    layerCount s 320 24 = 1582425260697600 ∧
    layerCount s 320 32 = 961802512637350 ∧
    layerCount s 320 40 = 488171450607616 ∧
    layerCount s 320 48 = 200080685520000 ∧
    layerCount s 320 56 = 62511367475200 ∧
    layerCount s 320 64 = 13618454702600 ∧
    layerCount s 320 72 = 1758528921600 ∧
    layerCount s 320 80 = 97917423808 ∧
    layerCount s 320 88 = 1062195200 ∧
    layerCount s 320 96 = 93150 ∧
    layerCount s 320 104 = 0 := by
  have transfer {k m j : ℤ} {n : ℕ} (e : PlayLayer s 320 k ≃ PlayLayer s m j)
      (h : Nat.card (PlayLayer s m j) = n) : layerCount s 320 k = (n : ℤ) :=
    congrArg (fun a : ℕ => (a : ℤ)) ((Nat.card_congr e).trans h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply transfer (subtractAxis s 320 24 304 8 (by decide) (by decide))
    simpa using card_norm304_dot_layer s 8
  · apply transfer (subtractAxis s 320 32 288 0 (by decide) (by decide))
    simpa using card_norm288_dot_layer s 0
  · apply transfer (subtractAxis s 320 40 272 (-8) (by decide) (by decide))
    simpa using card_norm272_dot_layer s (-8)
  · apply transfer (subtractAxis s 320 48 256 (-16) (by decide) (by decide))
    simpa using card_norm256_dot_layer s (-16)
  · apply transfer (subtractAxis s 320 56 240 (-24) (by decide) (by decide))
    simpa using card_norm240_dot_layer s (-24)
  · apply transfer (subtractAxis s 320 64 224 (-32) (by decide) (by decide))
    simpa using card_norm224_dot_layer s (-32)
  · apply transfer (subtractAxis s 320 72 208 (-40) (by decide) (by decide))
    simpa using card_norm208_dot_layer s (-40)
  · apply transfer (subtractAxis s 320 80 192 (-48) (by decide) (by decide))
    simpa using card_norm192_dot_layer s (-48)
  · apply transfer (subtractAxis s 320 88 176 (-56) (by decide) (by decide))
    simpa using card_norm176_dot_layer s (-56)
  · apply transfer (subtractAxis s 320 96 160 (-64) (by decide) (by decide))
    simpa using card_norm160_dot_layer s (-64)
  · apply transfer (subtractAxis s 320 104 144 (-72) (by decide) (by decide))
    simpa using card_norm144_dot_layer s (-72)

private theorem inner_counts320 (s : PlayShortestVectors) :
    layerCount s 320 0 = 2907616511773512 ∧
    layerCount s 320 8 = 2721056421785600 ∧
    layerCount s 320 16 = 2228888009691200 := by
  obtain ⟨h24, h32, h40, h48, h56, h64, h72, h80, h88, h96, h104⟩ := outer_counts320 s
  obtain ⟨h2, h4⟩ := LeechShellMoments.diff_moments 320
  rw [shell_card320] at h2 h4
  have total := sum_by_layers 320 products320 allowed320 s (fun _ => 1)
  have second := sum_by_layers 320 products320 allowed320 s (fun k => (k / 4) ^ 2)
  have fourth := sum_by_layers 320 products320 allowed320 s (fun k => (k / 4) ^ 4)
  have cancel (d : ℤ) : 4 * d / 4 = d := by omega
  simp only [cancel] at second fourth
  norm_num [products320, sum_insert, opposite_layer_count, h24, h32, h40, h48, h56, h64,
    h72, h80, h88, h96, h104, shell_card320] at total second fourth
  omega

/-- For any shortest axis, count the vectors of squared length 320 at each integer dot product. -/
theorem card_norm320_dot_layer (s : PlayShortestVectors) (k : ℤ) :
    Nat.card {v : PlayNorm320Vectors // dot s.val v.val = k} =
      if k = 0 then 2907616511773512
      else if k = 8 ∨ k = -8 then 2721056421785600
      else if k = 16 ∨ k = -16 then 2228888009691200
      else if k = 24 ∨ k = -24 then 1582425260697600
      else if k = 32 ∨ k = -32 then 961802512637350
      else if k = 40 ∨ k = -40 then 488171450607616
      else if k = 48 ∨ k = -48 then 200080685520000
      else if k = 56 ∨ k = -56 then 62511367475200
      else if k = 64 ∨ k = -64 then 13618454702600
      else if k = 72 ∨ k = -72 then 1758528921600
      else if k = 80 ∨ k = -80 then 97917423808
      else if k = 88 ∨ k = -88 then 1062195200
      else if k = 96 ∨ k = -96 then 93150
      else 0 := by
  classical
  apply Int.ofNat_inj.mp
  change layerCount s 320 k = _
  by_cases hk : k ∈ products320
  · obtain ⟨h0, h8, h16⟩ := inner_counts320 s
    obtain ⟨h24, h32, h40, h48, h56, h64, h72, h80, h88, h96, h104⟩ := outer_counts320 s
    simp only [products320, mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;>
      norm_num [opposite_layer_count, h0, h8, h16, h24, h32, h40, h48, h56, h64,
        h72, h80, h88, h96, h104]
  · have emptyLayer : (univ : Finset (Shell 320)).filter (fun x => 4 * diff x = k) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x _ hx
      exact hk (hx ▸ allowed320 x)
    rw [← reference_layer_card, emptyLayer]
    simp only [products320, mem_insert, mem_singleton, not_or] at hk
    obtain ⟨h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48, h56, hn56,
      h64, hn64, h72, hn72, h80, hn80, h88, hn88, h96, hn96, _, _⟩ := hk
    simp [h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48, h56, hn56,
      h64, hn64, h72, hn72, h80, hn80, h88, hn88, h96, hn96]

end LeechLayers
