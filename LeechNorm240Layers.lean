import LeechNorm240
import LeechNorm224Layers

/-! # Squared-length-240 layers along a shortest vector

The map from v to s − v gives eight positive layers from smaller shells.
The total and two coordinate moments give the layers at 0, 8 and 16.
Negating v exchanges the two signs.
-/
namespace LeechLayers

open PlaygroundGolay PlaygroundLeech LeechLattice LeechSymmetry Finset
open LeechShellMoments (Shell diff)

abbrev PlayNorm240Vectors := PlayShell 240

private noncomputable instance : Fintype (Shell 240) := by
  have : Finite (Shell 240) := (Nat.card_pos_iff.mp
    (show 0 < Nat.card (Shell 240) by rw [LeechNorm240.card_norm240_vectors]; decide)).2
  exact Fintype.ofFinite _

private theorem shell_card240 : Fintype.card (Shell 240) = 820166620815360 :=
  Nat.card_eq_fintype_card.symm.trans LeechNorm240.card_norm240_vectors

private def products240 : Finset ℤ :=
  {0, 8, -8, 16, -16, 24, -24, 32, -32, 40, -40, 48, -48, 56, -56, 64, -64, 72, -72, 80, -80}

private theorem allowed240 (x : Shell 240) : 4 * diff x ∈ products240 := by
  obtain ⟨lo, hi⟩ := reference_double_dot_bounds (by decide : (240 : ℤ) ≠ 128) x
  obtain ⟨⟨q, hq⟩, _, _⟩ := reference_dot_bounds (by decide : (240 : ℤ) ≠ 32) x
  simp only [products240, mem_insert, mem_singleton]
  omega

private theorem outer_counts240 (s : PlayShortestVectors) :
    layerCount s 240 24 = 62511367475200 ∧
    layerCount s 240 32 = 31528851609600 ∧
    layerCount s 240 40 = 12194621632512 ∧
    layerCount s 240 48 = 3348006886400 ∧
    layerCount s 240 56 = 573172070400 ∧
    layerCount s 240 64 = 47406643200 ∧
    layerCount s 240 72 = 1062195200 ∧
    layerCount s 240 80 = 953856 := by
  have transfer {k m j : ℤ} {n : ℕ} (e : PlayLayer s 240 k ≃ PlayLayer s m j)
      (h : Nat.card (PlayLayer s m j) = n) : layerCount s 240 k = (n : ℤ) :=
    congrArg (fun a : ℕ => (a : ℤ)) ((Nat.card_congr e).trans h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply transfer (subtractAxis s 240 24 224 8 (by decide) (by decide))
    simpa using card_norm224_dot_layer s 8
  · apply transfer (subtractAxis s 240 32 208 0 (by decide) (by decide))
    simpa using card_norm208_dot_layer s 0
  · apply transfer (subtractAxis s 240 40 192 (-8) (by decide) (by decide))
    simpa using card_norm192_dot_layer s (-8)
  · apply transfer (subtractAxis s 240 48 176 (-16) (by decide) (by decide))
    simpa using card_norm176_dot_layer s (-16)
  · apply transfer (subtractAxis s 240 56 160 (-24) (by decide) (by decide))
    simpa using card_norm160_dot_layer s (-24)
  · apply transfer (subtractAxis s 240 64 144 (-32) (by decide) (by decide))
    simpa using card_norm144_dot_layer s (-32)
  · apply transfer (subtractAxis s 240 72 128 (-40) (by decide) (by decide))
    simpa using card_norm128_dot_layer s (-40)
  · apply transfer (subtractAxis s 240 80 112 (-48) (by decide) (by decide))
    simpa using card_norm112_dot_layer s (-48)

private theorem inner_counts240 (s : PlayShortestVectors) :
    layerCount s 240 0 = 141663767066624 ∧
    layerCount s 240 8 = 129811503052800 ∧
    layerCount s 240 16 = 99235434355200 := by
  obtain ⟨h24, h32, h40, h48, h56, h64, h72, h80⟩ := outer_counts240 s
  obtain ⟨h2, h4⟩ := LeechShellMoments.diff_moments 240
  rw [shell_card240] at h2 h4
  have total := sum_by_layers 240 products240 allowed240 s (fun _ => 1)
  have second := sum_by_layers 240 products240 allowed240 s (fun k => (k / 4) ^ 2)
  have fourth := sum_by_layers 240 products240 allowed240 s (fun k => (k / 4) ^ 4)
  have cancel (d : ℤ) : 4 * d / 4 = d := by omega
  simp only [cancel] at second fourth
  norm_num [products240, sum_insert, opposite_layer_count, h24, h32, h40, h48, h56, h64,
    h72, h80, shell_card240] at total second fourth
  omega

/-- For any shortest axis, count the vectors of squared length 240 at each integer dot product. -/
theorem card_norm240_dot_layer (s : PlayShortestVectors) (k : ℤ) :
    Nat.card {v : PlayNorm240Vectors // dot s.val v.val = k} =
      if k = 0 then 141663767066624
      else if k = 8 ∨ k = -8 then 129811503052800
      else if k = 16 ∨ k = -16 then 99235434355200
      else if k = 24 ∨ k = -24 then 62511367475200
      else if k = 32 ∨ k = -32 then 31528851609600
      else if k = 40 ∨ k = -40 then 12194621632512
      else if k = 48 ∨ k = -48 then 3348006886400
      else if k = 56 ∨ k = -56 then 573172070400
      else if k = 64 ∨ k = -64 then 47406643200
      else if k = 72 ∨ k = -72 then 1062195200
      else if k = 80 ∨ k = -80 then 953856
      else 0 := by
  classical
  apply Int.ofNat_inj.mp
  change layerCount s 240 k = _
  by_cases hk : k ∈ products240
  · obtain ⟨h0, h8, h16⟩ := inner_counts240 s
    obtain ⟨h24, h32, h40, h48, h56, h64, h72, h80⟩ := outer_counts240 s
    simp only [products240, mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [opposite_layer_count, h0, h8, h16, h24, h32, h40, h48, h56, h64, h72, h80]
  · have emptyLayer : (univ : Finset (Shell 240)).filter (fun x => 4 * diff x = k) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x _ hx
      exact hk (hx ▸ allowed240 x)
    rw [← reference_layer_card, emptyLayer]
    simp only [products240, mem_insert, mem_singleton, not_or] at hk
    obtain ⟨h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48,
      h56, hn56, h64, hn64, h72, hn72, h80, hn80⟩ := hk
    simp [h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48,
      h56, hn56, h64, hn64, h72, hn72, h80, hn80]

end LeechLayers
