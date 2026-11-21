import LeechNorm208
import LeechNorm192Layers

/-! # Squared-length-208 layers along a shortest vector

The map from v to s − v gives seven positive layers from smaller shells.
The shell total and two coordinate moments give the layers at 0, 8 and 16.
Negating v exchanges the two signs.
-/
namespace LeechLayers

open PlaygroundGolay PlaygroundLeech LeechLattice LeechSymmetry Finset
open LeechShellMoments (Shell diff)

abbrev PlayNorm208Vectors := PlayShell 208

private noncomputable instance : Fintype (Shell 208) := by
  have : Finite (Shell 208) := (Nat.card_pos_iff.mp
    (show 0 < Nat.card (Shell 208) by rw [LeechNorm208.card_norm208_vectors]; decide)).2
  exact Fintype.ofFinite _

private theorem shell_card208 : Fintype.card (Shell 208) = 169931095326720 :=
  Nat.card_eq_fintype_card.symm.trans LeechNorm208.card_norm208_vectors

private def products208 : Finset ℤ :=
  {0, 8, -8, 16, -16, 24, -24, 32, -32, 40, -40, 48, -48, 56, -56, 64, -64, 72, -72}

private theorem allowed208 (x : Shell 208) : 4 * diff x ∈ products208 := by
  obtain ⟨lo, hi⟩ := reference_double_dot_bounds (by decide : (208 : ℤ) ≠ 128) x
  obtain ⟨⟨q, hq⟩, _, _⟩ := reference_dot_bounds (by decide : (208 : ℤ) ≠ 32) x
  simp only [products208, mem_insert, mem_singleton]
  omega

private theorem outer_counts208 (s : PlayShortestVectors) :
    layerCount s 208 24 = 12194621632512 ∧
    layerCount s 208 32 = 5456580940800 ∧
    layerCount s 208 40 = 1758528921600 ∧
    layerCount s 208 48 = 364086835200 ∧
    layerCount s 208 56 = 39253082112 ∧
    layerCount s 208 64 = 1384998912 ∧
    layerCount s 208 72 = 4147200 := by
  have transfer {k m j : ℤ} {n : ℕ} (e : PlayLayer s 208 k ≃ PlayLayer s m j)
      (h : Nat.card (PlayLayer s m j) = n) : layerCount s 208 k = (n : ℤ) :=
    congrArg (fun a : ℕ => (a : ℤ)) ((Nat.card_congr e).trans h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply transfer (subtractAxis s 208 24 192 8 (by decide) (by decide))
    simpa using card_norm192_dot_layer s 8
  · apply transfer (subtractAxis s 208 32 176 0 (by decide) (by decide))
    simpa using card_norm176_dot_layer s 0
  · apply transfer (subtractAxis s 208 40 160 (-8) (by decide) (by decide))
    simpa using card_norm160_dot_layer s (-8)
  · apply transfer (subtractAxis s 208 48 144 (-16) (by decide) (by decide))
    simpa using card_norm144_dot_layer s (-16)
  · apply transfer (subtractAxis s 208 56 128 (-24) (by decide) (by decide))
    simpa using card_norm128_dot_layer s (-24)
  · apply transfer (subtractAxis s 208 64 112 (-32) (by decide) (by decide))
    simpa using card_norm112_dot_layer s (-32)
  · apply transfer (subtractAxis s 208 72 96 (-40) (by decide) (by decide))
    simpa using card_norm96_dot_layer s (-40)

private theorem inner_counts208 (s : PlayShortestVectors) :
    layerCount s 208 0 = 31528851609600 ∧
    layerCount s 208 8 = 28500740352000 ∧
    layerCount s 208 16 = 20885920948224 := by
  obtain ⟨h24, h32, h40, h48, h56, h64, h72⟩ := outer_counts208 s
  obtain ⟨h2, h4⟩ := LeechShellMoments.diff_moments 208
  rw [shell_card208] at h2 h4
  have total := sum_by_layers 208 products208 allowed208 s (fun _ => 1)
  have second := sum_by_layers 208 products208 allowed208 s (fun k => (k / 4) ^ 2)
  have fourth := sum_by_layers 208 products208 allowed208 s (fun k => (k / 4) ^ 4)
  have cancel (d : ℤ) : 4 * d / 4 = d := by omega
  simp only [cancel] at second fourth
  norm_num [products208, sum_insert, opposite_layer_count, h24, h32, h40, h48, h56, h64,
    h72, shell_card208] at total second fourth
  omega

/-- For any shortest axis, count the vectors of squared length 208 at each integer dot product. -/
theorem card_norm208_dot_layer (s : PlayShortestVectors) (k : ℤ) :
    Nat.card {v : PlayNorm208Vectors // dot s.val v.val = k} =
      if k = 0 then 31528851609600
      else if k = 8 ∨ k = -8 then 28500740352000
      else if k = 16 ∨ k = -16 then 20885920948224
      else if k = 24 ∨ k = -24 then 12194621632512
      else if k = 32 ∨ k = -32 then 5456580940800
      else if k = 40 ∨ k = -40 then 1758528921600
      else if k = 48 ∨ k = -48 then 364086835200
      else if k = 56 ∨ k = -56 then 39253082112
      else if k = 64 ∨ k = -64 then 1384998912
      else if k = 72 ∨ k = -72 then 4147200
      else 0 := by
  classical
  apply Int.ofNat_inj.mp
  change layerCount s 208 k = _
  by_cases hk : k ∈ products208
  · obtain ⟨h0, h8, h16⟩ := inner_counts208 s
    obtain ⟨h24, h32, h40, h48, h56, h64, h72⟩ := outer_counts208 s
    simp only [products208, mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [opposite_layer_count, h0, h8, h16, h24, h32, h40, h48, h56, h64, h72]
  · have emptyLayer : (univ : Finset (Shell 208)).filter (fun x => 4 * diff x = k) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x _ hx
      exact hk (hx ▸ allowed208 x)
    rw [← reference_layer_card, emptyLayer]
    simp only [products208, mem_insert, mem_singleton, not_or] at hk
    obtain ⟨h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48,
      h56, hn56, h64, hn64, h72, hn72⟩ := hk
    simp [h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48,
      h56, hn56, h64, hn64, h72, hn72]

end LeechLayers
