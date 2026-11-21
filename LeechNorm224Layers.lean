import LeechNorm224
import LeechNorm208Layers

/-! # Squared-length-224 layers along a shortest vector

The map from v to s − v gives eight positive layers from smaller shells.
The total and two coordinate moments give the layers at 0, 8 and 16.
Negating v exchanges the two signs.
-/
namespace LeechLayers

open PlaygroundGolay PlaygroundLeech LeechLattice LeechSymmetry Finset
open LeechShellMoments (Shell diff)

abbrev PlayNorm224Vectors := PlayShell 224

private noncomputable instance : Fintype (Shell 224) := by
  have : Finite (Shell 224) := (Nat.card_pos_iff.mp
    (show 0 < Nat.card (Shell 224) by rw [LeechNorm224.card_norm224_vectors]; decide)).2
  exact Fintype.ofFinite _

private theorem shell_card224 : Fintype.card (Shell 224) = 384163586352000 :=
  Nat.card_eq_fintype_card.symm.trans LeechNorm224.card_norm224_vectors

private def products224 : Finset ℤ :=
  {0, 8, -8, 16, -16, 24, -24, 32, -32, 40, -40, 48, -48, 56, -56, 64, -64, 72, -72, 80, -80}

private theorem allowed224 (x : Shell 224) : 4 * diff x ∈ products224 := by
  obtain ⟨lo, hi⟩ := reference_double_dot_bounds (by decide : (224 : ℤ) ≠ 128) x
  obtain ⟨⟨q, hq⟩, _, _⟩ := reference_dot_bounds (by decide : (224 : ℤ) ≠ 32) x
  simp only [products224, mem_insert, mem_singleton]
  omega

private theorem outer_counts224 (s : PlayShortestVectors) :
    layerCount s 224 24 = 28500740352000 ∧
    layerCount s 224 32 = 13618454702600 ∧
    layerCount s 224 40 = 4841939097600 ∧
    layerCount s 224 48 = 1171711866600 ∧
    layerCount s 224 56 = 163357849600 ∧
    layerCount s 224 64 = 9403968600 ∧
    layerCount s 224 72 = 95385600 ∧
    layerCount s 224 80 = 4600 := by
  have transfer {k m j : ℤ} {n : ℕ} (e : PlayLayer s 224 k ≃ PlayLayer s m j)
      (h : Nat.card (PlayLayer s m j) = n) : layerCount s 224 k = (n : ℤ) :=
    congrArg (fun a : ℕ => (a : ℤ)) ((Nat.card_congr e).trans h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply transfer (subtractAxis s 224 24 208 8 (by decide) (by decide))
    simpa using card_norm208_dot_layer s 8
  · apply transfer (subtractAxis s 224 32 192 0 (by decide) (by decide))
    simpa using card_norm192_dot_layer s 0
  · apply transfer (subtractAxis s 224 40 176 (-8) (by decide) (by decide))
    simpa using card_norm176_dot_layer s (-8)
  · apply transfer (subtractAxis s 224 48 160 (-16) (by decide) (by decide))
    simpa using card_norm160_dot_layer s (-16)
  · apply transfer (subtractAxis s 224 56 144 (-24) (by decide) (by decide))
    simpa using card_norm144_dot_layer s (-24)
  · apply transfer (subtractAxis s 224 64 128 (-32) (by decide) (by decide))
    simpa using card_norm128_dot_layer s (-32)
  · apply transfer (subtractAxis s 224 72 112 (-40) (by decide) (by decide))
    simpa using card_norm112_dot_layer s (-40)
  · apply transfer (subtractAxis s 224 80 96 (-48) (by decide) (by decide))
    simpa using card_norm96_dot_layer s (-48)

private theorem inner_counts224 (s : PlayShortestVectors) :
    layerCount s 224 0 = 68717357121600 ∧
    layerCount s 224 8 = 62511367475200 ∧
    layerCount s 224 16 = 46906043912800 := by
  obtain ⟨h24, h32, h40, h48, h56, h64, h72, h80⟩ := outer_counts224 s
  obtain ⟨h2, h4⟩ := LeechShellMoments.diff_moments 224
  rw [shell_card224] at h2 h4
  have total := sum_by_layers 224 products224 allowed224 s (fun _ => 1)
  have second := sum_by_layers 224 products224 allowed224 s (fun k => (k / 4) ^ 2)
  have fourth := sum_by_layers 224 products224 allowed224 s (fun k => (k / 4) ^ 4)
  have cancel (d : ℤ) : 4 * d / 4 = d := by omega
  simp only [cancel] at second fourth
  norm_num [products224, sum_insert, opposite_layer_count, h24, h32, h40, h48, h56, h64,
    h72, h80, shell_card224] at total second fourth
  omega

/-- For any shortest axis, count the vectors of squared length 224 at each integer dot product. -/
theorem card_norm224_dot_layer (s : PlayShortestVectors) (k : ℤ) :
    Nat.card {v : PlayNorm224Vectors // dot s.val v.val = k} =
      if k = 0 then 68717357121600
      else if k = 8 ∨ k = -8 then 62511367475200
      else if k = 16 ∨ k = -16 then 46906043912800
      else if k = 24 ∨ k = -24 then 28500740352000
      else if k = 32 ∨ k = -32 then 13618454702600
      else if k = 40 ∨ k = -40 then 4841939097600
      else if k = 48 ∨ k = -48 then 1171711866600
      else if k = 56 ∨ k = -56 then 163357849600
      else if k = 64 ∨ k = -64 then 9403968600
      else if k = 72 ∨ k = -72 then 95385600
      else if k = 80 ∨ k = -80 then 4600
      else 0 := by
  classical
  apply Int.ofNat_inj.mp
  change layerCount s 224 k = _
  by_cases hk : k ∈ products224
  · obtain ⟨h0, h8, h16⟩ := inner_counts224 s
    obtain ⟨h24, h32, h40, h48, h56, h64, h72, h80⟩ := outer_counts224 s
    simp only [products224, mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [opposite_layer_count, h0, h8, h16, h24, h32, h40, h48, h56, h64, h72, h80]
  · have emptyLayer : (univ : Finset (Shell 224)).filter (fun x => 4 * diff x = k) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x _ hx
      exact hk (hx ▸ allowed224 x)
    rw [← reference_layer_card, emptyLayer]
    simp only [products224, mem_insert, mem_singleton, not_or] at hk
    obtain ⟨h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48,
      h56, hn56, h64, hn64, h72, hn72, h80, hn80⟩ := hk
    simp [h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48,
      h56, hn56, h64, hn64, h72, hn72, h80, hn80]

end LeechLayers
