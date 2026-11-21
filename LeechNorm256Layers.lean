import LeechNorm256
import LeechNorm240Layers

/-! # Squared-length-256 layers along a shortest vector

Subtracting a vector from the axis gives the outer layers from smaller shells.
At dot product 88 this lands in the empty −56 layer at squared length 112.
The shell total and two coordinate moments give the counts at 0, 8 and 16.
-/
namespace LeechLayers

open PlaygroundGolay PlaygroundLeech LeechLattice LeechSymmetry Finset
open LeechShellMoments (Shell diff)

abbrev PlayNorm256Vectors := PlayShell 256

private noncomputable instance : Fintype (Shell 256) := by
  have : Finite (Shell 256) := (Nat.card_pos_iff.mp
    (show 0 < Nat.card (Shell 256) by rw [LeechNorm256.card_norm256_vectors]; decide)).2
  exact Fintype.ofFinite _

private theorem shell_card256 : Fintype.card (Shell 256) = 1668890090322000 :=
  Nat.card_eq_fintype_card.symm.trans LeechNorm256.card_norm256_vectors

private def products256 : Finset ℤ :=
  {0, 8, -8, 16, -16, 24, -24, 32, -32, 40, -40, 48, -48, 56, -56, 64, -64,
    72, -72, 80, -80, 88, -88}

private theorem allowed256 (x : Shell 256) : 4 * diff x ∈ products256 := by
  obtain ⟨lo, hi⟩ := reference_double_dot_bounds (by decide : (256 : ℤ) ≠ 128) x
  obtain ⟨⟨q, hq⟩, _, _⟩ := reference_dot_bounds (by decide : (256 : ℤ) ≠ 32) x
  simp only [products256, mem_insert, mem_singleton]
  omega

private theorem outer_counts256 (s : PlayShortestVectors) :
    layerCount s 256 24 = 129811503052800 ∧
    layerCount s 256 32 = 68717357121600 ∧
    layerCount s 256 40 = 28500740352000 ∧
    layerCount s 256 48 = 8710737537600 ∧
    layerCount s 256 56 = 1758528921600 ∧
    layerCount s 256 64 = 192825064350 ∧
    layerCount s 256 72 = 7535462400 ∧
    layerCount s 256 80 = 32788800 ∧
    layerCount s 256 88 = 0 := by
  have transfer {k m j : ℤ} {n : ℕ} (e : PlayLayer s 256 k ≃ PlayLayer s m j)
      (h : Nat.card (PlayLayer s m j) = n) : layerCount s 256 k = (n : ℤ) :=
    congrArg (fun a : ℕ => (a : ℤ)) ((Nat.card_congr e).trans h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply transfer (subtractAxis s 256 24 240 8 (by decide) (by decide))
    simpa using card_norm240_dot_layer s 8
  · apply transfer (subtractAxis s 256 32 224 0 (by decide) (by decide))
    simpa using card_norm224_dot_layer s 0
  · apply transfer (subtractAxis s 256 40 208 (-8) (by decide) (by decide))
    simpa using card_norm208_dot_layer s (-8)
  · apply transfer (subtractAxis s 256 48 192 (-16) (by decide) (by decide))
    simpa using card_norm192_dot_layer s (-16)
  · apply transfer (subtractAxis s 256 56 176 (-24) (by decide) (by decide))
    simpa using card_norm176_dot_layer s (-24)
  · apply transfer (subtractAxis s 256 64 160 (-32) (by decide) (by decide))
    simpa using card_norm160_dot_layer s (-32)
  · apply transfer (subtractAxis s 256 72 144 (-40) (by decide) (by decide))
    simpa using card_norm144_dot_layer s (-40)
  · apply transfer (subtractAxis s 256 80 128 (-48) (by decide) (by decide))
    simpa using card_norm128_dot_layer s (-48)
  · apply transfer (subtractAxis s 256 88 112 (-56) (by decide) (by decide))
    simpa using card_norm112_dot_layer s (-56)

private theorem inner_counts256 (s : PlayShortestVectors) :
    layerCount s 256 0 = 279245882826900 ∧
    layerCount s 256 8 = 257042157926400 ∧
    layerCount s 256 16 = 200080685520000 := by
  obtain ⟨h24, h32, h40, h48, h56, h64, h72, h80, h88⟩ := outer_counts256 s
  obtain ⟨h2, h4⟩ := LeechShellMoments.diff_moments 256
  rw [shell_card256] at h2 h4
  have total := sum_by_layers 256 products256 allowed256 s (fun _ => 1)
  have second := sum_by_layers 256 products256 allowed256 s (fun k => (k / 4) ^ 2)
  have fourth := sum_by_layers 256 products256 allowed256 s (fun k => (k / 4) ^ 4)
  have cancel (d : ℤ) : 4 * d / 4 = d := by omega
  simp only [cancel] at second fourth
  norm_num [products256, sum_insert, opposite_layer_count, h24, h32, h40, h48, h56, h64,
    h72, h80, h88, shell_card256] at total second fourth
  omega

/-- For any shortest axis, count the vectors of squared length 256 at each integer dot product. -/
theorem card_norm256_dot_layer (s : PlayShortestVectors) (k : ℤ) :
    Nat.card {v : PlayNorm256Vectors // dot s.val v.val = k} =
      if k = 0 then 279245882826900
      else if k = 8 ∨ k = -8 then 257042157926400
      else if k = 16 ∨ k = -16 then 200080685520000
      else if k = 24 ∨ k = -24 then 129811503052800
      else if k = 32 ∨ k = -32 then 68717357121600
      else if k = 40 ∨ k = -40 then 28500740352000
      else if k = 48 ∨ k = -48 then 8710737537600
      else if k = 56 ∨ k = -56 then 1758528921600
      else if k = 64 ∨ k = -64 then 192825064350
      else if k = 72 ∨ k = -72 then 7535462400
      else if k = 80 ∨ k = -80 then 32788800
      else 0 := by
  classical
  apply Int.ofNat_inj.mp
  change layerCount s 256 k = _
  by_cases hk : k ∈ products256
  · obtain ⟨h0, h8, h16⟩ := inner_counts256 s
    obtain ⟨h24, h32, h40, h48, h56, h64, h72, h80, h88⟩ := outer_counts256 s
    simp only [products256, mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [opposite_layer_count, h0, h8, h16, h24, h32, h40, h48, h56, h64, h72, h80, h88]
  · have emptyLayer : (univ : Finset (Shell 256)).filter (fun x => 4 * diff x = k) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x _ hx
      exact hk (hx ▸ allowed256 x)
    rw [← reference_layer_card, emptyLayer]
    simp only [products256, mem_insert, mem_singleton, not_or] at hk
    obtain ⟨h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48,
      h56, hn56, h64, hn64, h72, hn72, h80, hn80, _, _⟩ := hk
    simp [h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48,
      h56, hn56, h64, hn64, h72, hn72, h80, hn80]

end LeechLayers
