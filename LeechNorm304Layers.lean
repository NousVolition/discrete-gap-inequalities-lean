import LeechNorm304
import LeechNorm288Layers

/-! # Squared-length-304 layers along a shortest vector

Subtracting from the axis gives the outer layers from smaller shells.
At +96 the target is the empty −64 layer at squared length 144.
The shell total and two coordinate moments give the counts at 0, ±8 and ±16.
-/
namespace LeechLayers

open PlaygroundGolay PlaygroundLeech LeechLattice LeechSymmetry Finset
open LeechShellMoments (Shell diff)

abbrev PlayNorm304Vectors := PlayShell 304

private noncomputable instance : Fintype (Shell 304) := by
  have : Finite (Shell 304) := (Nat.card_pos_iff.mp
    (show 0 < Nat.card (Shell 304) by rw [LeechNorm304.card_norm304_vectors]; decide)).2
  exact Fintype.ofFinite _

private theorem shell_card304 : Fintype.card (Shell 304) = 11045500816896000 :=
  Nat.card_eq_fintype_card.symm.trans LeechNorm304.card_norm304_vectors

private def products304 : Finset ℤ :=
  {0, 8, -8, 16, -16, 24, -24, 32, -32, 40, -40, 48, -48, 56, -56, 64, -64,
    72, -72, 80, -80, 88, -88, 96, -96}

private theorem allowed304 (x : Shell 304) : 4 * diff x ∈ products304 := by
  obtain ⟨lo, hi⟩ := reference_double_dot_bounds (by decide : (304 : ℤ) ≠ 128) x
  obtain ⟨⟨q, hq⟩, _, _⟩ := reference_dot_bounds (by decide : (304 : ℤ) ≠ 32) x
  simp only [products304, mem_insert, mem_singleton]
  omega

private theorem outer_counts304 (s : PlayShortestVectors) :
    layerCount s 304 24 = 893508106291200 ∧
    layerCount s 304 32 = 527244094771200 ∧
    layerCount s 304 40 = 257042157926400 ∧
    layerCount s 304 48 = 99235434355200 ∧
    layerCount s 304 56 = 28500740352000 ∧
    layerCount s 304 64 = 5456580940800 ∧
    layerCount s 304 72 = 573172070400 ∧
    layerCount s 304 80 = 21771763200 ∧
    layerCount s 304 88 = 95385600 ∧
    layerCount s 304 96 = 0 := by
  have transfer {k m j : ℤ} {n : ℕ} (e : PlayLayer s 304 k ≃ PlayLayer s m j)
      (h : Nat.card (PlayLayer s m j) = n) : layerCount s 304 k = (n : ℤ) :=
    congrArg (fun a : ℕ => (a : ℤ)) ((Nat.card_congr e).trans h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply transfer (subtractAxis s 304 24 288 8 (by decide) (by decide))
    simpa using card_norm288_dot_layer s 8
  · apply transfer (subtractAxis s 304 32 272 0 (by decide) (by decide))
    simpa using card_norm272_dot_layer s 0
  · apply transfer (subtractAxis s 304 40 256 (-8) (by decide) (by decide))
    simpa using card_norm256_dot_layer s (-8)
  · apply transfer (subtractAxis s 304 48 240 (-16) (by decide) (by decide))
    simpa using card_norm240_dot_layer s (-16)
  · apply transfer (subtractAxis s 304 56 224 (-24) (by decide) (by decide))
    simpa using card_norm224_dot_layer s (-24)
  · apply transfer (subtractAxis s 304 64 208 (-32) (by decide) (by decide))
    simpa using card_norm208_dot_layer s (-32)
  · apply transfer (subtractAxis s 304 72 192 (-40) (by decide) (by decide))
    simpa using card_norm192_dot_layer s (-40)
  · apply transfer (subtractAxis s 304 80 176 (-48) (by decide) (by decide))
    simpa using card_norm176_dot_layer s (-48)
  · apply transfer (subtractAxis s 304 88 160 (-56) (by decide) (by decide))
    simpa using card_norm160_dot_layer s (-56)
  · apply transfer (subtractAxis s 304 96 144 (-64) (by decide) (by decide))
    simpa using card_norm144_dot_layer s (-64)

private theorem inner_counts304 (s : PlayShortestVectors) :
    layerCount s 304 0 = 1695179576908800 ∧
    layerCount s 304 8 = 1582425260697600 ∧
    layerCount s 304 16 = 1281153205440000 := by
  obtain ⟨h24, h32, h40, h48, h56, h64, h72, h80, h88, h96⟩ := outer_counts304 s
  obtain ⟨h2, h4⟩ := LeechShellMoments.diff_moments 304
  rw [shell_card304] at h2 h4
  have total := sum_by_layers 304 products304 allowed304 s (fun _ => 1)
  have second := sum_by_layers 304 products304 allowed304 s (fun k => (k / 4) ^ 2)
  have fourth := sum_by_layers 304 products304 allowed304 s (fun k => (k / 4) ^ 4)
  have cancel (d : ℤ) : 4 * d / 4 = d := by omega
  simp only [cancel] at second fourth
  norm_num [products304, sum_insert, opposite_layer_count, h24, h32, h40, h48, h56, h64,
    h72, h80, h88, h96, shell_card304] at total second fourth
  omega

/-- For any shortest axis, count the vectors of squared length 304 at each integer dot product. -/
theorem card_norm304_dot_layer (s : PlayShortestVectors) (k : ℤ) :
    Nat.card {v : PlayNorm304Vectors // dot s.val v.val = k} =
      if k = 0 then 1695179576908800
      else if k = 8 ∨ k = -8 then 1582425260697600
      else if k = 16 ∨ k = -16 then 1281153205440000
      else if k = 24 ∨ k = -24 then 893508106291200
      else if k = 32 ∨ k = -32 then 527244094771200
      else if k = 40 ∨ k = -40 then 257042157926400
      else if k = 48 ∨ k = -48 then 99235434355200
      else if k = 56 ∨ k = -56 then 28500740352000
      else if k = 64 ∨ k = -64 then 5456580940800
      else if k = 72 ∨ k = -72 then 573172070400
      else if k = 80 ∨ k = -80 then 21771763200
      else if k = 88 ∨ k = -88 then 95385600
      else 0 := by
  classical
  apply Int.ofNat_inj.mp
  change layerCount s 304 k = _
  by_cases hk : k ∈ products304
  · obtain ⟨h0, h8, h16⟩ := inner_counts304 s
    obtain ⟨h24, h32, h40, h48, h56, h64, h72, h80, h88, h96⟩ := outer_counts304 s
    simp only [products304, mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;>
      norm_num [opposite_layer_count, h0, h8, h16, h24, h32, h40, h48, h56, h64,
        h72, h80, h88, h96]
  · have emptyLayer : (univ : Finset (Shell 304)).filter (fun x => 4 * diff x = k) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x _ hx
      exact hk (hx ▸ allowed304 x)
    rw [← reference_layer_card, emptyLayer]
    simp only [products304, mem_insert, mem_singleton, not_or] at hk
    obtain ⟨h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48, h56, hn56,
      h64, hn64, h72, hn72, h80, hn80, h88, hn88, _, _⟩ := hk
    simp [h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48, h56, hn56,
      h64, hn64, h72, hn72, h80, hn80, h88, hn88]

end LeechLayers
