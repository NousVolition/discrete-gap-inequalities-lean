import LeechNorm272
import LeechNorm256Layers

/-! # Squared-length-272 layers along a shortest vector

Subtracting a vector from the axis gives the outer layers from smaller shells.
At dot product 88, this gives the −56 layer at squared length 128.
The shell total and two coordinate moments give the counts at 0, 8 and 16.
-/
namespace LeechLayers

open PlaygroundGolay PlaygroundLeech LeechLattice LeechSymmetry Finset
open LeechShellMoments (Shell diff)

abbrev PlayNorm272Vectors := PlayShell 272

private noncomputable instance : Fintype (Shell 272) := by
  have : Finite (Shell 272) := (Nat.card_pos_iff.mp
    (show 0 < Nat.card (Shell 272) by rw [LeechNorm272.card_norm272_vectors]; decide)).2
  exact Fintype.ofFinite _

private theorem shell_card272 : Fintype.card (Shell 272) = 3249631112232960 :=
  Nat.card_eq_fintype_card.symm.trans LeechNorm272.card_norm272_vectors

private def products272 : Finset ℤ :=
  {0, 8, -8, 16, -16, 24, -24, 32, -32, 40, -40, 48, -48, 56, -56, 64, -64,
    72, -72, 80, -80, 88, -88}

private theorem allowed272 (x : Shell 272) : 4 * diff x ∈ products272 := by
  obtain ⟨lo, hi⟩ := reference_double_dot_bounds (by decide : (272 : ℤ) ≠ 128) x
  obtain ⟨⟨q, hq⟩, _, _⟩ := reference_dot_bounds (by decide : (272 : ℤ) ≠ 32) x
  simp only [products272, mem_insert, mem_singleton]
  omega

private theorem outer_counts272 (s : PlayShortestVectors) :
    layerCount s 272 24 = 257042157926400 ∧
    layerCount s 272 32 = 141663767066624 ∧
    layerCount s 272 40 = 62511367475200 ∧
    layerCount s 272 48 = 20885920948224 ∧
    layerCount s 272 56 = 4841939097600 ∧
    layerCount s 272 64 = 663509299200 ∧
    layerCount s 272 72 = 39253082112 ∧
    layerCount s 272 80 = 458086400 ∧
    layerCount s 272 88 = 47104 := by
  have transfer {k m j : ℤ} {n : ℕ} (e : PlayLayer s 272 k ≃ PlayLayer s m j)
      (h : Nat.card (PlayLayer s m j) = n) : layerCount s 272 k = (n : ℤ) :=
    congrArg (fun a : ℕ => (a : ℤ)) ((Nat.card_congr e).trans h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply transfer (subtractAxis s 272 24 256 8 (by decide) (by decide))
    simpa using card_norm256_dot_layer s 8
  · apply transfer (subtractAxis s 272 32 240 0 (by decide) (by decide))
    simpa using card_norm240_dot_layer s 0
  · apply transfer (subtractAxis s 272 40 224 (-8) (by decide) (by decide))
    simpa using card_norm224_dot_layer s (-8)
  · apply transfer (subtractAxis s 272 48 208 (-16) (by decide) (by decide))
    simpa using card_norm208_dot_layer s (-16)
  · apply transfer (subtractAxis s 272 56 192 (-24) (by decide) (by decide))
    simpa using card_norm192_dot_layer s (-24)
  · apply transfer (subtractAxis s 272 64 176 (-32) (by decide) (by decide))
    simpa using card_norm176_dot_layer s (-32)
  · apply transfer (subtractAxis s 272 72 160 (-40) (by decide) (by decide))
    simpa using card_norm160_dot_layer s (-40)
  · apply transfer (subtractAxis s 272 80 144 (-48) (by decide) (by decide))
    simpa using card_norm144_dot_layer s (-48)
  · apply transfer (subtractAxis s 272 88 128 (-56) (by decide) (by decide))
    simpa using card_norm128_dot_layer s (-56)

private theorem inner_counts272 (s : PlayShortestVectors) :
    layerCount s 272 0 = 527244094771200 ∧
    layerCount s 272 8 = 488171450607616 ∧
    layerCount s 272 16 = 385373685094400 := by
  obtain ⟨h24, h32, h40, h48, h56, h64, h72, h80, h88⟩ := outer_counts272 s
  obtain ⟨h2, h4⟩ := LeechShellMoments.diff_moments 272
  rw [shell_card272] at h2 h4
  have total := sum_by_layers 272 products272 allowed272 s (fun _ => 1)
  have second := sum_by_layers 272 products272 allowed272 s (fun k => (k / 4) ^ 2)
  have fourth := sum_by_layers 272 products272 allowed272 s (fun k => (k / 4) ^ 4)
  have cancel (d : ℤ) : 4 * d / 4 = d := by omega
  simp only [cancel] at second fourth
  norm_num [products272, sum_insert, opposite_layer_count, h24, h32, h40, h48, h56, h64,
    h72, h80, h88, shell_card272] at total second fourth
  omega

/-- For any shortest axis, count the vectors of squared length 272 at each integer dot product. -/
theorem card_norm272_dot_layer (s : PlayShortestVectors) (k : ℤ) :
    Nat.card {v : PlayNorm272Vectors // dot s.val v.val = k} =
      if k = 0 then 527244094771200
      else if k = 8 ∨ k = -8 then 488171450607616
      else if k = 16 ∨ k = -16 then 385373685094400
      else if k = 24 ∨ k = -24 then 257042157926400
      else if k = 32 ∨ k = -32 then 141663767066624
      else if k = 40 ∨ k = -40 then 62511367475200
      else if k = 48 ∨ k = -48 then 20885920948224
      else if k = 56 ∨ k = -56 then 4841939097600
      else if k = 64 ∨ k = -64 then 663509299200
      else if k = 72 ∨ k = -72 then 39253082112
      else if k = 80 ∨ k = -80 then 458086400
      else if k = 88 ∨ k = -88 then 47104
      else 0 := by
  classical
  apply Int.ofNat_inj.mp
  change layerCount s 272 k = _
  by_cases hk : k ∈ products272
  · obtain ⟨h0, h8, h16⟩ := inner_counts272 s
    obtain ⟨h24, h32, h40, h48, h56, h64, h72, h80, h88⟩ := outer_counts272 s
    simp only [products272, mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [opposite_layer_count, h0, h8, h16, h24, h32, h40, h48, h56, h64, h72, h80, h88]
  · have emptyLayer : (univ : Finset (Shell 272)).filter (fun x => 4 * diff x = k) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x _ hx
      exact hk (hx ▸ allowed272 x)
    rw [← reference_layer_card, emptyLayer]
    simp only [products272, mem_insert, mem_singleton, not_or] at hk
    obtain ⟨h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48,
      h56, hn56, h64, hn64, h72, hn72, h80, hn80, h88, hn88⟩ := hk
    simp [h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48,
      h56, hn56, h64, hn64, h72, hn72, h80, hn80, h88, hn88]

end LeechLayers
