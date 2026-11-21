import LeechNorm192
import LeechNorm176Layers

/-! # Squared-length-192 layers along a shortest vector

The map from v to s − v gives seven positive layers from smaller shells.
The shell total and two coordinate moments give the layers at 0, 8 and 16.
Negating v exchanges the two signs.
-/
namespace LeechLayers

open PlaygroundGolay PlaygroundLeech LeechLattice LeechSymmetry Finset
open LeechShellMoments (Shell diff)

abbrev PlayNorm192Vectors := PlayShell 192

private noncomputable instance : Fintype (Shell 192) := by
  have : Finite (Shell 192) := (Nat.card_pos_iff.mp
    (show 0 < Nat.card (Shell 192) by rw [LeechNorm192.card_norm192_vectors]; decide)).2
  exact Fintype.ofFinite _

private theorem shell_card192 : Fintype.card (Shell 192) = 70486236999360 :=
  Nat.card_eq_fintype_card.symm.trans LeechNorm192.card_norm192_vectors

private def products192 : Finset ℤ :=
  {0, 8, -8, 16, -16, 24, -24, 32, -32, 40, -40, 48, -48, 56, -56, 64, -64, 72, -72}

private theorem allowed192 (x : Shell 192) : 4 * diff x ∈ products192 := by
  obtain ⟨lo, hi⟩ := reference_double_dot_bounds (by decide : (192 : ℤ) ≠ 128) x
  obtain ⟨⟨q, hq⟩, _, _⟩ := reference_dot_bounds (by decide : (192 : ℤ) ≠ 32) x
  simp only [products192, mem_insert, mem_singleton]
  omega

private theorem outer_counts192 (s : PlayShortestVectors) :
    layerCount s 192 24 = 4841939097600 ∧
    layerCount s 192 32 = 2007834672456 ∧
    layerCount s 192 40 = 573172070400 ∧
    layerCount s 192 48 = 97917423808 ∧
    layerCount s 192 56 = 7535462400 ∧
    layerCount s 192 64 = 133204500 ∧
    layerCount s 192 72 = 47104 := by
  have transfer {k m j : ℤ} {n : ℕ} (e : PlayLayer s 192 k ≃ PlayLayer s m j)
      (h : Nat.card (PlayLayer s m j) = n) : layerCount s 192 k = (n : ℤ) :=
    congrArg (fun a : ℕ => (a : ℤ)) ((Nat.card_congr e).trans h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply transfer (subtractAxis s 192 24 176 8 (by decide) (by decide))
    simpa using card_norm176_dot_layer s 8
  · apply transfer (subtractAxis s 192 32 160 0 (by decide) (by decide))
    simpa using card_norm160_dot_layer s 0
  · apply transfer (subtractAxis s 192 40 144 (-8) (by decide) (by decide))
    simpa using card_norm144_dot_layer s (-8)
  · apply transfer (subtractAxis s 192 48 128 (-16) (by decide) (by decide))
    simpa using card_norm128_dot_layer s (-16)
  · apply transfer (subtractAxis s 192 56 112 (-24) (by decide) (by decide))
    simpa using card_norm112_dot_layer s (-24)
  · apply transfer (subtractAxis s 192 64 96 (-32) (by decide) (by decide))
    simpa using card_norm96_dot_layer s (-32)
  · apply transfer (subtractAxis s 192 72 80 (-40) (by decide) (by decide))
    simpa using card_norm80_dot_layer s (-40)

private theorem inner_counts192 (s : PlayShortestVectors) :
    layerCount s 192 0 = 13618454702600 ∧
    layerCount s 192 8 = 12194621632512 ∧
    layerCount s 192 16 = 8710737537600 := by
  obtain ⟨h24, h32, h40, h48, h56, h64, h72⟩ := outer_counts192 s
  obtain ⟨h2, h4⟩ := LeechShellMoments.diff_moments 192
  rw [shell_card192] at h2 h4
  have total := sum_by_layers 192 products192 allowed192 s (fun _ => 1)
  have second := sum_by_layers 192 products192 allowed192 s (fun k => (k / 4) ^ 2)
  have fourth := sum_by_layers 192 products192 allowed192 s (fun k => (k / 4) ^ 4)
  have cancel (d : ℤ) : 4 * d / 4 = d := by omega
  simp only [cancel] at second fourth
  norm_num [products192, sum_insert, opposite_layer_count, h24, h32, h40, h48, h56, h64,
    h72, shell_card192] at total second fourth
  omega

/-- For any shortest axis, count the vectors of squared length 192 at each integer dot product. -/
theorem card_norm192_dot_layer (s : PlayShortestVectors) (k : ℤ) :
    Nat.card {v : PlayNorm192Vectors // dot s.val v.val = k} =
      if k = 0 then 13618454702600
      else if k = 8 ∨ k = -8 then 12194621632512
      else if k = 16 ∨ k = -16 then 8710737537600
      else if k = 24 ∨ k = -24 then 4841939097600
      else if k = 32 ∨ k = -32 then 2007834672456
      else if k = 40 ∨ k = -40 then 573172070400
      else if k = 48 ∨ k = -48 then 97917423808
      else if k = 56 ∨ k = -56 then 7535462400
      else if k = 64 ∨ k = -64 then 133204500
      else if k = 72 ∨ k = -72 then 47104
      else 0 := by
  classical
  apply Int.ofNat_inj.mp
  change layerCount s 192 k = _
  by_cases hk : k ∈ products192
  · obtain ⟨h0, h8, h16⟩ := inner_counts192 s
    obtain ⟨h24, h32, h40, h48, h56, h64, h72⟩ := outer_counts192 s
    simp only [products192, mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [opposite_layer_count, h0, h8, h16, h24, h32, h40, h48, h56, h64, h72]
  · have emptyLayer : (univ : Finset (Shell 192)).filter (fun x => 4 * diff x = k) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x _ hx
      exact hk (hx ▸ allowed192 x)
    rw [← reference_layer_card, emptyLayer]
    simp only [products192, mem_insert, mem_singleton, not_or] at hk
    obtain ⟨h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48,
      h56, hn56, h64, hn64, h72, hn72⟩ := hk
    simp [h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48,
      h56, hn56, h64, hn64, h72, hn72]

end LeechLayers
