import LeechNorm160
import LeechNorm144Layers

/-! # Squared-length-160 layers along a shortest vector

Six positive layers come from earlier shells. The total and two coordinate
moments determine the inner layers. Negating a vector gives the other sign.
-/
namespace LeechLayers

open PlaygroundGolay PlaygroundLeech LeechLattice LeechSymmetry Finset
open LeechShellMoments (Shell diff)

abbrev PlayNorm160Vectors := PlayShell 160

private noncomputable instance : Fintype (Shell 160) := by
  have : Finite (Shell 160) := (Nat.card_pos_iff.mp
    (show 0 < Nat.card (Shell 160) by rw [LeechNorm160.card_norm160_vectors]; decide)).2
  exact Fintype.ofFinite _

private theorem shell_card160 : Fintype.card (Shell 160) = 9486551299680 :=
  Nat.card_eq_fintype_card.symm.trans LeechNorm160.card_norm160_vectors

private def products160 : Finset ℤ := {0, 8, -8, 16, -16, 24, -24, 32, -32, 40, -40, 48, -48, 56, -56, 64, -64}

private theorem allowed160 (x : Shell 160) : 4 * diff x ∈ products160 := by
  obtain ⟨lo, hi⟩ := reference_double_dot_bounds (by decide : (160 : ℤ) ≠ 128) x
  obtain ⟨⟨q, hq⟩, _, _⟩ := reference_dot_bounds (by decide : (160 : ℤ) ≠ 32) x
  simp only [products160, mem_insert, mem_singleton]
  omega

private theorem outer_counts160 (s : PlayShortestVectors) :
    layerCount s 160 24 = 573172070400 ∧
    layerCount s 160 32 = 192825064350 ∧
    layerCount s 160 40 = 39253082112 ∧
    layerCount s 160 48 = 3771829800 ∧
    layerCount s 160 56 = 95385600 ∧
    layerCount s 160 64 = 93150 := by
  have h24 : Nat.card (PlayLayer s 160 24) = 573172070400 := by
    rw [Nat.card_congr (subtractAxis s 160 24 144 8 (by decide) (by decide))]
    simpa using card_norm144_dot_layer s 8
  have h32 : Nat.card (PlayLayer s 160 32) = 192825064350 := by
    rw [Nat.card_congr (subtractAxis s 160 32 128 0 (by decide) (by decide))]
    simpa using card_norm128_dot_layer s 0
  have h40 : Nat.card (PlayLayer s 160 40) = 39253082112 := by
    rw [Nat.card_congr (subtractAxis s 160 40 112 (-8) (by decide) (by decide))]
    simpa using card_norm112_dot_layer s (-8)
  have h48 : Nat.card (PlayLayer s 160 48) = 3771829800 := by
    rw [Nat.card_congr (subtractAxis s 160 48 96 (-16) (by decide) (by decide))]
    simpa using card_norm96_dot_layer s (-16)
  have h56 : Nat.card (PlayLayer s 160 56) = 95385600 := by
    rw [Nat.card_congr (subtractAxis s 160 56 80 (-24) (by decide) (by decide))]
    simpa using card_norm80_dot_layer s (-24)
  have h64 : Nat.card (PlayLayer s 160 64) = 93150 := by
    rw [Nat.card_congr (subtractAxis s 160 64 64 (-32) (by decide) (by decide))]
    simpa using card_norm64_dot_layer s (-32)
  let cast := fun n : ℕ => (n : ℤ)
  exact ⟨congrArg cast h24, congrArg cast h32, congrArg cast h40,
    congrArg cast h48, congrArg cast h56, congrArg cast h64⟩

private theorem inner_counts160 (s : PlayShortestVectors) :
    layerCount s 160 0 = 2007834672456 ∧ layerCount s 160 8 = 1758528921600 ∧ layerCount s 160 16 = 1171711866600 := by
  obtain ⟨h24, h32, h40, h48, h56, h64⟩ := outer_counts160 s
  obtain ⟨h2, h4⟩ := LeechShellMoments.diff_moments 160
  rw [shell_card160] at h2 h4
  have total := sum_by_layers 160 products160 allowed160 s (fun _ => 1)
  have second := sum_by_layers 160 products160 allowed160 s (fun k => (k / 4) ^ 2)
  have fourth := sum_by_layers 160 products160 allowed160 s (fun k => (k / 4) ^ 4)
  have cancel (d : ℤ) : 4*d/4 = d := by omega
  simp only [cancel] at second fourth
  norm_num [products160, sum_insert, opposite_layer_count, h24, h32, h40, h48, h56, h64, shell_card160] at total second fourth
  omega

/-- Count the vectors of squared length 160 at every integer dot product with any shortest vector. -/
theorem card_norm160_dot_layer (s : PlayShortestVectors) (k : ℤ) :
    Nat.card {v : PlayNorm160Vectors // dot s.val v.val = k} =
      if k = 0 then 2007834672456
      else if k = 8 ∨ k = -8 then 1758528921600
      else if k = 16 ∨ k = -16 then 1171711866600
      else if k = 24 ∨ k = -24 then 573172070400
      else if k = 32 ∨ k = -32 then 192825064350
      else if k = 40 ∨ k = -40 then 39253082112
      else if k = 48 ∨ k = -48 then 3771829800
      else if k = 56 ∨ k = -56 then 95385600
      else if k = 64 ∨ k = -64 then 93150
      else 0 := by
  classical
  apply Int.ofNat_inj.mp
  change layerCount s 160 k = _
  by_cases hk : k ∈ products160
  · obtain ⟨h0, h8, h16⟩ := inner_counts160 s
    obtain ⟨h24, h32, h40, h48, h56, h64⟩ := outer_counts160 s
    simp only [products160, mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [opposite_layer_count, h0, h8, h16, h24, h32, h40, h48, h56, h64]
  · have noHits : (univ : Finset (Shell 160)).filter (fun x => 4 * diff x = k) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x _ hx
      exact hk (hx ▸ allowed160 x)
    rw [← reference_layer_card, noHits]
    simp only [products160, mem_insert, mem_singleton, not_or] at hk
    obtain ⟨h0,h8,hn8,h16,hn16,h24,hn24,h32,hn32,h40,hn40,h48,hn48,h56,hn56,h64,hn64⟩ := hk
    simp [h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48, h56, hn56, h64, hn64]

end LeechLayers
