import LeechNorm176
import LeechNorm160Layers

/-! # Squared-length-176 layers along a shortest vector

Six positive layers come from earlier shells. The total and two coordinate
moments determine the inner layers. Negating a vector gives the other sign.
-/
namespace LeechLayers

open PlaygroundGolay PlaygroundLeech LeechLattice LeechSymmetry Finset
open LeechShellMoments (Shell diff)

abbrev PlayNorm176Vectors := PlayShell 176

private noncomputable instance : Fintype (Shell 176) := by
  have : Finite (Shell 176) := (Nat.card_pos_iff.mp
    (show 0 < Nat.card (Shell 176) by rw [LeechNorm176.card_norm176_vectors]; decide)).2
  exact Fintype.ofFinite _

private theorem shell_card176 : Fintype.card (Shell 176) = 27052945920000 :=
  Nat.card_eq_fintype_card.symm.trans LeechNorm176.card_norm176_vectors

private def products176 : Finset ℤ := {0, 8, -8, 16, -16, 24, -24, 32, -32, 40, -40, 48, -48, 56, -56, 64, -64}

private theorem allowed176 (x : Shell 176) : 4 * diff x ∈ products176 := by
  obtain ⟨lo, hi⟩ := reference_double_dot_bounds (by decide : (176 : ℤ) ≠ 128) x
  obtain ⟨⟨q, hq⟩, _, _⟩ := reference_dot_bounds (by decide : (176 : ℤ) ≠ 32) x
  simp only [products176, mem_insert, mem_singleton]
  omega

private theorem outer_counts176 (s : PlayShortestVectors) :
    layerCount s 176 24 = 1758528921600 ∧
    layerCount s 176 32 = 663509299200 ∧
    layerCount s 176 40 = 163357849600 ∧
    layerCount s 176 48 = 21771763200 ∧
    layerCount s 176 56 = 1062195200 ∧
    layerCount s 176 64 = 6476800 := by
  have h24 : Nat.card (PlayLayer s 176 24) = 1758528921600 := by
    rw [Nat.card_congr (subtractAxis s 176 24 160 8 (by decide) (by decide))]
    simpa using card_norm160_dot_layer s 8
  have h32 : Nat.card (PlayLayer s 176 32) = 663509299200 := by
    rw [Nat.card_congr (subtractAxis s 176 32 144 0 (by decide) (by decide))]
    simpa using card_norm144_dot_layer s 0
  have h40 : Nat.card (PlayLayer s 176 40) = 163357849600 := by
    rw [Nat.card_congr (subtractAxis s 176 40 128 (-8) (by decide) (by decide))]
    simpa using card_norm128_dot_layer s (-8)
  have h48 : Nat.card (PlayLayer s 176 48) = 21771763200 := by
    rw [Nat.card_congr (subtractAxis s 176 48 112 (-16) (by decide) (by decide))]
    simpa using card_norm112_dot_layer s (-16)
  have h56 : Nat.card (PlayLayer s 176 56) = 1062195200 := by
    rw [Nat.card_congr (subtractAxis s 176 56 96 (-24) (by decide) (by decide))]
    simpa using card_norm96_dot_layer s (-24)
  have h64 : Nat.card (PlayLayer s 176 64) = 6476800 := by
    rw [Nat.card_congr (subtractAxis s 176 64 80 (-32) (by decide) (by decide))]
    simpa using card_norm80_dot_layer s (-32)
  let cast := fun n : ℕ => (n : ℤ)
  exact ⟨congrArg cast h24, congrArg cast h32, congrArg cast h40,
    congrArg cast h48, congrArg cast h56, congrArg cast h64⟩

private theorem inner_counts176 (s : PlayShortestVectors) :
    layerCount s 176 0 = 5456580940800 ∧ layerCount s 176 8 = 4841939097600 ∧ layerCount s 176 16 = 3348006886400 := by
  obtain ⟨h24, h32, h40, h48, h56, h64⟩ := outer_counts176 s
  obtain ⟨h2, h4⟩ := LeechShellMoments.diff_moments 176
  rw [shell_card176] at h2 h4
  have total := sum_by_layers 176 products176 allowed176 s (fun _ => 1)
  have second := sum_by_layers 176 products176 allowed176 s (fun k => (k / 4) ^ 2)
  have fourth := sum_by_layers 176 products176 allowed176 s (fun k => (k / 4) ^ 4)
  have cancel (d : ℤ) : 4*d/4 = d := by omega
  simp only [cancel] at second fourth
  norm_num [products176, sum_insert, opposite_layer_count, h24, h32, h40, h48, h56, h64, shell_card176] at total second fourth
  omega

/-- Count the vectors of squared length 176 at every integer dot product with any shortest vector. -/
theorem card_norm176_dot_layer (s : PlayShortestVectors) (k : ℤ) :
    Nat.card {v : PlayNorm176Vectors // dot s.val v.val = k} =
      if k = 0 then 5456580940800
      else if k = 8 ∨ k = -8 then 4841939097600
      else if k = 16 ∨ k = -16 then 3348006886400
      else if k = 24 ∨ k = -24 then 1758528921600
      else if k = 32 ∨ k = -32 then 663509299200
      else if k = 40 ∨ k = -40 then 163357849600
      else if k = 48 ∨ k = -48 then 21771763200
      else if k = 56 ∨ k = -56 then 1062195200
      else if k = 64 ∨ k = -64 then 6476800
      else 0 := by
  classical
  apply Int.ofNat_inj.mp
  change layerCount s 176 k = _
  by_cases hk : k ∈ products176
  · obtain ⟨h0, h8, h16⟩ := inner_counts176 s
    obtain ⟨h24, h32, h40, h48, h56, h64⟩ := outer_counts176 s
    simp only [products176, mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [opposite_layer_count, h0, h8, h16, h24, h32, h40, h48, h56, h64]
  · have noHits : (univ : Finset (Shell 176)).filter (fun x => 4 * diff x = k) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x _ hx
      exact hk (hx ▸ allowed176 x)
    rw [← reference_layer_card, noHits]
    simp only [products176, mem_insert, mem_singleton, not_or] at hk
    obtain ⟨h0,h8,hn8,h16,hn16,h24,hn24,h32,hn32,h40,hn40,h48,hn48,h56,hn56,h64,hn64⟩ := hk
    simp [h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48, h56, hn56, h64, hn64]

end LeechLayers
