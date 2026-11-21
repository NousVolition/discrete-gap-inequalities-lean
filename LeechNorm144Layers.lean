import LeechNorm144
import LeechNorm128Layers

/-! # Squared-length-144 layers along a shortest vector

Five positive layers come from earlier shells. The total and two coordinate
moments determine the inner layers. Negating a vector gives the other sign.
-/
namespace LeechLayers

open PlaygroundGolay PlaygroundLeech LeechLattice LeechMinimal LeechSymmetry Finset
open LeechShellMoments (Shell diff)

abbrev PlayNorm144Vectors := PlayShell 144

private noncomputable instance : Fintype (Shell 144) := by
  have : Finite (Shell 144) := (Nat.card_pos_iff.mp
    (show 0 < Nat.card (Shell 144) by rw [LeechNorm144.card_norm144_vectors]; decide)).2
  exact Fintype.ofFinite _

private theorem shell_card144 : Fintype.card (Shell 144) = 2975551488000 :=
  Nat.card_eq_fintype_card.symm.trans LeechNorm144.card_norm144_vectors

private def products144 : Finset ℤ := {0, 8, -8, 16, -16, 24, -24, 32, -32, 40, -40, 48, -48, 56, -56}

private theorem allowed144 (x : Shell 144) : 4 * diff x ∈ products144 := by
  let r := (ConwayPairs.root true).val
  let b := r + r
  have nr : normSq r = 32 := (ConwayPairs.root true).property.2
  have nb : normSq b = 128 := by
    change normSq (r + r) = 128
    rw [← two_nsmul, normSq_two_smul, nr]
    decide
  have hb : InLeech b := leechLattice.add_mem (ConwayPairs.root true).property.1 (ConwayPairs.root true).property.1
  have nx := x.property
  have dr : dot r x.val.val = 4 * diff x := ConwayPairs.root_dot _
  have db : dot b x.val.val = 2 * (4 * diff x) := by
    change dot (r + r) _ = _
    rw [dot_add_left, dr, two_mul]
  have nzsub : b - x.val.val ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h] at nb
    omega
  have nzadd : b + x.val.val ≠ 0 := by
    intro h
    rw [add_eq_zero_iff_eq_neg.mp h, normSq_neg] at nb
    omega
  have lo := leech_norm_ge_32 _ (leechLattice.add_mem hb x.val.property) nzadd
  have hi := leech_norm_ge_32 _ (leechLattice.sub_mem hb x.val.property) nzsub
  change 32 ≤ normSq (b + x.val.val) at lo
  change 32 ≤ normSq (b - x.val.val) at hi
  rw [normSq_add, nb, nx, db] at lo
  rw [normSq_sub, nb, nx, db] at hi
  obtain ⟨⟨q,hq⟩,_,_⟩ := reference_dot_bounds (by decide : (144 : ℤ) ≠ 32) x
  simp only [products144, mem_insert, mem_singleton]
  omega

private theorem outer_counts144 (s : PlayShortestVectors) :
    layerCount s 144 24 = 163357849600 ∧
    layerCount s 144 32 = 47406643200 ∧
    layerCount s 144 40 = 7535462400 ∧
    layerCount s 144 48 = 458086400 ∧
    layerCount s 144 56 = 4147200 := by
  have h24 : Nat.card (PlayLayer s 144 24) = 163357849600 := by
    rw [Nat.card_congr (subtractAxis s 144 24 128 8 (by decide) (by decide))]
    simpa using card_norm128_dot_layer s 8
  have h32 : Nat.card (PlayLayer s 144 32) = 47406643200 := by
    rw [Nat.card_congr (subtractAxis s 144 32 112 0 (by decide) (by decide))]
    simpa using card_norm112_dot_layer s 0
  have h40 : Nat.card (PlayLayer s 144 40) = 7535462400 := by
    rw [Nat.card_congr (subtractAxis s 144 40 96 (-8) (by decide) (by decide))]
    simpa using card_norm96_dot_layer s (-8)
  have h48 : Nat.card (PlayLayer s 144 48) = 458086400 := by
    rw [Nat.card_congr (subtractAxis s 144 48 80 (-16) (by decide) (by decide))]
    simpa using card_norm80_dot_layer s (-16)
  have h56 : Nat.card (PlayLayer s 144 56) = 4147200 := by
    rw [Nat.card_congr (subtractAxis s 144 56 64 (-24) (by decide) (by decide))]
    simpa using card_norm64_dot_layer s (-24)
  let cast := fun n : ℕ => (n : ℤ)
  exact ⟨congrArg cast h24, congrArg cast h32, congrArg cast h40, congrArg cast h48, congrArg cast h56⟩

private theorem inner_counts144 (s : PlayShortestVectors) :
    layerCount s 144 0 = 663509299200 ∧ layerCount s 144 8 = 573172070400 ∧ layerCount s 144 16 = 364086835200 := by
  obtain ⟨h24, h32, h40, h48, h56⟩ := outer_counts144 s
  obtain ⟨h2, h4⟩ := LeechShellMoments.diff_moments 144
  rw [shell_card144] at h2 h4
  have total := sum_by_layers 144 products144 allowed144 s (fun _ => 1)
  have second := sum_by_layers 144 products144 allowed144 s (fun k => (k / 4) ^ 2)
  have fourth := sum_by_layers 144 products144 allowed144 s (fun k => (k / 4) ^ 4)
  have cancel (d : ℤ) : 4*d/4 = d := by omega
  simp only [cancel] at second fourth
  norm_num [products144, sum_insert, opposite_layer_count, h24, h32, h40, h48, h56, shell_card144] at total second fourth
  omega

/-- Count the vectors of squared length 144 at every integer dot product with any shortest vector. -/
theorem card_norm144_dot_layer (s : PlayShortestVectors) (k : ℤ) :
    Nat.card {v : PlayNorm144Vectors // dot s.val v.val = k} =
      if k = 0 then 663509299200
      else if k = 8 ∨ k = -8 then 573172070400
      else if k = 16 ∨ k = -16 then 364086835200
      else if k = 24 ∨ k = -24 then 163357849600
      else if k = 32 ∨ k = -32 then 47406643200
      else if k = 40 ∨ k = -40 then 7535462400
      else if k = 48 ∨ k = -48 then 458086400
      else if k = 56 ∨ k = -56 then 4147200
      else 0 := by
  classical
  apply Int.ofNat_inj.mp
  change layerCount s 144 k = _
  by_cases hk : k ∈ products144
  · obtain ⟨h0, h8, h16⟩ := inner_counts144 s
    obtain ⟨h24, h32, h40, h48, h56⟩ := outer_counts144 s
    simp only [products144, mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [opposite_layer_count, h0, h8, h16, h24, h32, h40, h48, h56]
  · have noHits : (univ : Finset (Shell 144)).filter (fun x => 4 * diff x = k) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x _ hx
      exact hk (hx ▸ allowed144 x)
    rw [← reference_layer_card, noHits]
    simp only [products144, mem_insert, mem_singleton, not_or] at hk
    obtain ⟨h0,h8,hn8,h16,hn16,h24,hn24,h32,hn32,h40,hn40,h48,hn48,h56,hn56⟩ := hk
    simp [h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40, h48, hn48, h56, hn56]

end LeechLayers
