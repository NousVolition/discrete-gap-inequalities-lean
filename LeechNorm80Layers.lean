import LeechNorm80
import LeechNorm64Layers
import LeechLayers

/-! # Squared-length-80 layers along a shortest vector

Subtracting a vector from the axis gives three outer counts from the tables for
squared lengths 64, 48 and 32. The total and two coordinate moments give the rest.
-/
namespace LeechLayers

open PlaygroundGolay PlaygroundLeech LeechLattice LeechMinimal LeechSymmetry ConwayPairs Finset
open LeechShellMoments (Shell onShell diff)

abbrev PlayShell (m : ℤ) := {v : Vec // InPlayLeech v ∧ normSq v = m}
abbrev PlayLayer (s : PlayShortestVectors) (m k : ℤ) :=
  {v : PlayShell m // dot s.val v.val = k}

/-- Vectors of squared length 80 in playground coordinates. -/
abbrev PlayNorm80Vectors := {v : Vec // InPlayLeech v ∧ normSq v = 80}

noncomputable def layerCount (s : PlayShortestVectors) (m k : ℤ) : ℤ :=
  Nat.card (PlayLayer s m k)

-- Subtract twice from the same axis to recover the starting vector.
def subtractAxis (s : PlayShortestVectors) (m k n j : ℤ)
    (hn : 32 + m - 2*k = n) (hj : 32-k = j) : PlayLayer s m k ≃ PlayLayer s n j := by
  obtain ⟨hs, ns⟩ := (play_shortest_iff_norm32 _).mp s.property
  have self : dot s.val s.val = 32 := by simpa [dot, normSq, pow_two] using ns
  have subDot (x : Vec) : dot s.val (s.val - x) = 32 - dot s.val x := by
    rw [← self]
    simp [dot, mul_sub, sum_sub_distrib]
  let send {a b c d : ℤ} (hc : 32 + a - 2*b = c) (hd : 32-b = d)
      (v : PlayLayer s a b) : PlayLayer s c d :=
    ⟨⟨s.val - v.val.val, (lattice_correspondence _).mpr (leechLattice.sub_mem
        ((lattice_correspondence _).mp hs) ((lattice_correspondence _).mp v.val.property.1)),
       by rw [normSq_sub, ns, v.val.property.2, v.property, hc]⟩,
     by rw [subDot, v.property, hd]⟩
  refine ⟨send hn hj, send (by omega) (by omega), ?_, ?_⟩ <;> intro x <;>
    apply Subtype.ext <;> apply Subtype.ext <;>
    change s.val - (s.val - x.val.val) = x.val.val <;> abel

private theorem outer_counts80 (s : PlayShortestVectors) :
    layerCount s 80 24 = 95385600 ∧ layerCount s 80 32 = 6476800 ∧ layerCount s 80 40 = 47104 := by
  have a : Nat.card (PlayLayer s 80 24) = 95385600 := by
    rw [Nat.card_congr (subtractAxis s 80 24 64 8 (by decide) (by decide))]
    simpa using card_norm64_dot_layer s 8
  have b : Nat.card (PlayLayer s 80 32) = 6476800 := by
    rw [Nat.card_congr (subtractAxis s 80 32 48 0 (by decide) (by decide))]
    simpa using card_norm48_dot_layer s 0
  have c : Nat.card (PlayLayer s 80 40) = 47104 := by
    let e : PlayShell 32 ≃ PlayShortestVectors :=
      Equiv.subtypeEquivRight fun v => (play_shortest_iff_norm32 v).symm
    let layer : PlayLayer s 32 (-8) ≃ {v : PlayShortestVectors // dot s.val v.val = -8} :=
      Equiv.subtypeEquiv e fun _ => Iff.rfl
    rw [Nat.card_congr (subtractAxis s 80 40 32 (-8) (by decide) (by decide)),
      Nat.card_congr layer]
    exact card_dot_neg_eight s
  exact ⟨congrArg (fun n : ℕ => (n : ℤ)) a, congrArg (fun n : ℕ => (n : ℤ)) b,
    congrArg (fun n : ℕ => (n : ℤ)) c⟩

private noncomputable instance : Fintype (Shell 80) := by
  have : Finite (Shell 80) := (Nat.card_pos_iff.mp
    (show 0 < Nat.card (Shell 80) by rw [LeechNorm80.card_norm80_vectors]; decide)).2
  exact Fintype.ofFinite _

private theorem shell_card80 : Fintype.card (Shell 80) = 4629381120 :=
  Nat.card_eq_fintype_card.symm.trans LeechNorm80.card_norm80_vectors

def toLatticeShell (m : ℤ) : PlayShell m ≃ Shell m :=
  (Equiv.subtypeEquiv vectorEquiv (fun x => by
    change (InPlayLeech x ∧ normSq x = m) ↔ (InLeech (toLean x) ∧ normSq (toLean x) = m)
    rw [lattice_correspondence, norm_toLean])).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter InLeech (fun x => normSq x = m)).symm

private def products80 : Finset ℤ := {0, 8, -8, 16, -16, 24, -24, 32, -32, 40, -40}

theorem reference_dot_bounds {m : ℤ} (hm : m ≠ 32) (x : Shell m) :
    (8 ∣ 4 * diff x) ∧ -m ≤ 2 * (4 * diff x) ∧ 2 * (4 * diff x) ≤ m := by
  let r := (root true).val
  have nr : normSq r = 32 := (root true).property.2
  have nx := x.property
  have dr : dot r x.val.val = 4 * diff x := root_dot _
  have nzsub : r - x.val.val ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h] at nr
    omega
  have nzadd : r + x.val.val ≠ 0 := by
    intro h
    rw [add_eq_zero_iff_eq_neg.mp h, normSq_neg] at nr
    omega
  have lo := leech_norm_ge_32 _ (leechLattice.add_mem (root true).property.1 x.val.property) nzadd
  have hi := leech_norm_ge_32 _ (leechLattice.sub_mem (root true).property.1 x.val.property) nzsub
  change 32 ≤ normSq (r + x.val.val) at lo
  change 32 ≤ normSq (r - x.val.val) at hi
  rw [normSq_add, nr, nx, dr] at lo
  rw [normSq_sub, nr, nx, dr] at hi
  obtain ⟨q,hq⟩ := LeechBasis.leech_inner_dvd_eight _ _ (root true).property.1 x.val.property
  change dot r x.val.val = 8*q at hq
  rw [dr] at hq
  exact ⟨⟨q, hq⟩, by omega, by omega⟩

private theorem allowed80 (x : Shell 80) : 4 * diff x ∈ products80 := by
  obtain ⟨⟨q,hq⟩,lo,hi⟩ := reference_dot_bounds (by decide : (80 : ℤ) ≠ 32) x
  simp only [products80, mem_insert, mem_singleton]
  omega

-- A symmetry takes the reference shortest vector to the selected playground axis.
theorem reference_layer_card (m : ℤ) [Fintype (Shell m)] (s : PlayShortestVectors) (k : ℤ) :
    (((univ : Finset (Shell m)).filter fun x => 4 * diff x = k).card : ℤ) = layerCount s m k := by
  let a := LeechMinimal.shortestEquiv (PlaygroundLeech.shortestEquiv s)
  obtain ⟨g, hg⟩ := shortest_transitive a
  let e := (onShell (m := m) g).trans (toLatticeShell m).symm
  let layer : {x : Shell m // 4 * diff x = k} ≃ PlayLayer s m k :=
    Equiv.subtypeEquiv e fun x => by
      have hd : dot (toLean s.val) (toLean (e x).val) = dot s.val (e x).val := by
        apply Fintype.sum_equiv coordinateEquiv.symm
        intro i
        rfl
      change dot a.val ((toLatticeShell m) (e x)).val.val = _ at hd
      have he : (toLatticeShell m) (e x) = onShell g x := (toLatticeShell m).apply_symm_apply _
      rw [← hd, he, ← hg]
      change 4 * diff x = k ↔ dot (g (asL (root true))).val (g x.val).val = k
      rw [map_dot]
      change 4 * diff x = k ↔ dot (root true).val x.val.val = k
      rw [root_dot]
      rfl
  have h := Nat.card_congr layer
  rw [Nat.card_eq_fintype_card (α := {x : Shell m // 4 * diff x = k}), Fintype.card_subtype] at h
  exact congrArg (fun n : ℕ => (n : ℤ)) h

theorem opposite_layer_count (m : ℤ) (s : PlayShortestVectors) (k : ℤ) : layerCount s m (-k) = layerCount s m k := by
  let neg (x : PlayShell m) : PlayShell m :=
    ⟨-x.val, (lattice_correspondence _).mpr (leechLattice.neg_mem ((lattice_correspondence _).mp x.property.1)),
      (normSq_neg x.val).trans x.property.2⟩
  let e : PlayShell m ≃ PlayShell m := ⟨neg, neg,
    fun x => Subtype.ext (neg_neg x.val), fun x => Subtype.ext (neg_neg x.val)⟩
  let layer : PlayLayer s m (-k) ≃ PlayLayer s m k := Equiv.subtypeEquiv e fun x => by
    change dot s.val x.val = -k ↔ dot s.val (-x.val) = k
    simp [dot, sum_neg_distrib]
    omega
  exact congrArg (fun n : ℕ => (n : ℤ)) (Nat.card_congr layer)

theorem sum_by_layers (m : ℤ) [Fintype (Shell m)] (products : Finset ℤ)
    (covers : ∀ x : Shell m, 4 * diff x ∈ products) (s : PlayShortestVectors) (f : ℤ → ℤ) :
    (∑ x : Shell m, f (4 * diff x)) = ∑ k ∈ products, layerCount s m k * f k := by
  classical
  have h := (sum_fiberwise_of_maps_to' (s := (univ : Finset (Shell m)))
    (g := fun x => 4 * diff x) (fun x _ => covers x) f).symm
  simpa only [sum_const, nsmul_eq_mul, reference_layer_card m s] using h

private theorem inner_counts80 (s : PlayShortestVectors) :
    layerCount s 80 0 = 1384998912 ∧ layerCount s 80 8 = 1062195200 ∧ layerCount s 80 16 = 458086400 := by
  obtain ⟨h24, h32, h40⟩ := outer_counts80 s
  obtain ⟨h2, h4⟩ := LeechShellMoments.diff_moments 80
  rw [shell_card80] at h2 h4
  have total := sum_by_layers 80 products80 allowed80 s (fun _ => 1)
  have second := sum_by_layers 80 products80 allowed80 s (fun k => (k / 4) ^ 2)
  have fourth := sum_by_layers 80 products80 allowed80 s (fun k => (k / 4) ^ 4)
  have cancel (d : ℤ) : 4*d/4 = d := by omega
  simp only [cancel] at second fourth
  norm_num [products80, sum_insert, opposite_layer_count, h24, h32, h40, shell_card80] at total second fourth
  omega

/-- Count the vectors of squared length 80 at every integer dot product with any shortest vector. -/
theorem card_norm80_dot_layer (s : PlayShortestVectors) (k : ℤ) :
    Nat.card {v : PlayNorm80Vectors // dot s.val v.val = k} =
      if k = 0 then 1384998912
      else if k = 8 ∨ k = -8 then 1062195200
      else if k = 16 ∨ k = -16 then 458086400
      else if k = 24 ∨ k = -24 then 95385600
      else if k = 32 ∨ k = -32 then 6476800
      else if k = 40 ∨ k = -40 then 47104
      else 0 := by
  classical
  apply Int.ofNat_inj.mp
  change layerCount s 80 k = _
  by_cases hk : k ∈ products80
  · obtain ⟨h0, h8, h16⟩ := inner_counts80 s
    obtain ⟨h24, h32, h40⟩ := outer_counts80 s
    simp only [products80, mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [opposite_layer_count, h0, h8, h16, h24, h32, h40]
  · have noHits : (univ : Finset (Shell 80)).filter (fun x => 4 * diff x = k) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro x _ hx
      exact hk (hx ▸ allowed80 x)
    rw [← reference_layer_card, noHits]
    simp only [products80, mem_insert, mem_singleton, not_or] at hk
    obtain ⟨h0,h8,hn8,h16,hn16,h24,hn24,h32,hn32,h40,hn40⟩ := hk
    simp [h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32, h40, hn40]

end LeechLayers
