import LeechCoordinateFrames
import PlaygroundLeech

/-! # Squared-length-64 layers along a shortest vector

Count pairs of vectors with a given dot product in both orders. In the standard
frame, a dot product with a signed axis reads off one coordinate of a shortest
vector. The three shortest-vector shapes give its possible values.
-/
namespace LeechLayers

open LeechLattice LeechMinimal LeechSymmetry ConwayPairs ConwayMoves GolayMathieu Finset

private abbrev Shell64 := {v : Lattice // normSq v.val = 64}

private noncomputable instance : Fintype Shell64 := by
  have : Finite Shell64 := (Nat.card_pos_iff.mp
    (show 0 < Nat.card Shell64 by rw [LeechCoordinateFrames.card_norm64_vectors]; decide)).2
  exact Fintype.ofFinite _

private def onShell64 (g : Aut) : Shell64 ≃ Shell64 :=
  Equiv.subtypeEquiv g.val fun x => by
    change normSq x.val = 64 ↔ normSq (g x).val = 64
    rw [map_norm]

private def axis64 (i : Point) : Shell64 := ⟨latticeAxis i, axis_norm i⟩

private def entry (k : ℤ) (s : MinimalVectors) (v : Shell64) : ℕ :=
  if dot s.val v.val.val = k then 1 else 0

private theorem entry_map (g : Aut) (k : ℤ) (s : MinimalVectors) (v : Shell64) :
    entry k (onShortest g s) (onShell64 g v) = entry k s v := by
  unfold entry
  change (if dot (g (asL s)).val (g v.val).val = k then _ else _) = _
  rw [map_dot]
  rfl

private noncomputable def row64 (k : ℤ) (s : MinimalVectors) : ℕ := ∑ v, entry k s v
private noncomputable def column64 (k : ℤ) (v : Shell64) : ℕ := ∑ s, entry k s v

private theorem same_row64 (k : ℤ) (s t : MinimalVectors) : row64 k s = row64 k t := by
  have move (g : Aut) (a : MinimalVectors) : row64 k (onShortest g a) = row64 k a := by
    unfold row64
    rw [← (onShell64 g).sum_comp (entry k (onShortest g a))]
    simp_rw [entry_map]
  obtain ⟨g, rfl⟩ := shortest_transitive s
  obtain ⟨h, rfl⟩ := shortest_transitive t
  exact (move g _).trans (move h _).symm

private theorem same_column64 (k : ℤ) (v : Shell64) : column64 k v = column64 k (axis64 0) := by
  obtain ⟨g, _, hg⟩ := norm64_transitive v.val v.property
  have hv : onShell64 g (axis64 0) = v := Subtype.ext hg
  rw [← hv]
  unfold column64
  rw [← Equiv.sum_comp (onShortest g) (fun s => entry k s (onShell64 g (axis64 0)))]
  simp_rw [entry_map]

-- The first count fixes a shortest vector. The second fixes a vector of squared length 64.
private theorem count_pairs64 (k : ℤ) (s : MinimalVectors) :
    196560 * row64 k s = 398034000 * column64 k (axis64 0) := by
  have hv : Fintype.card Shell64 = 398034000 :=
    Nat.card_eq_fintype_card.symm.trans LeechCoordinateFrames.card_norm64_vectors
  have h : (∑ a : MinimalVectors, row64 k a) = ∑ v : Shell64, column64 k v :=
    sum_comm
  rw [sum_congr rfl (fun a _ => same_row64 k a s),
    sum_congr rfl (fun v _ => same_column64 k v)] at h
  simpa [leech_kissing_number, hv] using h

-- Each coordinate supplies two signed frame vectors, including two hits at zero when it vanishes.
private def hits64 (k a : ℤ) : ℕ :=
  (if 8 * a = k then 1 else 0) + (if -(8 * a) = k then 1 else 0)

private theorem hits64_neg (k a : ℤ) : hits64 k (-a) = hits64 k a := by
  simp [hits64, add_comm]

private def inFrame64 (k : ℤ) (x : Vec) : ℕ := ∑ i, hits64 k (x i)

private theorem frame_columns64 (k : ℤ) :
    (∑ s : MinimalVectors, inFrame64 k s.val) = 48 * column64 k (axis64 0) := by
  have pair (i : Point) (s : MinimalVectors) : hits64 k (s.val i) =
      entry k s (axis64 i) + entry k s (onShell64 centralNegation (axis64 i)) := by
    change _ = (if dot s.val (axis i) = k then 1 else 0) +
      (if dot s.val (-(axis i)) = k then 1 else 0)
    have neg : dot s.val (-(axis i)) = -(dot s.val (axis i)) := by
      simp [dot, sum_neg_distrib]
    rw [neg, dot_axis]
    rfl
  unfold inFrame64
  rw [sum_comm]
  have per (i : Point) : (∑ s : MinimalVectors, hits64 k (s.val i)) =
      column64 k (axis64 0) + column64 k (axis64 0) := by
    simp_rw [pair i, sum_add_distrib]
    exact congrArg₂ (· + ·) (same_column64 k (axis64 i))
      (same_column64 k (onShell64 centralNegation (axis64 i)))
  simp_rw [per]
  simp
  omega

private theorem sum_on64 (t : Finset Point) (a b : ℕ) :
    (∑ i : Point, if i ∈ t then a else b) = t.card * a + (24 - t.card) * b := by
  rw [sum_ite]
  simp [filter_notMem_eq_sdiff, card_sdiff_of_subset]

private theorem even_frame64 (k q : ℤ) (x : Vec) (hx : ∀ i, x i = 0 ∨ x i = q ∨ x i = -q)
    (hq : q ≠ 0) : inFrame64 k x =
    (support x).card * hits64 k q + (24 - (support x).card) * hits64 k 0 := by
  have per (i : Point) : hits64 k (x i) =
      if i ∈ support x then hits64 k q else hits64 k 0 := by
    rcases hx i with h | h | h <;> simp [support, h, hq, hits64_neg]
  unfold inFrame64
  simp_rw [per]
  exact sum_on64 _ _ _

private theorem odd_frame64 (k : ℤ) {x : Vec} (h : OddShape x) :
    inFrame64 k x = hits64 k 3 + 23 * hits64 k 1 := by
  obtain ⟨w, _, j, rfl⟩ := h
  have per (i : Point) : hits64 k (oddVector w j i) =
      if i ∈ ({j} : Finset Point) then hits64 k 3 else hits64 k 1 := by
    by_cases h : i = j
    · subst i
      cases hw : w j <;> simp [oddVector, hw, hits64_neg]
    · cases hw : w i <;> simp [oddVector, h, hw, hits64_neg]
  unfold inFrame64
  simp_rw [per]
  rw [sum_on64]
  simp

private theorem frame_rows64 (k : ℤ) : (∑ s : MinimalVectors, inFrame64 k s.val) =
    1104 * (2 * hits64 k 4 + 22 * hits64 k 0) +
    97152 * (8 * hits64 k 2 + 16 * hits64 k 0) +
    98304 * (hits64 k 3 + 23 * hits64 k 1) := by
  let f := fun s : MinimalVectors => inFrame64 k s.val
  have four (x : FourVectors) : f (minimalEquiv (.inl x)) = 2 * hits64 k 4 + 22 * hits64 k 0 := by
    change inFrame64 k x.val = _
    rw [even_frame64 k 4 _ x.property.1 (by decide), x.property.2]
  have octad (x : OctadVectors) : f (minimalEquiv (.inr (.inl x))) =
      8 * hits64 k 2 + 16 * hits64 k 0 := by
    change inFrame64 k x.val = _
    rw [even_frame64 k 2 _ x.property.1 (by decide), x.property.2.2.1]
  have odd (x : OddVectors) : f (minimalEquiv (.inr (.inr x))) =
      hits64 k 3 + 23 * hits64 k 1 := odd_frame64 k x.property
  change (∑ s, f s) = _
  rw [← minimalEquiv.sum_comp f, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp_rw [four, octad, odd]
  simp [card_four, card_octad_vectors, card_odd, Nat.add_assoc]

open PlaygroundGolay PlaygroundLeech

/-- Vectors of squared length 64 in playground coordinates. -/
abbrev PlayNorm64Vectors := {v : Vec // InPlayLeech v ∧ normSq v = 64}

private def toShell64 : PlayNorm64Vectors ≃ Shell64 :=
  (Equiv.subtypeEquiv vectorEquiv (fun x => by
    change (InPlayLeech x ∧ normSq x = 64) ↔ (InLeech (toLean x) ∧ normSq (toLean x) = 64)
    rw [lattice_correspondence, norm_toLean])).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter InLeech (fun x => normSq x = 64)).symm

/-- Count the vectors of squared length 64 at every integer dot product with any shortest vector. -/
theorem card_norm64_dot_layer (s : PlayShortestVectors) (k : ℤ) :
    Nat.card {v : PlayNorm64Vectors // dot s.val v.val = k} =
      if k = 0 then 133204500
      else if k = 8 ∨ k = -8 then 95385600
      else if k = 16 ∨ k = -16 then 32788800
      else if k = 24 ∨ k = -24 then 4147200
      else if k = 32 ∨ k = -32 then 93150
      else 0 := by
  classical
  let a := LeechMinimal.shortestEquiv (PlaygroundLeech.shortestEquiv s)
  let e : {v : PlayNorm64Vectors // dot s.val v.val = k} ≃
      {v : Shell64 // dot a.val v.val.val = k} := Equiv.subtypeEquiv toShell64 fun v => by
    have h : dot (toLean s.val) (toLean v.val) = dot s.val v.val := by
      apply Fintype.sum_equiv coordinateEquiv.symm
      intro i
      rfl
    change dot s.val v.val = k ↔ dot (toLean s.val) (toLean v.val) = k
    rw [h]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have row : row64 k a = ((univ : Finset Shell64).filter (fun v => dot a.val v.val.val = k)).card := by
    simp [row64, entry, sum_boole]
  rw [← row]
  have pairs := count_pairs64 k a
  have frame := (frame_columns64 k).symm.trans (frame_rows64 k)
  by_cases hk : k ∈ ({0, 8, -8, 16, -16, 24, -24, 32, -32} : Finset ℤ)
  · simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [hits64] at frame ⊢ <;> omega
  · simp only [mem_insert, mem_singleton, not_or] at hk
    obtain ⟨h0,h8,hn8,h16,hn16,h24,hn24,h32,hn32⟩ := hk
    have empty (j : ℤ) (h : j ∈ ({0, 1, 2, 3, 4} : Finset ℤ)) : hits64 k j = 0 := by
      simp only [mem_insert, mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> unfold hits64 <;> split_ifs <;> omega
    simp [empty, h0, h8, hn8, h16, hn16, h24, hn24, h32, hn32] at frame ⊢
    omega

private theorem column_zero_at_axis : column64 0 (axis64 0) = 65780 := by
  have h : 48 * column64 0 (axis64 0) = 3157440 :=
    (frame_columns64 0).symm.trans ((frame_rows64 0).trans (by decide))
  exact (show ∀ n : ℕ, 48 * n = 3157440 → n = 65780 by omega) _ h

private theorem count_zero_entries {α : Type} [Fintype α] (a : α → ℤ) :
    Nat.card {s : α // a s = 0} = ∑ s : α, (if 8 * a s = 0 then 1 else 0 : ℕ) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or, sum_boole, Nat.cast_id]

private theorem zero_coordinate_column (i : Point) :
    Nat.card {s : MinimalVectors // s.val i = 0} = column64 0 (axis64 i) := by
  apply (count_zero_entries (fun s : MinimalVectors => s.val i)).trans
  unfold column64
  apply sum_congr rfl
  intro s _
  change (if 8 * s.val i = 0 then 1 else 0) = (if dot s.val (axis i) = 0 then 1 else 0)
  rw [dot_axis]

/-- At any given coordinate, 65,780 shortest vectors have value zero. -/
theorem card_shortest_zero_coordinate (i : Point) :
    Nat.card {s : MinimalVectors // s.val i = 0} = 65780 :=
  (zero_coordinate_column i).trans ((same_column64 0 (axis64 i)).trans column_zero_at_axis)

end LeechLayers
