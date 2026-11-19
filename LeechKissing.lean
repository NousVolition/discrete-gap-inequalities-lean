import LeechFourCount
import LeechOctadVectors
import LeechOddCount

/-! # Counting the shortest vectors of the defined Leech lattice

The three families are disjoint and exhaust the vectors of squared length 32.
Their parameter counts therefore count lattice vectors, not merely candidate shapes.
-/
namespace LeechMinimal

open LeechLattice LeechCodeCounts GolayMatrixDistance

theorem four_octad_disjoint {x : Vec} (h4 : FourShape x) (h8 : OctadShape x) : False := by
  have := h4.2
  have := h8.2.2.1
  omega

theorem oddShape_parity {x : Vec} (hx : OddShape x) (i : Fin 24) : x i % 2 = 1 := by
  obtain ⟨w, _, j, rfl⟩ := hx
  by_cases hi : i = j
  · subst i; cases hw : w j <;> simp [oddVector, hw]
  · cases hw : w i <;> simp [oddVector, hi, hw]

theorem four_odd_disjoint {x : Vec} (h4 : FourShape x) (ho : OddShape x) : False := by
  have h := oddShape_parity ho 0
  rcases h4.1 0 with hv | hv | hv <;> simp [hv] at h

theorem octad_odd_disjoint {x : Vec} (h8 : OctadShape x) (ho : OddShape x) : False := by
  have h := oddShape_parity ho 0
  rcases h8.1 0 with hv | hv | hv <;> simp [hv] at h

abbrev MinimalVectors := {x : Vec // InLeech x ∧ normSq x = 32}
abbrev Families := FourVectors ⊕ (OctadVectors ⊕ OddVectors)

def familyMap : Families → MinimalVectors
  | .inl x => ⟨x.val, four_mem_norm x.property⟩
  | .inr (.inl x) => ⟨x.val, octad_mem_norm x.property⟩
  | .inr (.inr x) => ⟨x.val, odd_mem_norm x.property⟩

theorem familyMap_bijective : Function.Bijective familyMap := by
  constructor
  · intro p q h
    have hv := congrArg Subtype.val h
    rcases p with p | (p | p) <;> rcases q with q | (q | q)
    · exact congrArg Sum.inl (Subtype.ext hv)
    · exact False.elim (four_octad_disjoint (hv ▸ p.property) q.property)
    · exact False.elim (four_odd_disjoint (hv ▸ p.property) q.property)
    · exact False.elim (four_octad_disjoint q.property (hv ▸ p.property))
    · exact congrArg (fun x => Sum.inr (Sum.inl x)) (Subtype.ext hv)
    · exact False.elim (octad_odd_disjoint (hv ▸ p.property) q.property)
    · exact False.elim (four_odd_disjoint q.property (hv ▸ p.property))
    · exact False.elim (octad_odd_disjoint q.property (hv ▸ p.property))
    · exact congrArg (fun x => Sum.inr (Sum.inr x)) (Subtype.ext hv)
  · rintro ⟨x, hx⟩
    rcases (minimal_iff x).1 hx with h4 | h8 | ho
    · exact ⟨.inl ⟨x, h4⟩, rfl⟩
    · exact ⟨.inr (.inl ⟨x, h8⟩), rfl⟩
    · exact ⟨.inr (.inr ⟨x, ho⟩), rfl⟩

noncomputable def minimalEquiv : Families ≃ MinimalVectors :=
  Equiv.ofBijective familyMap familyMap_bijective

noncomputable instance : Fintype MinimalVectors := Fintype.ofEquiv Families minimalEquiv

/-- The three proved family cardinalities count the norm-32 vectors of `InLeech`. -/
theorem leech_kissing_number : Fintype.card MinimalVectors = 196560 := by
  rw [← Fintype.card_congr minimalEquiv, Fintype.card_sum, Fintype.card_sum,
    card_four, card_octad_vectors, card_odd]

/-- The earlier code-derived formula equals the cardinality of the defined lattice's shell. -/
theorem card_minimal_eq_code_formula : Fintype.card MinimalVectors =
    Nat.choose 24 2 * 2 ^ 2 + weightCounts.2.1 * 2 ^ 7 +
      (weightCounts.1 + weightCounts.2.1 + weightCounts.2.2.1 +
        weightCounts.2.2.2.1 + weightCounts.2.2.2.2) * 24 :=
  leech_kissing_number.trans GolayLeechBridge.leech_kissing_from_code.symm

def IsShortest (x : Vec) : Prop :=
  InLeech x ∧ x ≠ 0 ∧ ∀ y : Vec, InLeech y → y ≠ 0 → normSq x ≤ normSq y

theorem shortest_iff_norm32 (x : Vec) : IsShortest x ↔ InLeech x ∧ normSq x = 32 := by
  constructor
  · rintro ⟨hx, h0, hmin⟩
    refine ⟨hx, le_antisymm ?_ (leech_norm_ge_32 x hx h0)⟩
    obtain ⟨y, hy, hy0, hy32⟩ := leech_min_norm.1
    have h := hmin y hy hy0
    simpa only [normSq, hy32] using h
  · rintro ⟨hx, hn⟩
    refine ⟨hx, ?_, ?_⟩
    · intro h0
      subst x
      simp [normSq] at hn
    · intro y hy hy0
      rw [hn]
      exact leech_norm_ge_32 y hy hy0

abbrev ShortestVectors := {x : Vec // IsShortest x}

noncomputable def shortestEquiv : ShortestVectors ≃ MinimalVectors :=
  Equiv.subtypeEquivRight shortest_iff_norm32

noncomputable instance : Fintype ShortestVectors := Fintype.ofEquiv MinimalVectors shortestEquiv.symm

/-- There are 196,560 shortest nonzero vectors in the lattice already defined in Lean. -/
theorem card_shortest_vectors : Fintype.card ShortestVectors = 196560 := by
  rw [Fintype.card_congr shortestEquiv, leech_kissing_number]

end LeechMinimal
