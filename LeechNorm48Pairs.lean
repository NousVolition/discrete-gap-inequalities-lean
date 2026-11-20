import LeechNorm48

/-! # Opposite pairs at squared length 48 in the Leech lattice -/

namespace LeechNorm48

open LeechMinimal LeechSymmetry

/-- A lattice vector `v` of squared length 48 and its negative form the unordered pair `{v, -v}`. -/
def IsOppositePair (s : Finset Lattice) : Prop :=
  ∃ v : Lattice, normSq v.val = 48 ∧ s = {v, -v}

private theorem pair_of_member {s : Finset Lattice} (hs : IsOppositePair s)
    {x : Lattice} (hx : x ∈ s) : normSq x.val = 48 ∧ s = {x, -x} := by
  obtain ⟨v, hv, rfl⟩ := hs
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact ⟨hv, rfl⟩
  · obtain rfl := Finset.mem_singleton.mp hx
    exact ⟨(normSq_neg v.val).trans hv, by rw [neg_neg, Finset.pair_comm]⟩

/-- Each vector on this shell belongs to one opposite pair. -/
theorem existsUnique_opposite_pair (x : Lattice) (hx : normSq x.val = 48) :
    ∃! s : Finset Lattice, IsOppositePair s ∧ x ∈ s := by
  refine ⟨{x, -x}, ⟨⟨x, hx, rfl⟩, Finset.mem_insert_self _ _⟩, ?_⟩
  intro s hs
  exact (pair_of_member hs.1 hs.2).2

/-- Each pair has two vectors. Only zero is its own negative. -/
theorem card_members_of_opposite_pair {s : Finset Lattice} (hs : IsOppositePair s) :
    s.card = 2 := by
  obtain ⟨v, hv, rfl⟩ := hs
  apply Finset.card_pair
  intro heq
  have hz (i : Fin 24) : v.val i = 0 := by
    have hi := congrArg (fun x : Lattice => x.val i) heq
    change v.val i = -(v.val i) at hi
    omega
  simp [normSq, hz] at hv

/-- Count the unordered sets `{v, -v}` on the squared-length-48 shell. -/
theorem card_norm48_opposite_pairs :
    Nat.card {s : Finset Lattice // IsOppositePair s} = 8386560 := by
  let Pair := {s : Finset Lattice // IsOppositePair s}
  let forget : (Σ s : Pair, ↥s.val) → {x : Lattice // normSq x.val = 48} :=
    fun ⟨s, x⟩ => ⟨x.val, (pair_of_member s.property x.property).1⟩
  have bij : Function.Bijective forget := by
    constructor
    · rintro ⟨s, x⟩ ⟨t, y⟩ h
      have hxy : x.val = y.val := congrArg Subtype.val h
      have hu := existsUnique_opposite_pair x.val (pair_of_member s.property x.property).1
      have hst : s = t := Subtype.ext
        (hu.unique ⟨s.property, x.property⟩ ⟨t.property, hxy ▸ y.property⟩)
      subst t
      exact congrArg (Sigma.mk s) (Subtype.ext hxy)
    · intro x
      obtain ⟨s, ⟨hs, hx⟩, _⟩ := existsUnique_opposite_pair x.val x.property
      exact ⟨⟨⟨s, hs⟩, x.val, hx⟩, Subtype.ext rfl⟩
  let positions : (Σ s : Pair, ↥s.val) ≃ Pair × Fin 2 :=
    Equiv.sigmaEquivProdOfEquiv fun s : Pair =>
      Finset.equivFinOfCardEq (card_members_of_opposite_pair s.property)
  have h := Nat.card_congr ((Equiv.ofBijective forget bij).symm.trans positions)
  rw [card_norm48_vectors, Nat.card_prod, Nat.card_fin] at h
  change Nat.card Pair = 8386560
  omega

end LeechNorm48
