import LeechSymmetry

/-! # Pairing Leech lattice vectors with their negatives -/

namespace LeechOppositePairs

open LeechMinimal LeechSymmetry

/-- A vector of squared length `n` and its negative form the unordered pair `{v, -v}`. -/
def IsOppositePair (n : ℤ) (s : Finset Lattice) : Prop :=
  ∃ v : Lattice, normSq v.val = n ∧ s = {v, -v}

private theorem pair_of_member {n : ℤ} {s : Finset Lattice} (hs : IsOppositePair n s)
    {x : Lattice} (hx : x ∈ s) : normSq x.val = n ∧ s = {x, -x} := by
  obtain ⟨v, hv, rfl⟩ := hs
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact ⟨hv, rfl⟩
  · obtain rfl := Finset.mem_singleton.mp hx
    exact ⟨(normSq_neg v.val).trans hv, by rw [neg_neg, Finset.pair_comm]⟩

/-- Each vector belongs to one opposite pair at its squared length. -/
theorem existsUnique_opposite_pair {n : ℤ} (x : Lattice) (hx : normSq x.val = n) :
    ∃! s : Finset Lattice, IsOppositePair n s ∧ x ∈ s := by
  refine ⟨{x, -x}, ⟨⟨x, hx, rfl⟩, Finset.mem_insert_self _ _⟩, ?_⟩
  intro s hs
  exact (pair_of_member hs.1 hs.2).2

/-- At positive squared length, each pair has two vectors. Only zero is its own negative. -/
theorem card_members_of_opposite_pair {n : ℤ} (hn : 0 < n) {s : Finset Lattice}
    (hs : IsOppositePair n s) : s.card = 2 := by
  obtain ⟨v, hv, rfl⟩ := hs
  apply Finset.card_pair
  intro heq
  have hz (i : Fin 24) : v.val i = 0 := by
    have hi := congrArg (fun x : Lattice => x.val i) heq
    change v.val i = -(v.val i) at hi
    omega
  simp [normSq, hz] at hv
  omega

/-- At positive squared length, counting a vector and its negative together halves the count. -/
theorem card_opposite_pairs {n : ℤ} (hn : 0 < n) :
    Nat.card {s : Finset Lattice // IsOppositePair n s} =
      Nat.card {x : Lattice // normSq x.val = n} / 2 := by
  let Pair := {s : Finset Lattice // IsOppositePair n s}
  let forget : (Σ s : Pair, ↥s.val) → {x : Lattice // normSq x.val = n} :=
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
      Finset.equivFinOfCardEq (card_members_of_opposite_pair hn s.property)
  have h := Nat.card_congr ((Equiv.ofBijective forget bij).symm.trans positions)
  rw [Nat.card_prod, Nat.card_fin] at h
  change Nat.card Pair = _
  omega

end LeechOppositePairs
