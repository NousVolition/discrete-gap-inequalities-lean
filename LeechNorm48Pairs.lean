import LeechNorm48
import LeechOppositePairs

/-! # Opposite pairs at squared length 48 in the Leech lattice -/

namespace LeechNorm48

open LeechMinimal LeechSymmetry

/-- A lattice vector `v` of squared length 48 and its negative form the unordered pair `{v, -v}`. -/
def IsOppositePair (s : Finset Lattice) : Prop :=
  LeechOppositePairs.IsOppositePair 48 s

/-- Each vector on this shell belongs to one opposite pair. -/
theorem existsUnique_opposite_pair (x : Lattice) (hx : normSq x.val = 48) :
    ∃! s : Finset Lattice, IsOppositePair s ∧ x ∈ s :=
  LeechOppositePairs.existsUnique_opposite_pair x hx

/-- Each pair has two vectors. Only zero is its own negative. -/
theorem card_members_of_opposite_pair {s : Finset Lattice} (hs : IsOppositePair s) :
    s.card = 2 :=
  LeechOppositePairs.card_members_of_opposite_pair (by decide : (0 : ℤ) < 48) hs

/-- Count the unordered sets `{v, -v}` on the squared-length-48 shell. -/
theorem card_norm48_opposite_pairs :
    Nat.card {s : Finset Lattice // IsOppositePair s} = 8386560 := by
  change Nat.card {s : Finset Lattice // LeechOppositePairs.IsOppositePair 48 s} = _
  rw [LeechOppositePairs.card_opposite_pairs (by decide : (0 : ℤ) < 48), card_norm48_vectors]

end LeechNorm48
