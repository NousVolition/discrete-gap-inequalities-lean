import ConwayNeighborCount
import ConwayPairs
import ConwayStabilizer

/-! # The order of the full origin-fixing Leech symmetry group

The group acts transitively on ordered orthogonal pairs of shortest vectors.
Their sum and difference determine the two axes fixed by the pair stabilizer.
-/

namespace ConwayOrder

open GolayMathieu LeechSymmetry LeechLattice LeechMinimal ConwayIncidence ConwayPairs ConwayStabilizer

theorem card_partner (v : MinimalVectors) : Nat.card (Partner v) = 93150 := by
  obtain ⟨g,rfl⟩ := shortest_transitive v
  have e : Partner (root true) ≃ Neighbors :=
    Equiv.subtypeEquivRight fun x => by rw [root_dot]; omega
  exact (Nat.card_congr (partnerTransport g (root true)).symm).trans
    ((Nat.card_congr e).trans (Nat.card_eq_fintype_card.trans card_neighbors))

theorem card_pairs : Nat.card Pair = 196560 * 93150 := by
  classical
  rw [Nat.card_congr pairEquiv,Nat.card_sigma]
  simp_rw [card_partner]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,leech_kissing_number]; rfl

/-- The full group of distance-preserving bijections fixing the origin has this order. -/
theorem card_aut : Nat.card LeechSymmetry.Aut = 8315553613086720000 := by
  have ho : MulAction.orbit Aut basePair = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr; exact pair_transitive
  have orbitCard : Nat.card (MulAction.orbit Aut basePair) = Nat.card Pair := by
    rw [ho]; exact Nat.card_congr (Equiv.Set.univ _)
  have stab : MulAction.stabilizer Aut basePair ≃ FixAxes :=
    Equiv.subtypeEquivRight fun g => fixes_pair_iff g
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Aut basePair),
    Nat.card_prod,orbitCard,card_pairs,Nat.card_congr stab,card_fix_axes]

end ConwayOrder
