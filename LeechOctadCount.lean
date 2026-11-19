import LeechCodeCounts

/-! The computed weight-eight message count counts distinct Golay octads. -/
namespace LeechCodeCounts

open LeechLattice GolayMatrixDistance Finset

private theorem countP_as_sum {α : Type*} (p : α → Bool) (l : List α) :
    l.countP p = (l.map (fun a => if p a then 1 else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => cases hp : p a <;> simp [hp, ih, Nat.add_comm]

private theorem list_range_sum (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i := by
  rw [Fin.sum_univ_eq_sum_range]
  have hr : (List.range n).toFinset = Finset.range n := by ext i; simp
  simpa only [hr] using (List.sum_toFinset f (List.nodup_range (n := n))).symm

theorem weightCounts_eight_sum : weightCounts.2.1 =
    ∑ b : Fin 16, ∑ k : Fin 256,
      if popcount24 (encodeNat (b.val * 256 + k.val)) = 8 then 1 else 0 := by
  rw [weightCounts_eight, list_range_sum]
  apply sum_congr rfl
  intro b _
  rw [countP_as_sum, list_range_sum]
  simp

noncomputable def octadMessageEquiv :
    {m : Fin 4096 // popcount24 (encodeNat m.val) = 8} ≃ Octad :=
  Equiv.subtypeEquiv codeEquiv (fun m => by
    change popcount24 (encodeNat m.val) = 8 ↔ weight (word (encodeNat m.val)) = 8
    rw [weight, ← popcount24_eq_card])

theorem card_octad_eq_weightCounts : Fintype.card Octad = weightCounts.2.1 := by
  classical
  rw [← Fintype.card_congr octadMessageEquiv, Fintype.card_subtype]
  have hc : (univ.filter (fun m : Fin 4096 => popcount24 (encodeNat m.val) = 8)).card =
      ∑ m : Fin 4096, if popcount24 (encodeNat m.val) = 8 then 1 else 0 :=
    natCast_card_filter (R := ℕ) _ _
  rw [hc, weightCounts_eight_sum]
  rw [← Fintype.sum_prod_type']
  symm
  apply Fintype.sum_equiv (finProdFinEquiv : Fin 16 × Fin 256 ≃ Fin 4096)
  intro p
  simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

theorem card_octad : Fintype.card Octad = 759 := by
  rw [card_octad_eq_weightCounts, golay_weight_distribution]

end LeechCodeCounts
