import ConwayTally

/-! # Orthogonal neighbors of a shortest Leech vector

Count signed coordinate equalities by coordinate pair and by shortest-vector family.
-/

namespace ConwayIncidence

open GolayMathieu ConwayMoves LeechMinimal LeechSymmetry LeechLattice

abbrev Neighbors := {x : MinimalVectors // x.val 0 = x.val 1}
noncomputable instance : Fintype Neighbors := Fintype.ofFinite _

private theorem count_equiv {A B : Type} [Fintype A] [Fintype B] (P : A → Prop)
    [DecidablePred P] (e : Subtype P ≃ B) :
    (∑ x : A, if P x then 1 else 0) = Fintype.card B := by
  rw [Finset.sum_boole, ← Fintype.card_subtype P, Fintype.card_congr e]; rfl

theorem column (i j : Point) (b : Bool) :
    (∑ x : MinimalVectors, score x.val i j b) = if j = i then 0 else Fintype.card Neighbors := by
  by_cases h : j = i
  · subst j; simp [score]
  · simp only [h,ite_false]
    obtain ⟨g,hg⟩ := move_indices i j h b
    let P := fun x : MinimalVectors => x.val i = twoSign b (x.val j)
    have e : Subtype P ≃ Neighbors := Equiv.subtypeEquiv (onShortest g) (fun x => by
      obtain ⟨h0,h1⟩ := hg ⟨x.val,x.property.1⟩
      change (x.val i = twoSign b (x.val j)) ↔
        (g ⟨x.val,x.property.1⟩).val 0 = (g ⟨x.val,x.property.1⟩).val 1
      rw [h0,h1])
    calc
      _ = ∑ x, if P x then 1 else 0 := Finset.sum_congr rfl fun x _ => by
        simp [score,h,P]
      _ = _ := count_equiv P e

private theorem switch_sums {A I J B : Type} [Fintype A] [Fintype I] [Fintype J] [Fintype B]
    (f : A → I → J → B → Nat) :
    (∑ a, ∑ i, ∑ j, ∑ b, f a i j b) = ∑ i, ∑ j, ∑ b, ∑ a, f a i j b := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]

theorem column_total : (∑ x : MinimalVectors, tally x.val) = 1104 * Fintype.card Neighbors := by
  rw [show (∑ x : MinimalVectors, tally x.val) = _ from
    switch_sums (fun (x : MinimalVectors) i j b => score x.val i j b)]
  let c := Fintype.card Neighbors
  have h (i j : Point) (b : Bool) : (∑ x : MinimalVectors, score x.val i j b) =
      (if j=i then 0 else 1) * c := by
    rw [column]; by_cases he : j = i <;> simp only [he,ite_true,ite_false,zero_mul,one_mul,c]
  simp_rw [h, ← Finset.sum_mul]
  have cc : (∑ i : Point, ∑ j : Point, ∑ _ : Bool, if j=i then 0 else (1 : ℕ)) = 1104 := by decide +kernel
  rw [cc]

private theorem sum_three {A B C X : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype X]
    (e : A ⊕ (B ⊕ C) ≃ X) (f : X → Nat) (a b c : Nat)
    (ha : ∀ x, f (e (.inl x)) = a) (hb : ∀ x, f (e (.inr (.inl x))) = b)
    (hc : ∀ x, f (e (.inr (.inr x))) = c) :
    (∑ x, f x) = Fintype.card A*a + Fintype.card B*b + Fintype.card C*c := by
  rw [← e.sum_comp f, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp_rw [ha,hb,hc]; simp [Nat.add_assoc]

theorem row_total : (∑ x : MinimalVectors, tally x.val) = 1104*926 + 97152*536 + 98304*506 := by
  have h4 (x : FourVectors) : tally x.val = 926 := by
    rw [tally_even _ 4 (by decide) x.property.1, x.property.2]
  have h8 (x : OctadVectors) : tally x.val = 536 := by
    rw [tally_even _ 2 (by decide) x.property.1, x.property.2.2.1]
  exact (sum_three minimalEquiv (fun x => tally x.val) 926 536 506 h4 h8
    (fun x => tally_odd x.property)).trans (by rw [card_four,card_octad_vectors,card_odd])

/-- There are 93,150 shortest vectors whose first two coordinates agree. -/
theorem card_neighbors : Fintype.card Neighbors = 93150 := by
  have h := column_total.symm.trans row_total
  omega

end ConwayIncidence
