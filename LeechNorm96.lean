import LeechNorm80
import LeechNorm64Layers

/-! # Leech lattice vectors of squared length 96

The Golay coordinate count covers entries from −8 to 7. A vector outside that
box has a +8 entry. Subtracting 8 there leaves a shortest vector with a zero
in that position. -/
namespace LeechNorm96

open LeechLattice LeechMinimal LeechCodeCounts LeechSymmetry ConwayPairs Finset

private abbrev Shell := {x : Lattice // normSq x.val = 96}
private def withinBox (x : Shell) := ∀ i, -8 ≤ x.val.val i ∧ x.val.val i ≤ 7

private theorem weight_zero : Fintype.card {w : Codeword // weight w.val = 0} = 1 := by
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨⟨fun _ => false, isGolayWord_false⟩, by simp [weight]⟩, ?_⟩
  intro w
  apply Subtype.ext
  apply Subtype.ext
  funext i
  have empty := Finset.card_eq_zero.mp w.property
  change (univ.filter fun j => w.val.val j = true) = ∅ at empty
  cases h : w.val.val i with
  | false => rfl
  | true =>
    have hi : i ∈ univ.filter (fun j => w.val.val j = true) := mem_filter.mpr ⟨mem_univ _, h⟩
    simp [empty] at hi

private theorem weight_full : Fintype.card {w : Codeword // weight w.val = 24} = 1 := by
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨⟨fun _ => true, isGolayWord_true⟩, by simp [weight]⟩, ?_⟩
  intro w
  apply Subtype.ext
  apply Subtype.ext
  funext i
  have full : (univ.filter fun j => w.val.val j = true) = univ :=
    eq_of_subset_of_card_le (filter_subset _ _) (by
      simpa [weight] using w.property.ge)
  have hi : i ∈ univ.filter (fun j => w.val.val j = true) := by rw [full]; exact mem_univ i
  exact (mem_filter.mp hi).2

private def perWord (p : Bool) (k : ℕ) : ℕ :=
  if p then 4200352 else if k = 0 then 8638432 else if k = 8 then 4224512
  else if k = 24 then 8388608 else 4194304

-- Sum the per-word counts using only the number of words of each weight.
private theorem sum_words {α : Type} [Fintype α] (wgt : α → ℕ)
    (allWords : Fintype.card α = 4096)
    (zero : Fintype.card {w // wgt w = 0} = 1)
    (octads : Nat.card {w // wgt w = 8} = 759)
    (full : Fintype.card {w // wgt w = 24} = 1) :
    (∑ p : Bool, ∑ w : α, perWord p (wgt w)) = 34416077280 := by
  have eight : Fintype.card {w // wgt w = 8} = 759 := Nat.card_eq_fintype_card.symm.trans octads
  have term (k : ℕ) : perWord false k =
      4194304 + (if k = 0 then 1 else 0) * 4444128 +
      (if k = 8 then 1 else 0) * 30208 +
      (if k = 24 then 1 else 0) * 4194304 := by
    simp only [perWord, Bool.false_eq_true, ite_false]
    split_ifs <;> omega
  have odd (k : ℕ) : perWord true k = 4200352 := rfl
  rw [Fintype.sum_bool]
  simp only [odd, term, sum_add_distrib, ← sum_mul, sum_boole, sum_const, card_univ,
    nsmul_eq_mul, Nat.cast_id]
  rw [← Fintype.card_subtype (fun w : α => wgt w = 0),
    ← Fintype.card_subtype (fun w : α => wgt w = 8),
    ← Fintype.card_subtype (fun w : α => wgt w = 24), zero, eight, full, allWords]
  decide

private theorem card_box : Nat.card {x : Shell // withinBox x} = 34416077280 := by
  apply (LeechShellCoordinates.card_box_from_choices 12).trans
  have octads : Nat.card Octad = 759 := Nat.card_eq_fintype_card.trans card_octad
  refine Eq.trans ?_ (sum_words (fun w : Codeword => weight w.val) card_codeword weight_zero octads weight_full)
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro w _
  exact LeechNorm80Count.choices96 p (LeechNorm80.word_weights w)

private theorem coord_upper (x : Shell) (i : Fin 24) : x.val.val i ≤ 8 := by
  have nz : x.val.val - axis i ≠ 0 := by
    intro h
    have he := (congrArg normSq (sub_eq_zero.mp h))
    rw [x.property, axis_norm] at he
    omega
  have h := leech_norm_ge_32 _ (leechLattice.sub_mem x.val.property (axis_mem i)) nz
  change 32 ≤ normSq (x.val.val - axis i) at h
  rw [normSq_sub, x.property, axis_norm, dot_axis] at h
  omega

private abbrev WithEight := {x : Shell // ∃ i, x.val.val i = 8}
private abbrev ZeroAt (i : Fin 24) := {v : MinimalVectors // v.val i = 0}

private theorem outside_iff (x : Shell) : ¬ withinBox x ↔ ∃ i, x.val.val i = 8 := by
  have lower (i : Fin 24) : -8 ≤ x.val.val i := by
    have h := coord_upper ⟨-x.val, (normSq_neg x.val.val).trans x.property⟩ i
    change -(x.val.val i) ≤ 8 at h
    omega
  constructor
  · intro h
    by_contra! absent
    exact h (fun i => ⟨lower i, by have := coord_upper x i; have := absent i; omega⟩)
  · rintro ⟨i, hi⟩ h
    have := (h i).2
    omega

private def addEight : (Σ i, ZeroAt i) → WithEight
  | ⟨i,u⟩ => ⟨⟨⟨u.val.val + axis i, leechLattice.add_mem u.val.property.1 (axis_mem i)⟩,
      by rw [normSq_add, u.val.property.2, axis_norm, dot_axis, u.property]; decide⟩,
    i, by simp [axis, u.property]⟩

private theorem addEight_bijective : Function.Bijective addEight := by
  constructor
  · rintro ⟨i,u⟩ ⟨j,v⟩ h
    have he : u.val.val + axis i = v.val.val + axis j := congrArg (fun x : WithEight => x.val.val.val) h
    have hij : i = j := by
      by_contra ne
      have hi := congrFun he i
      simp [axis, ne, u.property] at hi
      have hb := (abs_le.mp (coord_bound v.val i)).2
      omega
    subst j
    apply congrArg (Sigma.mk i)
    exact Subtype.ext (Subtype.ext (add_right_cancel he))
  · rintro ⟨x,i,hi⟩
    let u : MinimalVectors := ⟨x.val.val - axis i,
      leechLattice.sub_mem x.val.property (axis_mem i), by rw [normSq_sub, x.property, axis_norm, dot_axis, hi]; decide⟩
    have hz : u.val i = 0 := by simp [u, axis, hi]
    exact ⟨⟨i,u,hz⟩, Subtype.ext (Subtype.ext (Subtype.ext (sub_add_cancel _ _)))⟩

private theorem card_with_eight : Nat.card WithEight = 1578720 := by
  classical
  rw [← Nat.card_congr (Equiv.ofBijective addEight addEight_bijective),
    Nat.card_eq_fintype_card, Fintype.card_sigma]
  have hc (i : Fin 24) : Fintype.card (ZeroAt i) = 65780 :=
    Nat.card_eq_fintype_card.symm.trans (LeechLayers.card_shortest_zero_coordinate i)
  simp [hc]

/-- There are 34,417,656,000 lattice vectors of squared length 96. -/
theorem card_norm96_vectors : Nat.card {x : Lattice // normSq x.val = 96} = 34417656000 := by
  classical
  let e := Equiv.subtypeEquivRight outside_iff
  have hc : Nat.card {x : Shell // ¬ withinBox x} = 1578720 :=
    (Nat.card_congr e).trans card_with_eight
  have : Finite {x : Shell // withinBox x} := (Nat.card_pos_iff.mp (by rw [card_box]; decide)).2
  have : Finite {x : Shell // ¬ withinBox x} := (Nat.card_pos_iff.mp (by rw [hc]; decide)).2
  change Nat.card Shell = _
  rw [← Nat.card_congr (Equiv.sumCompl withinBox), Nat.card_sum, card_box, hc]

end LeechNorm96
