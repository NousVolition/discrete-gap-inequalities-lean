import ConwayOrder
import PlaygroundLeech

/-! # Layers perpendicular to a shortest vector in playground coordinates -/
namespace LeechLayers

open PlaygroundGolay PlaygroundLeech LeechLattice LeechMinimal LeechSymmetry

private theorem dot_toLean (s v : Vec) : dot (toLean s) (toLean v) = dot s v := by
  apply Fintype.sum_equiv coordinateEquiv.symm
  intro i
  rfl

private def toMinimal : PlayShortestVectors ≃ MinimalVectors :=
  Equiv.subtypeEquiv vectorEquiv (fun x => (shortest_correspondence x).trans (shortest_iff_norm32 _))

/-- Any shortest vector in the playground coordinates has 93,150 perpendicular shortest vectors. -/
theorem card_perpendicular (s : PlayShortestVectors) :
    Nat.card {v : PlayShortestVectors // dot s.val v.val = 0} = 93150 := by
  let e : {v : PlayShortestVectors // dot s.val v.val = 0} ≃ ConwayPairs.Partner (toMinimal s) :=
    Equiv.subtypeEquiv toMinimal (fun v => by
      change dot s.val v.val = 0 ↔ dot (toLean s.val) (toLean v.val) = 0
      rw [dot_toLean])
  exact (Nat.card_congr e).trans (ConwayOrder.card_partner _)

/-- A dot product of 24 or −24 would give a nonzero difference or sum of squared length 16. -/
theorem no_dot_twenty_four (s v : PlayShortestVectors) :
    dot s.val v.val ≠ 24 ∧ dot s.val v.val ≠ -24 := by
  obtain ⟨hs, ns⟩ := (play_shortest_iff_norm32 _).mp s.property
  obtain ⟨hv, nv⟩ := (play_shortest_iff_norm32 _).mp v.property
  have exclude (x : Vec) (hm : InPlayLeech x) (hn : normSq x = 16) : False := by
    have nz : x ≠ 0 := by intro h; simp [h, normSq] at hn
    have := play_norm_ge_32 x hm nz
    omega
  have sm := (lattice_correspondence _).mp hs
  have vm := (lattice_correspondence _).mp hv
  constructor
  · intro h
    apply exclude (s.val - v.val) ((lattice_correspondence _).mpr (leechLattice.sub_mem sm vm))
    rw [normSq_sub, ns, nv, h]
    decide
  · intro h
    apply exclude (s.val + v.val) ((lattice_correspondence _).mpr (leechLattice.add_mem sm vm))
    rw [normSq_add, ns, nv, h]
    decide

open ConwayIncidence ConwayPairs GolayMathieu Finset

-- For the reference vector (4, −4, 0, …), the dot product is four times this difference.
private def diff (x : MinimalVectors) : ℤ := x.val 0 - x.val 1

private theorem levels (x : MinimalVectors) :
    diff x ∈ ({0, 2, -2, 4, -4, 8, -8} : Finset ℤ) := by
  rcases (minimal_iff x.val).mp x.property with h | h | ⟨w, _, j, hx⟩
  · rcases h.1 0 with h0|h0|h0 <;> rcases h.1 1 with h1|h1|h1 <;>
      rw [diff, h0, h1] <;> decide
  · rcases h.1 0 with h0|h0|h0 <;> rcases h.1 1 with h1|h1|h1 <;>
      rw [diff, h0, h1] <;> decide
  · rw [diff, hx]
    by_cases h0 : (0 : Point) = j
    · subst j; cases hw : w 0 <;> cases hw' : w 1 <;> norm_num [oddVector, hw, hw']
    by_cases h1 : (1 : Point) = j
    · subst j; cases hw : w 0 <;> cases hw' : w 1 <;> norm_num [oddVector, hw, hw']
    · cases hw : w 0 <;> cases hw' : w 1 <;> norm_num [oddVector, h0, h1, hw, hw']

private noncomputable def squareSum (i : Point) : ℤ := ∑ x : MinimalVectors, x.val i ^ 2

private theorem same_squareSum (i : Point) : squareSum i = squareSum 0 := by
  obtain ⟨j, hj⟩ := exists_ne i
  obtain ⟨g, hg⟩ := move_indices i j hj false
  let f := fun x : MinimalVectors => x.val 0 ^ 2
  calc
    squareSum i = ∑ x : MinimalVectors, f (onShortest g x) := by
      apply sum_congr rfl
      intro x _
      change x.val i ^ 2 = (g (asL x)).val 0 ^ 2
      rw [(hg (asL x)).1]
      rfl
    _ = squareSum 0 := Equiv.sum_comp (onShortest g) f

private theorem squareSum_zero : squareSum 0 = 262080 := by
  have total : (∑ i : Point, squareSum i) = 196560 * 32 := by
    unfold squareSum
    rw [sum_comm]
    have hn (x : MinimalVectors) : (∑ i : Point, x.val i ^ 2) = 32 := x.property.2
    simp [hn, leech_kissing_number]
  have all_eq : (∑ i : Point, squareSum i) = 24 * squareSum 0 := by
    calc
      _ = ∑ _ : Point, squareSum 0 := sum_congr rfl (fun i _ => same_squareSum i)
      _ = _ := by simp
  omega

private theorem cross_sum_zero : (∑ x : MinimalVectors, x.val 0 * x.val 1) = 0 := by
  obtain ⟨g, hg⟩ := move_indices 0 1 (by decide) true
  let f := fun x : MinimalVectors => x.val 0 * x.val 1
  have sign (x : MinimalVectors) : f (onShortest g x) = -f x := by
    change (g (asL x)).val 0 * (g (asL x)).val 1 = -(x.val 0 * x.val 1)
    rw [(hg (asL x)).1, (hg (asL x)).2]
    simp [twoSign, asL]
  have h := Equiv.sum_comp (onShortest g) f
  simp only [sign, sum_neg_distrib] at h
  change (∑ x, f x) = 0
  omega

-- The sum of (x₀ − x₁)² over the shortest vectors.
private theorem diff_square_sum : (∑ x : MinimalVectors, diff x ^ 2) = 524160 := by
  have expand (x : MinimalVectors) :
      diff x ^ 2 = x.val 0 ^ 2 + x.val 1 ^ 2 - 2 * (x.val 0 * x.val 1) := by
    unfold diff
    ring
  simp only [expand, sum_sub_distrib, sum_add_distrib, ← mul_sum, cross_sum_zero, mul_zero, sub_zero]
  change squareSum 0 + squareSum 1 = _
  rw [same_squareSum 1, squareSum_zero]
  norm_num

private noncomputable def count (k : ℤ) : ℤ :=
  ∑ x : MinimalVectors, if diff x = k then 1 else 0

private theorem count_card (k : ℤ) :
    count k = (Nat.card {x : MinimalVectors // diff x = k} : ℤ) := by
  classical
  unfold count
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, sum_boole]


private theorem count_neg (k : ℤ) : count (-k) = count k := by
  let e := onShortest centralNegation
  have opposite (x : MinimalVectors) : diff (e x) = -(diff x) := by
    change -x.val 0 - (-x.val 1) = -(x.val 0 - x.val 1)
    ring
  let f := fun x : MinimalVectors => if diff x = -k then (1 : ℤ) else 0
  calc
    count (-k) = ∑ x : MinimalVectors, f (e x) := (Equiv.sum_comp e f).symm
    _ = count k := by
      change (∑ x : MinimalVectors, if diff (e x) = -k then (1 : ℤ) else 0) =
        ∑ x : MinimalVectors, if diff x = k then (1 : ℤ) else 0
      simp only [opposite, neg_inj]

private theorem count_zero : count 0 = 93150 := by
  let e : {x : MinimalVectors // diff x = 0} ≃ Neighbors :=
    Equiv.subtypeEquivRight fun x => by simp [diff, sub_eq_zero]
  rw [count_card, Nat.card_congr e, Nat.card_eq_fintype_card, card_neighbors]
  rfl

private theorem count_eight : count 8 = 1 := by
  classical
  have h : Fintype.card {x : MinimalVectors // diff x = 8} = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨⟨root true, rfl⟩, ?_⟩
    rintro ⟨x, hx⟩
    apply Subtype.ext
    change x = root true
    have h0 := abs_le.mp (coord_bound x 0)
    have h1 := abs_le.mp (coord_bound x 1)
    change x.val 0 - x.val 1 = 8 at hx
    apply root_unique x true (by omega)
    change x.val 1 = -4
    omega
  rw [count_card, Nat.card_eq_fintype_card, h]
  rfl

private theorem sum_by_layer (f : ℤ → ℤ) :
    (∑ x : MinimalVectors, f (diff x)) =
      ∑ k ∈ ({0, 2, -2, 4, -4, 8, -8} : Finset ℤ), f k * count k := by
  let ks : Finset ℤ := {0, 2, -2, 4, -4, 8, -8}
  calc
    _ = ∑ x : MinimalVectors, ∑ k ∈ ks, if diff x = k then f k else 0 := by
      apply sum_congr rfl
      intro x _
      simp [show diff x ∈ ks from levels x]
    _ = ∑ k ∈ ks, ∑ x : MinimalVectors, if diff x = k then f k else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro k _
      rw [count, mul_sum]
      apply sum_congr rfl
      intro x _
      by_cases h : diff x = k <;> simp [h]

private theorem counts : count 2 = 47104 ∧ count 4 = 4600 := by
  have total := sum_by_layer (fun _ => 1)
  have squares := sum_by_layer (fun k => k ^ 2)
  norm_num [sum_insert, leech_kissing_number, diff_square_sum, count_neg, count_zero, count_eight] at total squares
  constructor <;> omega

private theorem play_count (s : PlayShortestVectors) (k : ℤ) :
    (Nat.card {v : PlayShortestVectors // dot s.val v.val = 4 * k} : ℤ) = count k := by
  obtain ⟨g, hg⟩ := shortest_transitive (toMinimal s)
  let e := (onShortest g).trans toMinimal.symm
  let layer : {x : MinimalVectors // diff x = k} ≃
      {v : PlayShortestVectors // dot s.val v.val = 4 * k} :=
    Equiv.subtypeEquiv e fun x => by
      have hd := dot_toLean s.val (e x).val
      change dot (toMinimal s).val (toMinimal (e x)).val = _ at hd
      have he : toMinimal (e x) = onShortest g x := toMinimal.apply_symm_apply _
      rw [← hd, he, ← hg]
      change diff x = k ↔ dot (g (asL (root true))).val (g (asL x)).val = 4 * k
      rw [map_dot]
      change diff x = k ↔ dot (root true).val x.val = 4 * k
      rw [root_dot]
      unfold diff
      omega
  rw [count_card, Nat.card_congr layer]

/-- For any shortest vector s, 47,104 shortest vectors have dot product +8 with s. -/
theorem card_dot_pos_eight (s : PlayShortestVectors) :
    Nat.card {v : PlayShortestVectors // dot s.val v.val = 8} = 47104 := by
  exact_mod_cast (play_count s 2).trans counts.1

/-- For any shortest vector s, 47,104 shortest vectors have dot product −8 with s. -/
theorem card_dot_neg_eight (s : PlayShortestVectors) :
    Nat.card {v : PlayShortestVectors // dot s.val v.val = -8} = 47104 := by
  exact_mod_cast (play_count s (-2)).trans ((count_neg 2).trans counts.1)

/-- For any shortest vector s, 4,600 shortest vectors have dot product +16 with s. -/
theorem card_dot_pos_sixteen (s : PlayShortestVectors) :
    Nat.card {v : PlayShortestVectors // dot s.val v.val = 16} = 4600 := by
  exact_mod_cast (play_count s 4).trans counts.2

/-- For any shortest vector s, 4,600 shortest vectors have dot product −16 with s. -/
theorem card_dot_neg_sixteen (s : PlayShortestVectors) :
    Nat.card {v : PlayShortestVectors // dot s.val v.val = -16} = 4600 := by
  exact_mod_cast (play_count s (-4)).trans ((count_neg 4).trans counts.2)

private theorem eq_zero_of_normSq_zero (v : Vec) (h : normSq v = 0) : v = 0 := by
  funext i
  have hi := single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg (v j)) (mem_univ i)
  change v i ^ 2 ≤ normSq v at hi
  rw [h] at hi
  exact sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _))

/-- The +32 layer contains only the chosen shortest vector. -/
theorem pos_thirty_two_layer_iff (s : PlayShortestVectors) (v : Vec) :
    IsPlayShortest v ∧ dot s.val v = 32 ↔ v = s.val := by
  have ns := ((play_shortest_iff_norm32 _).mp s.property).2
  constructor
  · rintro ⟨hv, hd⟩
    have nv := ((play_shortest_iff_norm32 _).mp hv).2
    have hz : s.val - v = 0 := eq_zero_of_normSq_zero _ (by
      rw [normSq_sub, ns, nv, hd]; decide)
    exact (sub_eq_zero.mp hz).symm
  · rintro rfl
    exact ⟨s.property, by simpa only [dot, normSq, pow_two] using ns⟩

/-- The −32 layer contains only the negative of the chosen shortest vector. -/
theorem neg_thirty_two_layer_iff (s : PlayShortestVectors) (v : Vec) :
    IsPlayShortest v ∧ dot s.val v = -32 ↔ v = -s.val := by
  obtain ⟨hs, ns⟩ := (play_shortest_iff_norm32 _).mp s.property
  constructor
  · rintro ⟨hv, hd⟩
    have nv := ((play_shortest_iff_norm32 _).mp hv).2
    have hz : s.val + v = 0 := eq_zero_of_normSq_zero _ (by
      rw [normSq_add, ns, nv, hd]; decide)
    rw [add_comm] at hz
    exact add_eq_zero_iff_eq_neg.mp hz
  · rintro rfl
    have hn : InPlayLeech (-s.val) := (lattice_correspondence _).mpr
      (leechLattice.neg_mem ((lattice_correspondence _).mp hs))
    refine ⟨(play_shortest_iff_norm32 _).mpr ⟨hn, (normSq_neg _).trans ns⟩, ?_⟩
    simpa [dot, normSq, pow_two] using congrArg Neg.neg ns

private theorem card_layer_of_singleton (s : PlayShortestVectors) (k : ℤ) (w : Vec)
    (hw : ∀ v : Vec, IsPlayShortest v ∧ dot s.val v = k ↔ v = w) :
    Nat.card {v : PlayShortestVectors // dot s.val v.val = k} = 1 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_one_iff]
  obtain ⟨hs, hd⟩ := (hw w).mpr rfl
  refine ⟨⟨⟨w, hs⟩, hd⟩, fun v => ?_⟩
  exact Subtype.ext (Subtype.ext ((hw v.val.val).mp ⟨v.val.property, v.property⟩))

/-- The +32 layer has one shortest vector. -/
theorem card_dot_pos_thirty_two (s : PlayShortestVectors) :
    Nat.card {v : PlayShortestVectors // dot s.val v.val = 32} = 1 :=
  card_layer_of_singleton s 32 s.val (pos_thirty_two_layer_iff s)

/-- The −32 layer has one shortest vector. -/
theorem card_dot_neg_thirty_two (s : PlayShortestVectors) :
    Nat.card {v : PlayShortestVectors // dot s.val v.val = -32} = 1 :=
  card_layer_of_singleton s (-32) (-s.val) (neg_thirty_two_layer_iff s)

end LeechLayers
