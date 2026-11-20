import ConwayOrder
import PlaygroundLeech
import LeechNorm48Moments
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

-- The seven layers together contain all 196,560 shortest vectors.
private theorem dot_mem_layers (s v : PlayShortestVectors) :
    dot s.val v.val ∈ ({0, 8, -8, 16, -16, 32, -32} : Finset ℤ) := by
  classical
  let layers : Finset ℤ := {0, 8, -8, 16, -16, 32, -32}
  let product (x : PlayShortestVectors) := dot s.val x.val
  have fiber (k : ℤ) : (univ.filter (fun x => product x = k)).card =
      Nat.card {x : PlayShortestVectors // dot s.val x.val = k} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have full : (univ.filter (fun x => product x ∈ layers)).card =
      (univ : Finset PlayShortestVectors).card := by
    rw [← sum_card_fiberwise_eq_card_filter univ layers product]
    simp only [fiber, card_univ, card_play_shortest_vectors]
    norm_num [layers, sum_insert, -Nat.card_eq_fintype_card, card_perpendicular,
      card_dot_pos_eight, card_dot_neg_eight,
      card_dot_pos_sixteen, card_dot_neg_sixteen, card_dot_pos_thirty_two, card_dot_neg_thirty_two]
  have covered : ∀ x ∈ (univ : Finset PlayShortestVectors), product x ∈ layers :=
    card_filter_eq_iff.mp full
  change product v ∈ layers
  simpa only [mem_univ, forall_const] using covered v

/-- For any shortest vector, count the shortest vectors at each integer dot product.
Every value outside the seven listed here has count zero. -/
theorem card_dot_layer (s : PlayShortestVectors) (k : ℤ) :
    Nat.card {v : PlayShortestVectors // dot s.val v.val = k} =
      if k = 0 then 93150
      else if k = 8 ∨ k = -8 then 47104
      else if k = 16 ∨ k = -16 then 4600
      else if k = 32 ∨ k = -32 then 1
      else 0 := by
  split_ifs with h0 h8 h16 h32
  · subst k
    exact card_perpendicular s
  · rcases h8 with rfl | rfl
    · exact card_dot_pos_eight s
    · exact card_dot_neg_eight s
  · rcases h16 with rfl | rfl
    · exact card_dot_pos_sixteen s
    · exact card_dot_neg_sixteen s
  · rcases h32 with rfl | rfl
    · exact card_dot_pos_thirty_two s
    · exact card_dot_neg_thirty_two s
  · classical
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
    refine ⟨fun v => ?_⟩
    have hm := dot_mem_layers s v.val
    rw [v.property] at hm
    simp only [mem_insert, mem_singleton] at hm
    tauto

open LeechNorm48Layers (Shell onShell)
local notation "diff48" => LeechNorm48Layers.diff

private theorem levels48 (x : Shell) :
    diff48 x ∈ ({0, 2, -2, 4, -4, 6, -6} : Finset ℤ) := by
  let r := (root true).val
  have nr : normSq r = 32 := (root true).property.2
  have nx : normSq x.val.val = 48 := x.property
  have dr : dot r x.val.val = 4 * diff48 x := root_dot _
  have nzsub : r - x.val.val ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h] at nr
    omega
  have nzadd : r + x.val.val ≠ 0 := by
    intro h
    rw [add_eq_zero_iff_eq_neg.mp h, normSq_neg] at nr
    omega
  have lo := leech_norm_ge_32 _ (leechLattice.add_mem (root true).property.1 x.val.property) nzadd
  have hi := leech_norm_ge_32 _ (leechLattice.sub_mem (root true).property.1 x.val.property) nzsub
  change 32 ≤ normSq (r + x.val.val) at lo
  change 32 ≤ normSq (r - x.val.val) at hi
  rw [normSq_add, nr, nx, dr] at lo
  rw [normSq_sub, nr, nx, dr] at hi
  have hd : 8 ∣ dot r x.val.val :=
    LeechBasis.leech_inner_dvd_eight _ _ (root true).property.1 x.val.property
  rw [dr] at hd
  obtain ⟨q, hq⟩ := hd
  simp only [mem_insert, mem_singleton]
  omega

private noncomputable def count48 (d : ℤ) : ℤ := Nat.card {x : Shell // diff48 x = d}

private theorem opposite48 (d : ℤ) : count48 (-d) = count48 d := by
  let e : {x : Shell // diff48 x = -d} ≃ {x : Shell // diff48 x = d} :=
    Equiv.subtypeEquiv (onShell centralNegation) fun x => by
      change x.val.val 0 - x.val.val 1 = -d ↔ -x.val.val 0 - (-x.val.val 1) = d
      omega
  exact congrArg (fun n : ℕ => (n : ℤ)) (Nat.card_congr e)

-- Subtracting a vector from the reference axis exchanges the +24 layer at squared length 48
-- with the +8 layer of shortest vectors.
private def outer48 : {x : Shell // diff48 x = 6} ≃ {v : MinimalVectors // diff v = 2} where
  toFun := fun ⟨x, hx⟩ => by
    have hd : dot (root true).val x.val.val = 24 := by
      rw [root_dot]; change 4 * diff48 x = 24; omega
    refine ⟨⟨(root true).val - x.val.val, leechLattice.sub_mem (root true).property.1 x.val.property,
      by rw [normSq_sub, (root true).property.2, x.property, hd]; decide⟩, ?_⟩
    change (4 - x.val.val 0) - (-4 - x.val.val 1) = 2
    change x.val.val 0 - x.val.val 1 = 6 at hx
    omega
  invFun := fun ⟨v, hv⟩ => by
    have hd : dot (root true).val v.val = 8 := by
      rw [root_dot]; change 4 * diff v = 8; omega
    refine ⟨⟨asL (root true) - asL v, ?_⟩, ?_⟩
    · change normSq ((root true).val - v.val) = 48
      rw [normSq_sub, (root true).property.2, v.property.2, hd]; decide
    · change (4 - v.val 0) - (-4 - v.val 1) = 6
      change v.val 0 - v.val 1 = 2 at hv
      omega
  left_inv x := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    change (root true).val - ((root true).val - x.val.val.val) = x.val.val.val
    abel
  right_inv v := by
    apply Subtype.ext; apply Subtype.ext
    change (root true).val - ((root true).val - v.val.val) = v.val.val
    abel

private theorem at_six48 : count48 6 = 47104 := by
  change (Nat.card {x : Shell // diff48 x = 6} : ℤ) = _
  rw [Nat.card_congr outer48, ← count_card]
  exact counts.1

private theorem sum_by_layer48 (f : ℤ → ℤ) :
    (∑ x : Shell, f (diff48 x)) =
      ∑ d ∈ ({0, 2, -2, 4, -4, 6, -6} : Finset ℤ), count48 d * f d := by
  classical
  have h := (sum_fiberwise_of_maps_to' (s := (univ : Finset Shell))
    (g := diff48) (fun x _ => levels48 x) f).symm
  simpa only [sum_const, nsmul_eq_mul, count48, Nat.card_eq_fintype_card, Fintype.card_subtype] using h

private theorem counts48 : count48 0 = 6476800 ∧ count48 2 = 4147200 ∧ count48 4 = 953856 := by
  have total := sum_by_layer48 (fun _ => 1)
  have second := sum_by_layer48 (fun d => d ^ 2)
  have fourth := sum_by_layer48 (fun d => d ^ 4)
  norm_num [sum_insert, LeechNorm48Layers.shell_card, LeechNorm48Layers.diff_moments.1,
    LeechNorm48Layers.diff_moments.2, opposite48, at_six48] at total second fourth
  omega

/-- Vectors of squared length 48 in the playground's integer coordinates. -/
abbrev PlayNorm48Vectors := {v : Vec // InPlayLeech v ∧ normSq v = 48}

private def toShell48 : PlayNorm48Vectors ≃ Shell :=
  (Equiv.subtypeEquiv vectorEquiv (fun x => by
    change (InPlayLeech x ∧ normSq x = 48) ↔ (InLeech (toLean x) ∧ normSq (toLean x) = 48)
    rw [lattice_correspondence, norm_toLean])).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter InLeech (fun x => normSq x = 48)).symm

private def layerEquiv48 (s : PlayShortestVectors) (k : ℤ) (g : Aut)
    (hg : onShortest g (root true) = toMinimal s) :
    {x : Shell // 4 * diff48 x = k} ≃ {v : PlayNorm48Vectors // dot s.val v.val = k} :=
  let e := (onShell g).trans toShell48.symm
  Equiv.subtypeEquiv e fun x => by
    have hd := dot_toLean s.val (e x).val
    change dot (toMinimal s).val (toShell48 (e x)).val.val = _ at hd
    have he : toShell48 (e x) = onShell g x := toShell48.apply_symm_apply _
    rw [← hd, he, ← hg]
    change 4 * diff48 x = k ↔ dot (g (asL (root true))).val (g x.val).val = k
    rw [map_dot]
    change 4 * diff48 x = k ↔ dot (root true).val x.val.val = k
    rw [root_dot]
    rfl

/-- Count squared-length-48 vectors by their dot product with any shortest vector.
Every other integer dot product has count zero. -/
theorem card_norm48_dot_layer (s : PlayShortestVectors) (k : ℤ) :
    Nat.card {v : PlayNorm48Vectors // dot s.val v.val = k} =
      if k = 0 then 6476800
      else if k = 8 ∨ k = -8 then 4147200
      else if k = 16 ∨ k = -16 then 953856
      else if k = 24 ∨ k = -24 then 47104
      else 0 := by
  classical
  obtain ⟨g, hg⟩ := shortest_transitive (toMinimal s)
  rw [← Nat.card_congr (layerEquiv48 s k g hg)]
  have sum := sum_by_layer48 (fun d => if 4 * d = k then 1 else 0)
  simp only [sum_boole] at sum
  have card : (Nat.card {x : Shell // 4 * diff48 x = k} : ℤ) =
      ((univ.filter (fun x : Shell => 4 * diff48 x = k)).card : ℤ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  norm_num [sum_insert, opposite48, counts48.1, counts48.2.1, counts48.2.2, at_six48] at sum
  apply Int.ofNat_inj.mp
  rw [card, sum]
  by_cases hk : k ∈ ({0, 8, -8, 16, -16, 24, -24} : Finset ℤ)
  · simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · simp only [mem_insert, mem_singleton, not_or] at hk
    obtain ⟨h0,h8,hn8,h16,hn16,h24,hn24⟩ := hk
    simp [h0, h8, hn8, h16, hn16, h24, hn24, Ne.symm h0, Ne.symm h8, Ne.symm hn8,
      Ne.symm h16, Ne.symm hn16, Ne.symm h24, Ne.symm hn24]

end LeechLayers
