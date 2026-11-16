import HarperSquash.NbhdInit

/-!
# Stage 1b. The squash in direction `i`

Split a family by whether its members contain `i`. The squash replaces each of the two halves by
the initial segment of the same size, taken in the smaller cube on `S.erase i`.
-/

open Finset

namespace HarperVertex

open scoped Classical symmDiff

variable {α : Type*} [LinearOrder α]

/-- The squash of `𝒜` in direction `i`. -/
noncomputable def squash (S : Finset α) (i : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  initSeg (S.erase i) (𝒜.nonMemberSubfamily i).card ∪
    (initSeg (S.erase i) (𝒜.memberSubfamily i).card).image (insert i)

/-- Harper's inequality for the cube on `T`, in the form used for the induction. -/
def HarperAt (T : Finset α) : Prop :=
  ∀ 𝒜 : Finset (Finset α), 𝒜 ⊆ T.powerset → (nbhd T (initSeg T 𝒜.card)).card ≤ (nbhd T 𝒜).card

lemma notMem_of_mem_initSeg {S x : Finset α} {i : α} {m : ℕ} (hx : x ∈ initSeg (S.erase i) m) :
    i ∉ x := by
  intro h
  have := mem_powerset.1 ((isInit_initSeg _ _).1 hx) h
  exact (mem_erase.1 this).1 rfl

lemma squash_subset {S : Finset α} {i : α} (hi : i ∈ S) (𝒜 : Finset (Finset α)) :
    squash S i 𝒜 ⊆ S.powerset := by
  intro x hx
  rcases mem_union.1 hx with hx | hx
  · exact mem_powerset.2 ((mem_powerset.1 ((isInit_initSeg _ _).1 hx)).trans (erase_subset _ _))
  · obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
    exact mem_powerset.2 (insert_subset hi
      ((mem_powerset.1 ((isInit_initSeg _ _).1 hy)).trans (erase_subset _ _)))

lemma nonMember_squash (S : Finset α) (i : α) (𝒜 : Finset (Finset α)) :
    (squash S i 𝒜).nonMemberSubfamily i =
      initSeg (S.erase i) (𝒜.nonMemberSubfamily i).card := by
  ext x
  rw [mem_nonMemberSubfamily, squash, mem_union, mem_image]
  constructor
  · rintro ⟨hx | ⟨y, -, rfl⟩, hix⟩
    · exact hx
    · exact absurd (mem_insert_self i y) hix
  · intro hx
    exact ⟨Or.inl hx, notMem_of_mem_initSeg hx⟩

lemma member_squash (S : Finset α) (i : α) (𝒜 : Finset (Finset α)) :
    (squash S i 𝒜).memberSubfamily i = initSeg (S.erase i) (𝒜.memberSubfamily i).card := by
  ext x
  rw [mem_memberSubfamily, squash, mem_union, mem_image]
  constructor
  · rintro ⟨hx | ⟨y, hy, hyx⟩, hix⟩
    · exact absurd (mem_insert_self i x) (notMem_of_mem_initSeg hx)
    · have : y = x := by
        rw [← erase_insert (notMem_of_mem_initSeg hy), hyx, erase_insert hix]
      exact this ▸ hy
  · intro hx
    exact ⟨Or.inr ⟨x, hx, rfl⟩, notMem_of_mem_initSeg hx⟩

/-- A squash keeps the size of the family. -/
lemma card_squash {S : Finset α} {𝒜 : Finset (Finset α)} (h : 𝒜 ⊆ S.powerset) (i : α) :
    (squash S i 𝒜).card = 𝒜.card := by
  rw [card_sections i (squash S i 𝒜), nonMember_squash, member_squash,
    card_initSeg (card_le_card (nonMember_subset h i)),
    card_initSeg (card_le_card (member_subset h i)), ← card_sections]

/-- **Stage 1.** Assuming Harper's inequality in the smaller cube on `S.erase i`, a squash never
makes the neighbourhood bigger. -/
theorem card_nbhd_squash_le {S : Finset α} {𝒜 : Finset (Finset α)} (h : 𝒜 ⊆ S.powerset) {i : α}
    (hi : i ∈ S) (hT : HarperAt (S.erase i)) :
    (nbhd S (squash S i 𝒜)).card ≤ (nbhd S 𝒜).card := by
  have hsq := squash_subset hi 𝒜
  rw [card_sections i (nbhd S (squash S i 𝒜)), card_sections i (nbhd S 𝒜),
    nonMember_nbhd hsq, member_nbhd hsq hi, nonMember_nbhd h, member_nbhd h hi,
    nonMember_squash, member_squash]
  set lo := 𝒜.nonMemberSubfamily i
  set hi' := 𝒜.memberSubfamily i
  set T := S.erase i
  have hlo : lo ⊆ T.powerset := nonMember_subset h i
  have hhi : hi' ⊆ T.powerset := member_subset h i
  rw [card_union_init (isInit_nbhd (isInit_initSeg T _)) (isInit_initSeg T _),
    card_union_init (isInit_nbhd (isInit_initSeg T _)) (isInit_initSeg T _),
    card_initSeg (card_le_card hlo), card_initSeg (card_le_card hhi)]
  apply add_le_add
  · exact max_le ((hT lo hlo).trans (card_le_card subset_union_left))
      (card_le_card subset_union_right)
  · exact max_le ((hT hi' hhi).trans (card_le_card subset_union_left))
      (card_le_card subset_union_right)

/-! ## Squashing terminates: the weight goes down -/

/-- The weight of a family: the sum of the positions of its members in the simplicial order. -/
noncomputable def weight (S : Finset α) (𝒜 : Finset (Finset α)) : ℕ := ∑ x ∈ 𝒜, rank S x

lemma weight_sections (S : Finset α) (i : α) (𝒜 : Finset (Finset α)) :
    weight S 𝒜 = ∑ x ∈ 𝒜.nonMemberSubfamily i, rank S x +
      ∑ y ∈ 𝒜.memberSubfamily i, rank S (insert i y) := by
  unfold weight
  rw [← sum_filter_add_sum_filter_not 𝒜 (fun x => i ∈ x), add_comm]
  congr 1
  rw [← image_insert_memberSubfamily, sum_image]
  intro x hx y hy hxy
  have hx' := (mem_memberSubfamily.1 hx).2
  have hy' := (mem_memberSubfamily.1 hy).2
  rw [← erase_insert hx', hxy, erase_insert hy']

/-- Among families of a given size in a cube, the initial segment has the least sum of any
strictly increasing function, and any other family has a strictly larger sum. -/
lemma sum_init_lt {T : Finset α} {f : Finset α → ℕ}
    (hf : ∀ x y, x ⊆ T → y ⊆ T → Before x y → f x < f y) {P 𝒜 : Finset (Finset α)}
    (hP : IsInit T P) (h𝒜 : 𝒜 ⊆ T.powerset) (hcard : P.card = 𝒜.card) (hne : 𝒜 ≠ P) :
    ∑ x ∈ P, f x < ∑ x ∈ 𝒜, f x := by
  have h1 : (𝒜 \ P).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    exact hne (eq_of_subset_of_card_le (sdiff_eq_empty_iff_subset.1 h) hcard.le)
  have hc : (P \ 𝒜).card = (𝒜 \ P).card := by
    have e1 := card_sdiff_add_card_inter P 𝒜
    have e2 := card_sdiff_add_card_inter 𝒜 P
    rw [inter_comm] at e2
    omega
  have h2 : (P \ 𝒜).Nonempty := by
    rw [← card_pos, hc]; exact card_pos.2 h1
  have hlt : ∀ u ∈ P \ 𝒜, ∀ v ∈ 𝒜 \ P, f u < f v := by
    intro u hu v hv
    rw [mem_sdiff] at hu hv
    have huv : u ≠ v := fun e => hu.2 (e ▸ hv.1)
    have huT := mem_powerset.1 (hP.1 hu.1)
    have hvT := mem_powerset.1 (h𝒜 hv.1)
    rcases before_total huv with h | h
    · exact hf u v huT hvT h
    · exact absurd (hP.2 u hu.1 v hvT h) hv.2
  obtain ⟨v0, hv0, hmin⟩ := exists_min_image (𝒜 \ P) f h1
  have key : ∑ x ∈ P \ 𝒜, f x < ∑ x ∈ 𝒜 \ P, f x := by
    calc ∑ x ∈ P \ 𝒜, f x < ∑ _x ∈ P \ 𝒜, f v0 :=
          sum_lt_sum_of_nonempty h2 (fun u hu => hlt u hu v0 hv0)
      _ = ∑ _x ∈ 𝒜 \ P, f v0 := by rw [sum_const, sum_const, hc]
      _ ≤ ∑ x ∈ 𝒜 \ P, f x := sum_le_sum (fun x hx => hmin x hx)
  rw [← sum_sdiff (inter_subset_left : P ∩ 𝒜 ⊆ P), ← sum_sdiff (inter_subset_right : P ∩ 𝒜 ⊆ 𝒜),
    sdiff_inter_self_left, sdiff_inter_self_right]
  omega

lemma sum_init_le {T : Finset α} {f : Finset α → ℕ}
    (hf : ∀ x y, x ⊆ T → y ⊆ T → Before x y → f x < f y) {P 𝒜 : Finset (Finset α)}
    (hP : IsInit T P) (h𝒜 : 𝒜 ⊆ T.powerset) (hcard : P.card = 𝒜.card) :
    ∑ x ∈ P, f x ≤ ∑ x ∈ 𝒜, f x := by
  by_cases hne : 𝒜 = P
  · rw [hne]
  · exact (sum_init_lt hf hP h𝒜 hcard hne).le

/-- **Squashing terminates.** If one of the two halves of `𝒜` in direction `i` is not already an
initial segment, the squash strictly lowers the weight. -/
theorem weight_squash_lt {S : Finset α} {𝒜 : Finset (Finset α)} (h : 𝒜 ⊆ S.powerset) {i : α}
    (hi : i ∈ S)
    (hnot : ¬ (IsInit (S.erase i) (𝒜.nonMemberSubfamily i) ∧
      IsInit (S.erase i) (𝒜.memberSubfamily i))) :
    weight S (squash S i 𝒜) < weight S 𝒜 := by
  rw [weight_sections S i (squash S i 𝒜), weight_sections S i 𝒜, nonMember_squash,
    member_squash]
  set T := S.erase i
  have hlo : 𝒜.nonMemberSubfamily i ⊆ T.powerset := nonMember_subset h i
  have hhi : 𝒜.memberSubfamily i ⊆ T.powerset := member_subset h i
  have hf1 : ∀ x y, x ⊆ T → y ⊆ T → Before x y → rank S x < rank S y :=
    fun x y hx _ hxy => rank_lt_rank (hx.trans (erase_subset _ _)) hxy
  have hf2 : ∀ x y, x ⊆ T → y ⊆ T → Before x y → rank S (insert i x) < rank S (insert i y) := by
    intro x y hx hy hxy
    have hix : i ∉ x := fun h' => (mem_erase.1 (hx h')).1 rfl
    have hiy : i ∉ y := fun h' => (mem_erase.1 (hy h')).1 rfl
    exact rank_lt_rank (insert_subset hi (hx.trans (erase_subset _ _)))
      ((before_insert_iff hix hiy).2 hxy)
  have c1 := (card_initSeg (card_le_card hlo))
  have c2 := (card_initSeg (card_le_card hhi))
  by_cases h1 : IsInit T (𝒜.nonMemberSubfamily i)
  · have h2 : ¬ IsInit T (𝒜.memberSubfamily i) := fun h2 => hnot ⟨h1, h2⟩
    have hne : 𝒜.memberSubfamily i ≠ initSeg T (𝒜.memberSubfamily i).card :=
      fun e => h2 (e ▸ isInit_initSeg _ _)
    exact add_lt_add_of_le_of_lt (sum_init_le hf1 (isInit_initSeg _ _) hlo c1)
      (sum_init_lt hf2 (isInit_initSeg _ _) hhi c2 hne)
  · have hne : 𝒜.nonMemberSubfamily i ≠ initSeg T (𝒜.nonMemberSubfamily i).card :=
      fun e => h1 (e ▸ isInit_initSeg _ _)
    exact add_lt_add_of_lt_of_le (sum_init_lt hf1 (isInit_initSeg _ _) hlo c1 hne)
      (sum_init_le hf2 (isInit_initSeg _ _) hhi c2)

end HarperVertex
