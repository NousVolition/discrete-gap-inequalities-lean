import Mathlib

/-!
# Stage 1a. The simplicial order, the neighbourhood, initial segments, sections

The cube is the family of all subsets of a finite ground set `S` (inside a linearly ordered type
`α`). Two sets are neighbours when they differ in at most one element.
-/

open Finset

namespace HarperVertex

open scoped Classical symmDiff

variable {α : Type*} [LinearOrder α]

/-! ## The order -/

/-- `x` comes before `y` in lexicographic order: the least element where they differ lies in `x`. -/
def LexBefore (x y : Finset α) : Prop :=
  ∃ d, d ∈ x ∧ d ∉ y ∧ ∀ e, e < d → (e ∈ x ↔ e ∈ y)

/-- The simplicial order: smaller sets come first; sets of equal size are in lexicographic order. -/
def Before (x y : Finset α) : Prop :=
  x.card < y.card ∨ (x.card = y.card ∧ LexBefore x y)

lemma lexBefore_irrefl (x : Finset α) : ¬ LexBefore x x := by
  rintro ⟨d, h1, h2, -⟩
  exact h2 h1

lemma lexBefore_trans {x y z : Finset α} (h1 : LexBefore x y) (h2 : LexBefore y z) :
    LexBefore x z := by
  obtain ⟨d, hdx, hdy, hd⟩ := h1
  obtain ⟨e, hey, hez, he⟩ := h2
  rcases lt_trichotomy d e with hde | rfl | hed
  · refine ⟨d, hdx, fun hz => hdy ((he d hde).2 hz), fun c hc => ?_⟩
    rw [hd c hc, he c (hc.trans hde)]
  · exact absurd hey hdy
  · refine ⟨e, (hd e hed).2 hey, hez, fun c hc => ?_⟩
    rw [hd c (hc.trans hed), he c hc]

lemma lexBefore_total {x y : Finset α} (h : x ≠ y) : LexBefore x y ∨ LexBefore y x := by
  have hne : (x ∆ y).Nonempty := symmDiff_nonempty.2 h
  set d := (x ∆ y).min' hne with hd
  have hmem : d ∈ x ∆ y := min'_mem _ _
  have hbelow : ∀ e, e < d → (e ∈ x ↔ e ∈ y) := by
    intro e he
    have : e ∉ x ∆ y := fun h' => absurd (min'_le _ _ h') (not_le.2 he)
    rw [mem_symmDiff] at this
    tauto
  rw [mem_symmDiff] at hmem
  rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨d, h1, h2, hbelow⟩
  · exact Or.inr ⟨d, h1, h2, fun e he => (hbelow e he).symm⟩

lemma before_irrefl (x : Finset α) : ¬ Before x x := by
  rintro (h | ⟨-, h⟩)
  · exact lt_irrefl _ h
  · exact lexBefore_irrefl x h

lemma before_trans {x y z : Finset α} (h1 : Before x y) (h2 : Before y z) : Before x z := by
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (h1.trans h2)
  · exact Or.inl (h2 ▸ h1)
  · exact Or.inl (h1 ▸ h2)
  · exact Or.inr ⟨h1.trans h2, lexBefore_trans h1' h2'⟩

lemma before_asymm {x y : Finset α} (h1 : Before x y) (h2 : Before y x) : False :=
  before_irrefl x (before_trans h1 h2)

lemma before_total {x y : Finset α} (h : x ≠ y) : Before x y ∨ Before y x := by
  rcases lt_trichotomy x.card y.card with hc | hc | hc
  · exact Or.inl (Or.inl hc)
  · rcases lexBefore_total h with h' | h'
    · exact Or.inl (Or.inr ⟨hc, h'⟩)
    · exact Or.inr (Or.inr ⟨hc.symm, h'⟩)
  · exact Or.inr (Or.inl hc)

lemma before_of_card_lt {x y : Finset α} (h : x.card < y.card) : Before x y := Or.inl h

lemma card_le_of_before {x y : Finset α} (h : Before x y) : x.card ≤ y.card := by
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

lemma lexBefore_insert_iff {i : α} {x y : Finset α} (hx : i ∉ x) (hy : i ∉ y) :
    LexBefore (insert i x) (insert i y) ↔ LexBefore x y := by
  constructor
  · rintro ⟨d, h1, h2, h3⟩
    have hdi : d ≠ i := fun h => h2 (h ▸ mem_insert_self _ _)
    refine ⟨d, (mem_insert.1 h1).resolve_left hdi, fun h => h2 (mem_insert_of_mem h),
      fun e he => ?_⟩
    have := h3 e he
    by_cases hei : e = i
    · subst hei; simp [hx, hy]
    · simpa [mem_insert, hei] using this
  · rintro ⟨d, h1, h2, h3⟩
    have hdi : d ≠ i := fun h => hx (h ▸ h1)
    refine ⟨d, mem_insert_of_mem h1, ?_, fun e he => ?_⟩
    · simp [mem_insert, hdi, h2]
    · simp [mem_insert, h3 e he]

lemma before_insert_iff {i : α} {x y : Finset α} (hx : i ∉ x) (hy : i ∉ y) :
    Before (insert i x) (insert i y) ↔ Before x y := by
  unfold Before
  rw [card_insert_of_notMem hx, card_insert_of_notMem hy, lexBefore_insert_iff hx hy]
  simp only [Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]

lemma before_erase_iff {i : α} {x y : Finset α} (hx : i ∈ x) (hy : i ∈ y) :
    Before (x.erase i) (y.erase i) ↔ Before x y := by
  conv_rhs => rw [← insert_erase hx, ← insert_erase hy]
  exact (before_insert_iff (notMem_erase i x) (notMem_erase i y)).symm

/-! ## Neighbours and the neighbourhood -/

/-- Two sets are neighbours (or equal) when they differ in at most one element. -/
def Adj (x y : Finset α) : Prop := (x ∆ y).card ≤ 1

lemma adj_refl (x : Finset α) : Adj x x := by simp [Adj]

lemma adj_comm {x y : Finset α} : Adj x y ↔ Adj y x := by
  unfold Adj; rw [symmDiff_comm]

lemma adj_insert {a : α} {x : Finset α} (ha : a ∉ x) : Adj x (insert a x) := by
  unfold Adj
  have : x ∆ insert a x = {a} := by
    ext e
    simp only [mem_symmDiff, mem_insert, mem_singleton]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact absurd (Or.inr h1) h2
      · exact h1.resolve_right h2
    · rintro rfl; exact Or.inr ⟨Or.inl rfl, ha⟩
  rw [this, card_singleton]

lemma adj_erase {a : α} {x : Finset α} (ha : a ∈ x) : Adj x (x.erase a) := by
  rw [adj_comm]
  have := adj_insert (notMem_erase a x)
  rwa [insert_erase ha] at this

lemma adj_cases {x y : Finset α} (h : Adj x y) :
    x = y ∨ (∃ a, a ∉ x ∧ y = insert a x) ∨ (∃ a, a ∈ x ∧ y = x.erase a) := by
  unfold Adj at h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with h0 | h1
  · left
    rw [card_eq_zero] at h0
    exact symmDiff_eq_bot.1 h0
  · right
    obtain ⟨a, ha⟩ := card_eq_one.1 h1
    have hmem : a ∈ x ∆ y := by rw [ha]; exact mem_singleton_self a
    have hoth : ∀ e, e ≠ a → (e ∈ x ↔ e ∈ y) := by
      intro e he
      have : e ∉ x ∆ y := by rw [ha]; simpa using he
      rw [mem_symmDiff] at this
      tauto
    rw [mem_symmDiff] at hmem
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right
      refine ⟨a, h1, ?_⟩
      ext e
      rw [mem_erase]
      by_cases hea : e = a
      · subst hea; simp [h2]
      · simp [hea, hoth e hea]
    · left
      refine ⟨a, h2, ?_⟩
      ext e
      rw [mem_insert]
      by_cases hea : e = a
      · subst hea; simp [h1]
      · simp [hea, hoth e hea]

lemma card_le_succ_of_adj {x y : Finset α} (h : Adj x y) : y.card ≤ x.card + 1 := by
  rcases adj_cases h with rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · omega
  · rw [card_insert_of_notMem ha]
  · rw [card_erase_of_mem ha]; omega

lemma symmDiff_insert_insert {i : α} {x y : Finset α} (hx : i ∉ x) (hy : i ∉ y) :
    insert i x ∆ insert i y = x ∆ y := by
  ext e
  simp only [mem_symmDiff, mem_insert]
  by_cases hei : e = i
  · subst hei; simp [hx, hy]
  · simp [hei]

lemma adj_insert_insert_iff {i : α} {x y : Finset α} (hx : i ∉ x) (hy : i ∉ y) :
    Adj (insert i x) (insert i y) ↔ Adj x y := by
  unfold Adj; rw [symmDiff_insert_insert hx hy]

lemma adj_insert_left_iff {i : α} {x y : Finset α} (hx : i ∉ x) (hy : i ∉ y) :
    Adj (insert i x) y ↔ x = y := by
  unfold Adj
  have h1 : insert i x ∆ y = insert i (x ∆ y) := by
    ext e
    simp only [mem_symmDiff, mem_insert]
    by_cases hei : e = i
    · subst hei; simp [hx, hy]
    · simp [hei]
  have h2 : i ∉ x ∆ y := by simp [mem_symmDiff, hx, hy]
  rw [h1, card_insert_of_notMem h2, ← symmDiff_eq_bot, bot_eq_empty, ← card_eq_zero]
  omega

/-- The neighbourhood of a family `𝒜` inside the cube on `S`: every subset of `S` that equals,
or differs in one element from, some member of `𝒜`. -/
noncomputable def nbhd (S : Finset α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  S.powerset.filter (fun y => ∃ x ∈ 𝒜, Adj x y)

lemma mem_nbhd {S : Finset α} {𝒜 : Finset (Finset α)} {y : Finset α} :
    y ∈ nbhd S 𝒜 ↔ y ⊆ S ∧ ∃ x ∈ 𝒜, Adj x y := by
  simp [nbhd]

lemma nbhd_subset_powerset (S : Finset α) (𝒜 : Finset (Finset α)) : nbhd S 𝒜 ⊆ S.powerset :=
  filter_subset _ _

lemma nbhd_mono {S : Finset α} {𝒜 ℬ : Finset (Finset α)} (h : 𝒜 ⊆ ℬ) : nbhd S 𝒜 ⊆ nbhd S ℬ := by
  intro y hy
  rw [mem_nbhd] at hy ⊢
  obtain ⟨hyS, x, hx, hxy⟩ := hy
  exact ⟨hyS, x, h hx, hxy⟩

lemma subset_nbhd {S : Finset α} {𝒜 : Finset (Finset α)} (h : 𝒜 ⊆ S.powerset) :
    𝒜 ⊆ nbhd S 𝒜 := by
  intro y hy
  rw [mem_nbhd]
  exact ⟨mem_powerset.1 (h hy), y, hy, adj_refl y⟩

/-! ## Initial segments -/

/-- `𝒞` is an initial segment of the simplicial order on the subsets of `S`. -/
def IsInit (S : Finset α) (𝒞 : Finset (Finset α)) : Prop :=
  𝒞 ⊆ S.powerset ∧ ∀ x ∈ 𝒞, ∀ y, y ⊆ S → Before y x → y ∈ 𝒞

lemma init_nested {S : Finset α} {P Q : Finset (Finset α)} (hP : IsInit S P) (hQ : IsInit S Q) :
    P ⊆ Q ∨ Q ⊆ P := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨x, hxP, hxQ⟩ := not_subset.1 h1
  obtain ⟨y, hyQ, hyP⟩ := not_subset.1 h2
  have hxy : x ≠ y := fun h => hxQ (h ▸ hyQ)
  rcases before_total hxy with h | h
  · exact hxQ (hQ.2 y hyQ x (mem_powerset.1 (hP.1 hxP)) h)
  · exact hyP (hP.2 x hxP y (mem_powerset.1 (hQ.1 hyQ)) h)

lemma init_eq_of_card_eq {S : Finset α} {P Q : Finset (Finset α)} (hP : IsInit S P)
    (hQ : IsInit S Q) (h : P.card = Q.card) : P = Q := by
  rcases init_nested hP hQ with h' | h'
  · exact eq_of_subset_of_card_le h' h.ge
  · exact (eq_of_subset_of_card_le h' h.le).symm

lemma card_union_init {S : Finset α} {P Q : Finset (Finset α)} (hP : IsInit S P)
    (hQ : IsInit S Q) : (P ∪ Q).card = max P.card Q.card := by
  rcases init_nested hP hQ with h | h
  · rw [union_eq_right.2 h, max_eq_right (card_le_card h)]
  · rw [union_eq_left.2 h, max_eq_left (card_le_card h)]

/-! ## Rank and the initial segment of each size -/

/-- The position of `x` in the simplicial order on the subsets of `S`. -/
noncomputable def rank (S : Finset α) (x : Finset α) : ℕ :=
  (S.powerset.filter (fun y => Before y x)).card

lemma rank_lt_rank {S x y : Finset α} (hx : x ⊆ S) (h : Before x y) : rank S x < rank S y := by
  unfold rank
  apply card_lt_card
  rw [ssubset_iff_of_subset]
  · refine ⟨x, ?_, ?_⟩
    · simp [hx, h]
    · simp [before_irrefl]
  · intro z hz
    simp only [mem_filter] at hz ⊢
    exact ⟨hz.1, before_trans hz.2 h⟩

lemma rank_lt_card {S x : Finset α} (hx : x ⊆ S) : rank S x < S.powerset.card := by
  unfold rank
  apply card_lt_card
  rw [ssubset_iff_of_subset (filter_subset _ _)]
  exact ⟨x, mem_powerset.2 hx, by simp [before_irrefl]⟩

lemma rank_injOn (S : Finset α) : Set.InjOn (rank S) S.powerset := by
  intro x hx y hy h
  by_contra hxy
  rcases before_total hxy with h' | h'
  · exact absurd h (rank_lt_rank (mem_powerset.1 hx) h').ne
  · exact absurd h (rank_lt_rank (mem_powerset.1 hy) h').ne'

lemma image_rank (S : Finset α) : S.powerset.image (rank S) = range S.powerset.card := by
  apply eq_of_subset_of_card_le
  · intro r hr
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hr
    exact mem_range.2 (rank_lt_card (mem_powerset.1 hx))
  · rw [card_range, card_image_of_injOn (rank_injOn S)]

/-- The initial segment of size `m` of the simplicial order on the subsets of `S`. -/
noncomputable def initSeg (S : Finset α) (m : ℕ) : Finset (Finset α) :=
  S.powerset.filter (fun x => rank S x < m)

lemma isInit_initSeg (S : Finset α) (m : ℕ) : IsInit S (initSeg S m) := by
  refine ⟨filter_subset _ _, fun x hx y hy hyx => ?_⟩
  simp only [initSeg, mem_filter, mem_powerset] at hx ⊢
  exact ⟨hy, (rank_lt_rank hy hyx).trans hx.2⟩

lemma card_initSeg {S : Finset α} {m : ℕ} (hm : m ≤ S.powerset.card) :
    (initSeg S m).card = m := by
  have hinj : Set.InjOn (rank S) (initSeg S m) :=
    (rank_injOn S).mono (by intro x hx; exact filter_subset _ _ hx)
  rw [← card_image_of_injOn hinj]
  have : (initSeg S m).image (rank S) = (range S.powerset.card).filter (· < m) := by
    rw [← image_rank, filter_image]; rfl
  rw [this]
  have : (range S.powerset.card).filter (· < m) = range m := by
    ext r; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]

/-! ## Sections in direction `i` -/

lemma nonMember_subset {S : Finset α} {𝒜 : Finset (Finset α)} (h : 𝒜 ⊆ S.powerset) (i : α) :
    𝒜.nonMemberSubfamily i ⊆ (S.erase i).powerset := by
  intro x hx
  rw [mem_nonMemberSubfamily] at hx
  rw [mem_powerset]
  intro e he
  exact mem_erase.2 ⟨fun h' => hx.2 (h' ▸ he), mem_powerset.1 (h hx.1) he⟩

lemma member_subset {S : Finset α} {𝒜 : Finset (Finset α)} (h : 𝒜 ⊆ S.powerset) (i : α) :
    𝒜.memberSubfamily i ⊆ (S.erase i).powerset := by
  intro x hx
  rw [mem_memberSubfamily] at hx
  rw [mem_powerset]
  intro e he
  exact mem_erase.2 ⟨fun h' => hx.2 (h' ▸ he),
    mem_powerset.1 (h hx.1) (mem_insert_of_mem he)⟩

/-- The lower section of the neighbourhood. -/
lemma nonMember_nbhd {S : Finset α} {𝒜 : Finset (Finset α)} (h : 𝒜 ⊆ S.powerset) (i : α) :
    (nbhd S 𝒜).nonMemberSubfamily i =
      nbhd (S.erase i) (𝒜.nonMemberSubfamily i) ∪ 𝒜.memberSubfamily i := by
  ext y
  simp only [mem_nonMemberSubfamily, mem_union, mem_memberSubfamily, mem_nbhd]
  constructor
  · rintro ⟨⟨hyS, x, hx, hxy⟩, hiy⟩
    by_cases hix : i ∈ x
    · right
      have hx' : x = insert i (x.erase i) := (insert_erase hix).symm
      rw [hx', adj_insert_left_iff (notMem_erase i x) hiy] at hxy
      rw [← hxy, ← hx']
      exact ⟨hx, notMem_erase i x⟩
    · left
      refine ⟨?_, x, ⟨hx, hix⟩, hxy⟩
      intro e he
      exact mem_erase.2 ⟨fun h' => hiy (h' ▸ he), hyS he⟩
  · rintro (⟨hyS, x, ⟨hx, hix⟩, hxy⟩ | ⟨hy, hiy⟩)
    · refine ⟨⟨hyS.trans (erase_subset _ _), x, hx, hxy⟩, fun h' => ?_⟩
      exact (mem_erase.1 (hyS h')).1 rfl
    · refine ⟨⟨?_, insert i y, hy, ?_⟩, hiy⟩
      · exact (subset_insert _ _).trans (mem_powerset.1 (h hy))
      · rw [adj_comm]; exact adj_insert hiy

/-- The upper section of the neighbourhood. -/
lemma member_nbhd {S : Finset α} {𝒜 : Finset (Finset α)} (h : 𝒜 ⊆ S.powerset) {i : α}
    (hi : i ∈ S) :
    (nbhd S 𝒜).memberSubfamily i =
      nbhd (S.erase i) (𝒜.memberSubfamily i) ∪ 𝒜.nonMemberSubfamily i := by
  ext y
  simp only [mem_nonMemberSubfamily, mem_union, mem_memberSubfamily, mem_nbhd]
  constructor
  · rintro ⟨⟨hyS, x, hx, hxy⟩, hiy⟩
    by_cases hix : i ∈ x
    · left
      have hx' : x = insert i (x.erase i) := (insert_erase hix).symm
      rw [hx', adj_insert_insert_iff (notMem_erase i x) hiy] at hxy
      refine ⟨?_, x.erase i, ⟨by rwa [insert_erase hix], notMem_erase i x⟩, hxy⟩
      intro e he
      exact mem_erase.2 ⟨fun h' => hiy (h' ▸ he), hyS (mem_insert_of_mem he)⟩
    · right
      rw [adj_comm, adj_insert_left_iff hiy hix] at hxy
      exact ⟨hxy ▸ hx, hiy⟩
  · rintro (⟨hyS, x, ⟨hx, hix⟩, hxy⟩ | ⟨hy, hiy⟩)
    · have hiy : i ∉ y := fun h' => (mem_erase.1 (hyS h')).1 rfl
      refine ⟨⟨?_, insert i x, hx, (adj_insert_insert_iff hix hiy).2 hxy⟩, hiy⟩
      exact insert_subset hi (hyS.trans (erase_subset _ _))
    · refine ⟨⟨insert_subset hi (mem_powerset.1 (h hy)), y, hy, adj_insert hiy⟩, hiy⟩

lemma card_sections (i : α) (𝒜 : Finset (Finset α)) :
    𝒜.card = (𝒜.nonMemberSubfamily i).card + (𝒜.memberSubfamily i).card := by
  rw [← card_memberSubfamily_add_card_nonMemberSubfamily i 𝒜, add_comm]

end HarperVertex
