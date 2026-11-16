import HarperSquash.Squash

/-!
# Stage 3. Families squashed in every direction

A family whose two halves in every direction `i` are initial segments is either an initial
segment itself, or it is the one exceptional family: an initial segment ending at `x`, with `x`
taken out and its complement `S \ x` put in, where `S \ x` comes right after `x`. In that case
the neighbourhood already contains the neighbourhood of the initial segment of the same size.
-/

open Finset

namespace HarperVertex

open scoped Classical symmDiff

variable {α : Type*} [LinearOrder α]

/-- `𝓑` is squashed in every direction of the cube on `S`. -/
def SquashedAll (S : Finset α) (𝓑 : Finset (Finset α)) : Prop :=
  ∀ i ∈ S, IsInit (S.erase i) (𝓑.nonMemberSubfamily i) ∧ IsInit (S.erase i) (𝓑.memberSubfamily i)

/-- In a family squashed in every direction, a missing set that comes before a member is the
complement of that member. -/
lemma eq_sdiff_of_squashedAll {S : Finset α} {𝓑 : Finset (Finset α)} (hsq : SquashedAll S 𝓑)
    {x y : Finset α} (hxS : x ⊆ S) (hx : x ∉ 𝓑) (hy : y ∈ 𝓑) (hxy : Before x y) :
    x = S \ y := by
  ext e
  rw [mem_sdiff]
  by_cases heS : e ∈ S
  · simp only [heS, true_and]
    by_contra hcon
    have hiff : e ∈ x ↔ e ∈ y := by tauto
    obtain ⟨hlo, hhi⟩ := hsq e heS
    have hxe : ∀ u, u ⊆ S → e ∉ u → u ⊆ S.erase e := fun u hu heu f hf =>
      mem_erase.2 ⟨fun h' => heu (h' ▸ hf), hu hf⟩
    by_cases hex : e ∈ x
    · have hey : e ∈ y := hiff.1 hex
      have hy' : y.erase e ∈ 𝓑.memberSubfamily e :=
        mem_memberSubfamily.2 ⟨by rwa [insert_erase hey], notMem_erase e y⟩
      have hx' := hhi.2 _ hy' (x.erase e) (hxe _ ((erase_subset _ _).trans hxS) (notMem_erase e x))
        ((before_erase_iff hex hey).2 hxy)
      rw [mem_memberSubfamily, insert_erase hex] at hx'
      exact hx hx'.1
    · have hey : e ∉ y := fun h' => hex (hiff.2 h')
      have hy' : y ∈ 𝓑.nonMemberSubfamily e := mem_nonMemberSubfamily.2 ⟨hy, hey⟩
      have hx' := hlo.2 _ hy' x (hxe x hxS hex) hxy
      exact hx (mem_nonMemberSubfamily.1 hx').1
  · simp only [heS, false_and, iff_false]
    exact fun h' => heS (hxS h')

/-- If `S \ ∅` comes right after `∅`, then `S` has at most one element. -/
lemma card_le_one_of_succ_empty {S : Finset α}
    (hsucc : ∀ w, w ⊆ S → Before ∅ w → Before w (S \ ∅) → False) : S.card ≤ 1 := by
  by_contra hS
  push Not at hS
  obtain ⟨s, hs⟩ := card_pos.1 (by omega : 0 < S.card)
  apply hsucc {s} (singleton_subset_iff.2 hs) (before_of_card_lt (by simp))
  rw [sdiff_empty]
  exact before_of_card_lt (by rw [card_singleton]; omega)

/-- The exceptional case: every neighbour of `x` is a neighbour of `S \ x` or of a set before `x`. -/
lemma exceptional_adj {S x : Finset α} (hxS : x ⊆ S) (hxy : Before x (S \ x))
    (hsucc : ∀ w, w ⊆ S → Before x w → Before w (S \ x) → False) {z : Finset α}
    (hz : Adj x z) (hzS : z ⊆ S) :
    Adj (S \ x) z ∨ ∃ w, w ⊆ S ∧ Before w x ∧ Adj w z := by
  rcases adj_cases hz with rfl | ⟨a, hax, rfl⟩ | ⟨b, hbx, rfl⟩
  · by_cases hx : x.Nonempty
    · obtain ⟨b, hb⟩ := hx
      right
      exact ⟨x.erase b, (erase_subset _ _).trans hxS,
        before_of_card_lt (card_erase_lt_of_mem hb), by rw [adj_comm]; exact adj_erase hb⟩
    · rw [not_nonempty_iff_eq_empty] at hx
      subst hx
      left
      have := card_le_one_of_succ_empty hsucc
      unfold Adj
      have e : (S \ ∅) ∆ (∅ : Finset α) = S := by ext; simp [mem_symmDiff]
      rwa [e]
  · have haS : a ∈ S := hzS (mem_insert_self a x)
    by_cases hb : ∃ b ∈ x, a < b
    · obtain ⟨b, hb, hab⟩ := hb
      right
      have hba : b ≠ a := ne_of_gt hab
      have hcard : (insert a (x.erase b)).card = x.card := by
        rw [card_insert_of_notMem (fun h' => hax (mem_of_mem_erase h')), card_erase_of_mem hb]
        have := card_pos.2 ⟨b, hb⟩
        omega
      refine ⟨insert a (x.erase b), insert_subset haS ((erase_subset _ _).trans hxS),
        Or.inr ⟨hcard, a, mem_insert_self a _, hax, fun e he => ?_⟩, ?_⟩
      · have h1 : e ≠ a := ne_of_lt he
        have h2 : e ≠ b := ne_of_lt (he.trans hab)
        simp [mem_insert, mem_erase, h1, h2]
      · have hbw : b ∉ insert a (x.erase b) := by simp [hba]
        have heq : insert a x = insert b (insert a (x.erase b)) := by
          rw [insert_comm, insert_erase hb]
        rw [heq]
        exact adj_insert hbw
    · push Not at hb
      by_cases hx : x = ∅
      · subst hx
        left
        have h1 := card_le_one_of_succ_empty hsucc
        have hSa : S = {a} := by
          apply eq_singleton_iff_unique_mem.2 ⟨haS, fun b hb' => card_le_one.1 h1 b hb' a haS⟩
        rw [sdiff_empty, hSa]
        simpa using adj_refl ({a} : Finset α)
      · have hSne : S.Nonempty := ⟨a, haS⟩
        set m := S.max' hSne with hm
        have hmS : m ∈ S := max'_mem _ _
        have hmx : m ∉ x := by
          intro h'
          have h1 := hb m h'
          have h2 : a ≤ m := le_max' _ _ haS
          exact hax (le_antisymm h1 h2 ▸ h')
        obtain ⟨b0, hb0⟩ := nonempty_iff_ne_empty.2 hx
        -- a set strictly between `x` and `S \ x`, used to reach a contradiction
        have hw : ∀ b ∈ x, Before x (insert m (x.erase b)) ∧ (insert m (x.erase b)).card = x.card
            ∧ insert m (x.erase b) ⊆ S := by
          intro b hb'
          have hbm : b ≠ m := fun h' => hmx (h' ▸ hb')
          have hbm' : b < m := lt_of_le_of_ne (le_max' _ _ (hxS hb')) hbm
          have hcard : (insert m (x.erase b)).card = x.card := by
            rw [card_insert_of_notMem (fun h' => hmx (mem_of_mem_erase h')),
              card_erase_of_mem hb']
            have := card_pos.2 ⟨b, hb'⟩
            omega
          refine ⟨Or.inr ⟨hcard.symm, b, hb', ?_, fun e he => ?_⟩, hcard,
            insert_subset hmS ((erase_subset _ _).trans hxS)⟩
          · simp [hbm]
          · have h1 : e ≠ b := ne_of_lt he
            have h2 : e ≠ m := ne_of_lt (he.trans hbm')
            simp [mem_insert, mem_erase, h1, h2]
        rcases hxy with hlt | ⟨heq, d, hdx, hdS, hd⟩
        · obtain ⟨h1, h2, h3⟩ := hw b0 hb0
          exact absurd (hsucc _ h3 h1 (before_of_card_lt (h2 ▸ hlt))) id
        · by_cases hxd : ∃ b ∈ x, b ≠ d
          · obtain ⟨b, hb', hbd⟩ := hxd
            obtain ⟨h1, h2, h3⟩ := hw b hb'
            refine absurd (hsucc _ h3 h1 (Or.inr ⟨h2.trans heq, d, ?_, hdS, fun e he => ?_⟩)) id
            · simp [mem_insert, mem_erase, hbd.symm, hdx]
            · have heS : e ∉ S := by
                intro heS
                have := hd e he
                rw [mem_sdiff] at this
                tauto
              constructor
              · intro h'; exact absurd (h3 h') heS
              · intro h'; exact absurd (mem_sdiff.1 h').1 heS
          · push Not at hxd
            have hxsing : x = {d} := eq_singleton_iff_unique_mem.2 ⟨hdx, hxd⟩
            have haSx : a ∈ S \ x := mem_sdiff.2 ⟨haS, hax⟩
            have hc1 : (S \ x).card = 1 := by rw [← heq, hxsing, card_singleton]
            obtain ⟨c, hc⟩ := card_eq_one.1 hc1
            have hca : S \ x = {a} := by
              rw [hc] at haSx ⊢; rw [mem_singleton.1 haSx]
            left
            rw [hca, hxsing]
            have hda : d ∉ ({a} : Finset α) := by
              intro h'
              rw [mem_singleton] at h'
              exact hax (hxsing ▸ (h' ▸ mem_singleton_self d))
            have : insert a ({d} : Finset α) = insert d {a} := by
              ext e; simp [or_comm]
            rw [this]
            exact adj_insert hda
  · right
    exact ⟨x.erase b, (erase_subset _ _).trans hxS, before_of_card_lt (card_erase_lt_of_mem hbx),
      adj_refl _⟩

/-- **Stage 3 (classification).** A family squashed in every direction is an initial segment, or
it is the exceptional family `{w : w before x} ∪ {S \ x}` where `S \ x` comes right after `x`. -/
theorem squashedAll_classify {S : Finset α} {𝓑 : Finset (Finset α)} (h : 𝓑 ⊆ S.powerset)
    (hsq : SquashedAll S 𝓑) :
    IsInit S 𝓑 ∨ ∃ x, x ⊆ S ∧ Before x (S \ x) ∧
      (∀ w, w ⊆ S → Before x w → Before w (S \ x) → False) ∧
      𝓑 = insert (S \ x) (S.powerset.filter (fun w => Before w x)) := by
  by_cases hI : IsInit S 𝓑
  · exact Or.inl hI
  right
  unfold IsInit at hI
  push Not at hI
  obtain ⟨y, hy, x, hxS, hxy, hx⟩ := hI h
  have hyS : y ⊆ S := mem_powerset.1 (h hy)
  have pair := fun {u v} (huS : u ⊆ S) (hu : u ∉ 𝓑) (hv : v ∈ 𝓑) (huv : Before u v) =>
    eq_sdiff_of_squashedAll hsq huS hu hv huv
  have hxeq : x = S \ y := pair hxS hx hy hxy
  have hyeq : y = S \ x := by rw [hxeq, Finset.sdiff_sdiff_eq_self hyS]
  have below : ∀ w, w ⊆ S → Before w x → w ∈ 𝓑 := by
    intro w hwS hwx
    by_contra hw
    have := pair hwS hw hy (before_trans hwx hxy)
    rw [← hxeq] at this
    exact before_irrefl x (this ▸ hwx)
  have upper : ∀ w ∈ 𝓑, w = y ∨ Before w x := by
    intro w hw
    have hwx : w ≠ x := fun e => hx (e ▸ hw)
    rcases before_total hwx with h' | h'
    · exact Or.inr h'
    · left
      have := pair hxS hx hw h'
      rw [hyeq, this, Finset.sdiff_sdiff_eq_self (mem_powerset.1 (h hw))]
  refine ⟨x, hxS, hyeq ▸ hxy, fun w hwS h1 h2 => ?_, ?_⟩
  · rw [← hyeq] at h2
    have hw : w ∈ 𝓑 := by
      by_contra hw
      have := pair hwS hw hy h2
      rw [← hxeq] at this
      exact before_irrefl x (this ▸ h1)
    rcases upper w hw with e | e
    · exact before_irrefl y (e ▸ h2)
    · exact before_asymm h1 e
  · rw [← hyeq]
    ext w
    simp only [mem_insert, mem_filter, mem_powerset]
    constructor
    · intro hw
      rcases upper w hw with e | e
      · exact Or.inl e
      · exact Or.inr ⟨mem_powerset.1 (h hw), e⟩
    · rintro (rfl | ⟨hwS, hwx⟩)
      · exact hy
      · exact below w hwS hwx

/-- **Stage 3 (conclusion).** For a family squashed in every direction, the neighbourhood is at
least as large as the neighbourhood of the initial segment of the same size. -/
theorem card_nbhd_le_of_squashedAll {S : Finset α} {𝓑 : Finset (Finset α)} (h : 𝓑 ⊆ S.powerset)
    (hsq : SquashedAll S 𝓑) {C : Finset (Finset α)} (hC : IsInit S C) (hcard : C.card = 𝓑.card) :
    (nbhd S C).card ≤ (nbhd S 𝓑).card := by
  rcases squashedAll_classify h hsq with hI | ⟨x, hxS, hxy, hsucc, hB⟩
  · rw [init_eq_of_card_eq hC hI hcard]
  set D := S.powerset.filter (fun w => Before w x) with hD
  have hxD : x ∉ D := by simp [hD, before_irrefl]
  have hyD : S \ x ∉ D := by
    simp only [hD, mem_filter, not_and]
    exact fun _ h' => before_asymm h' hxy
  have hC' : IsInit S (insert x D) := by
    refine ⟨insert_subset (mem_powerset.2 hxS) (filter_subset _ _), fun u hu w hwS hwu => ?_⟩
    rw [mem_insert] at hu ⊢
    right
    rcases hu with rfl | hu
    · simp [hD, hwS, hwu]
    · simp only [hD, mem_filter, mem_powerset] at hu ⊢
      exact ⟨hwS, before_trans hwu hu.2⟩
  have hcard' : (insert x D).card = 𝓑.card := by
    rw [hB, card_insert_of_notMem hxD, card_insert_of_notMem hyD]
  rw [init_eq_of_card_eq hC hC' (hcard.trans hcard'.symm)]
  apply card_le_card
  intro z hz
  rw [mem_nbhd] at hz ⊢
  obtain ⟨hzS, u, hu, huz⟩ := hz
  refine ⟨hzS, ?_⟩
  rw [mem_insert] at hu
  rcases hu with rfl | hu
  · rcases exceptional_adj hxS hxy hsucc huz hzS with h' | ⟨w, hwS, hwx, hwz⟩
    · exact ⟨S \ u, by rw [hB]; exact mem_insert_self _ _, h'⟩
    · exact ⟨w, by rw [hB]; exact mem_insert_of_mem (by simp [hD, hwS, hwx]), hwz⟩
  · exact ⟨u, by rw [hB]; exact mem_insert_of_mem hu, huz⟩

end HarperVertex
