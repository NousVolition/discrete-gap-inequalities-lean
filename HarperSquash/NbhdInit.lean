import HarperSquash.Basic

/-!
# Stage 2. The neighbourhood of an initial segment is an initial segment
-/

open Finset

namespace HarperVertex

open scoped Classical symmDiff

variable {α : Type*} [LinearOrder α]

/-- The lexicographic step: if `w` comes before `insert a c` (both of the same size) then
removing the largest element of `w` gives `c` itself or a set before `c`. -/
lemma erase_max_lex {w c : Finset α} {a : α} (hac : a ∉ c) (hlex : LexBefore w (insert a c))
    (hcard : w.card = c.card + 1) (hwne : w.Nonempty) :
    w.erase (w.max' hwne) = c ∨ LexBefore (w.erase (w.max' hwne)) c := by
  obtain ⟨d, hdw, hdz, hd⟩ := hlex
  have hdm : d ≤ w.max' hwne := le_max' _ _ hdw
  have hmw : w.max' hwne ∈ w := max'_mem _ _
  have hc'card : (w.erase (w.max' hwne)).card = c.card := by
    rw [card_erase_of_mem hmw]; omega
  have had : a ≠ d := fun h => hdz (h ▸ mem_insert_self a c)
  rcases lt_or_gt_of_ne had with had | hda
  · right
    have haw : a ∈ w := (hd a had).2 (mem_insert_self a c)
    have ham : a ≠ w.max' hwne := ne_of_lt (lt_of_lt_of_le had hdm)
    refine ⟨a, mem_erase.2 ⟨ham, haw⟩, hac, fun e he => ?_⟩
    have hem : e ≠ w.max' hwne := ne_of_lt (he.trans (lt_of_lt_of_le had hdm))
    have hea : e ≠ a := ne_of_lt he
    have := hd e (he.trans had)
    simp only [mem_erase, ne_eq, hem, not_false_eq_true, true_and, this, mem_insert, hea, false_or]
  · rcases lt_or_eq_of_le hdm with hdm' | hdm'
    · right
      refine ⟨d, mem_erase.2 ⟨ne_of_lt hdm', hdw⟩, fun h => hdz (mem_insert_of_mem h),
        fun e he => ?_⟩
      have hem : e ≠ w.max' hwne := ne_of_lt (he.trans hdm')
      have hea : e ≠ a := ne_of_lt (he.trans hda)
      have := hd e he
      simp only [mem_erase, ne_eq, hem, not_false_eq_true, true_and, this, mem_insert, hea,
        false_or]
    · left
      apply eq_of_subset_of_card_le _ (le_of_eq hc'card.symm)
      intro e he
      obtain ⟨hem, hew⟩ := mem_erase.1 he
      have hle : e ≤ d := hdm' ▸ le_max' _ _ hew
      have hel : e < d := lt_of_le_of_ne hle (hdm' ▸ hem)
      have := (hd e hel).1 hew
      exact (mem_insert.1 this).resolve_left (ne_of_lt (hel.trans hda))

/-- **Stage 2.** The neighbourhood of an initial segment of the simplicial order is again an
initial segment. -/
theorem isInit_nbhd {S : Finset α} {C : Finset (Finset α)} (hC : IsInit S C) :
    IsInit S (nbhd S C) := by
  refine ⟨nbhd_subset_powerset _ _, ?_⟩
  intro z hz w hwS hwz
  rw [mem_nbhd] at hz ⊢
  obtain ⟨hzS, c, hc, hcz⟩ := hz
  refine ⟨hwS, ?_⟩
  have small : ∀ u, u ⊆ S → u.card < c.card → u ∈ C :=
    fun u hu h => hC.2 c hc u hu (before_of_card_lt h)
  by_cases hwc : w.card ≤ c.card
  · by_cases hw : w = c
    · exact ⟨c, hc, hw ▸ adj_refl _⟩
    rcases lt_or_eq_of_le hwc with hlt | heq
    · exact ⟨w, small w hwS hlt, adj_refl w⟩
    · have hne : w.Nonempty := by
        rw [nonempty_iff_ne_empty]
        rintro rfl
        rw [card_empty, eq_comm, card_eq_zero] at heq
        exact hw heq.symm
      obtain ⟨a, ha⟩ := hne
      have hpos : 0 < w.card := card_pos.2 ⟨a, ha⟩
      refine ⟨w.erase a, small _ ((erase_subset _ _).trans hwS) ?_, ?_⟩
      · rw [card_erase_of_mem ha]; omega
      · rw [adj_comm]; exact adj_erase ha
  · push Not at hwc
    have hz1 := card_le_succ_of_adj hcz
    have hwz' := card_le_of_before hwz
    have hzcard : z.card = c.card + 1 := by omega
    have hwcard : w.card = c.card + 1 := by omega
    have hlex : LexBefore w z := by
      rcases hwz with h | ⟨-, h⟩
      · omega
      · exact h
    rcases adj_cases hcz with rfl | ⟨a, hac, rfl⟩ | ⟨a, hac, rfl⟩
    · omega
    · have hwne : w.Nonempty := card_pos.1 (by omega)
      have hmw : w.max' hwne ∈ w := max'_mem _ _
      refine ⟨w.erase (w.max' hwne), ?_, by rw [adj_comm]; exact adj_erase hmw⟩
      have hcard' : (w.erase (w.max' hwne)).card = c.card := by
        rw [card_erase_of_mem hmw]; omega
      rcases erase_max_lex hac hlex hwcard hwne with h | h
      · exact h ▸ hc
      · exact hC.2 c hc _ ((erase_subset _ _).trans hwS) (Or.inr ⟨hcard', h⟩)
    · rw [card_erase_of_mem hac] at hzcard
      have : 0 < c.card := card_pos.2 ⟨a, hac⟩
      omega

end HarperVertex
