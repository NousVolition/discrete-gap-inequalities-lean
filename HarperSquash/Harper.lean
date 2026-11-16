import HarperSquash.Classify

/-!
# Stage 4. Harper's vertex-isoperimetric theorem on the cube

Squash a family until it is squashed in every direction (the weight goes down at every real step,
so this stops), then use Stage 3. The smaller cubes needed by each squash are handled by
induction on the ground set.
-/

open Finset

namespace HarperVertex

open scoped Classical

variable {α : Type*} [LinearOrder α]

/-- Harper's inequality holds in the cube on every finite ground set. -/
theorem harperAt (S : Finset α) : HarperAt S := by
  refine Finset.strongInduction (p := fun S => HarperAt S) (fun S ih => ?_) S
  intro 𝒜 h𝒜
  set K := S.powerset.powerset.filter
    (fun 𝓑 => 𝓑.card = 𝒜.card ∧ (nbhd S 𝓑).card ≤ (nbhd S 𝒜).card) with hKdef
  have hK : 𝒜 ∈ K := by simp [K, h𝒜]
  obtain ⟨𝓑, h𝓑K, hmin⟩ := exists_min_image K (weight S) ⟨𝒜, hK⟩
  simp only [K, mem_filter, mem_powerset] at h𝓑K
  obtain ⟨h𝓑, hc, hn⟩ := h𝓑K
  have hsq : SquashedAll S 𝓑 := by
    intro i hi
    by_contra hnot
    have hT : HarperAt (S.erase i) := ih _ (erase_ssubset hi)
    have hmem : squash S i 𝓑 ∈ K := by
      simp only [K, mem_filter, mem_powerset]
      exact ⟨squash_subset hi 𝓑, (card_squash h𝓑 i).trans hc,
        (card_nbhd_squash_le h𝓑 hi hT).trans hn⟩
    exact absurd (hmin _ hmem) (not_le.2 (weight_squash_lt h𝓑 hi hnot))
  calc (nbhd S (initSeg S 𝒜.card)).card ≤ (nbhd S 𝓑).card :=
        card_nbhd_le_of_squashedAll h𝓑 hsq (isInit_initSeg S _)
          (by rw [card_initSeg (card_le_card h𝒜), hc])
    _ ≤ _ := hn

/-- **Harper's vertex-isoperimetric theorem** (cube on a finite ground set `S`). Among all
families of subsets of `S` with a given number of members, an initial segment of the simplicial
order has the smallest neighbourhood. -/
theorem harper {S : Finset α} {𝒜 C : Finset (Finset α)} (h𝒜 : 𝒜 ⊆ S.powerset) (hC : IsInit S C)
    (hcard : C.card = 𝒜.card) : (nbhd S C).card ≤ (nbhd S 𝒜).card := by
  have := harperAt S 𝒜 h𝒜
  rwa [init_eq_of_card_eq hC (isInit_initSeg S 𝒜.card)
    (by rw [hcard, card_initSeg (card_le_card h𝒜)])]

/-- **Harper's theorem on the `n`-cube.** For every family `𝒜` of subsets of `{0, …, n-1}`,
the neighbourhood of `𝒜` is at least as large as the neighbourhood of the initial segment of
the simplicial order with the same number of sets. -/
theorem harper_cube (n : ℕ) (𝒜 : Finset (Finset (Fin n))) :
    (nbhd (univ : Finset (Fin n)) (initSeg univ 𝒜.card)).card ≤ (nbhd univ 𝒜).card :=
  harperAt univ 𝒜 (fun x _ => mem_powerset.2 (subset_univ x))

/-! ## The ball form -/

/-- The ball of radius `r` about the empty set: all subsets of `S` with at most `r` elements. -/
noncomputable def ball (S : Finset α) (r : ℕ) : Finset (Finset α) :=
  S.powerset.filter (fun x => x.card ≤ r)

lemma isInit_ball (S : Finset α) (r : ℕ) : IsInit S (ball S r) := by
  refine ⟨filter_subset _ _, fun x hx y hy hyx => ?_⟩
  simp only [ball, mem_filter, mem_powerset] at hx ⊢
  exact ⟨hy, (card_le_of_before hyx).trans hx.2⟩

lemma ball_succ_subset_nbhd (S : Finset α) (r : ℕ) : ball S (r + 1) ⊆ nbhd S (ball S r) := by
  intro y hy
  simp only [ball, mem_filter, mem_powerset] at hy
  rw [mem_nbhd]
  refine ⟨hy.1, ?_⟩
  by_cases hyr : y.card ≤ r
  · exact ⟨y, by simp [ball, hy.1, hyr], adj_refl y⟩
  · obtain ⟨a, ha⟩ := card_pos.1 (by omega : 0 < y.card)
    refine ⟨y.erase a, ?_, ?_⟩
    · simp only [ball, mem_filter, mem_powerset]
      exact ⟨(erase_subset _ _).trans hy.1, by rw [card_erase_of_mem ha]; omega⟩
    · rw [adj_comm]; exact adj_erase ha

omit [LinearOrder α] in
lemma card_ball (S : Finset α) (r : ℕ) :
    (ball S r).card = ∑ j ∈ range (r + 1), S.card.choose j := by
  rw [card_eq_sum_card_fiberwise (f := card) (t := range (r + 1))]
  · apply sum_congr rfl
    intro j hj
    rw [← card_powersetCard j S, powersetCard_eq_filter]
    congr 1
    ext x
    simp only [ball, mem_filter, mem_powerset, mem_range] at hj ⊢
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by omega⟩, h2⟩
  · intro x hx
    simp only [ball, coe_filter, Set.mem_ofPred_eq, mem_powerset] at hx
    simp only [coe_range, Set.mem_Iio]
    omega

/-- **Harper's theorem, ball form.** A family with at least as many sets as the ball of radius `r`
has a neighbourhood at least as large as the ball of radius `r + 1`. -/
theorem harper_ball {S : Finset α} {𝒜 : Finset (Finset α)} (h𝒜 : 𝒜 ⊆ S.powerset) {r : ℕ}
    (hr : (ball S r).card ≤ 𝒜.card) : (ball S (r + 1)).card ≤ (nbhd S 𝒜).card := by
  set I := initSeg S 𝒜.card
  have hI : IsInit S I := isInit_initSeg S _
  have hIc : I.card = 𝒜.card := card_initSeg (card_le_card h𝒜)
  have hsub : ball S r ⊆ I := by
    rcases init_nested (isInit_ball S r) hI with h | h
    · exact h
    · exact (eq_of_subset_of_card_le h (hr.trans hIc.ge)).ge
  calc (ball S (r + 1)).card ≤ (nbhd S (ball S r)).card := card_le_card (ball_succ_subset_nbhd S r)
    _ ≤ (nbhd S I).card := card_le_card (nbhd_mono hsub)
    _ ≤ (nbhd S 𝒜).card := harperAt S 𝒜 h𝒜

/-- **Ball form with binomial sums.** If a family of subsets of an `n`-element set has at least
`∑_{j ≤ r} (n choose j)` members, its neighbourhood has at least `∑_{j ≤ r+1} (n choose j)`. -/
theorem harper_ball_choose {S : Finset α} {𝒜 : Finset (Finset α)} (h𝒜 : 𝒜 ⊆ S.powerset) {r : ℕ}
    (hr : ∑ j ∈ range (r + 1), S.card.choose j ≤ 𝒜.card) :
    ∑ j ∈ range (r + 2), S.card.choose j ≤ (nbhd S 𝒜).card := by
  rw [← card_ball] at hr ⊢
  exact harper_ball h𝒜 hr

end HarperVertex
