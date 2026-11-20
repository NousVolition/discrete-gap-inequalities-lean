import MathieuBase
import PlaygroundGolay

/-! # Generators and order of the permutation group of the extended Golay code

The tables give one representative for each possible image of the next base
point. The seven successive group sizes follow by splitting off this image.
-/

namespace GolayMathieu

open GolayMatrixDistance LeechLattice LeechCodeCounts LeechSymmetry

abbrev RepIndex := Fin 129

def pointMap (r : RepIndex) (i : Point) : Point :=
  Fin.ofNat 24 ((MathieuData.perms.getD r.val #[]).getD i.val 0)

def message (r : RepIndex) (i : Fin 12) : Fin 4096 :=
  Fin.ofNat 4096 ((MathieuData.messages.getD r.val #[]).getD i.val 0)

def slot (k : Fin 7) (i : Point) : RepIndex :=
  Fin.ofNat 129 ((MathieuData.slots.getD k.val #[]).getD i.val 0)

theorem pointMap_injective : ∀ r, Function.Injective (pointMap r) := by decide +kernel

noncomputable def rep (r : RepIndex) : Perm :=
  Equiv.ofBijective _ ⟨pointMap_injective r, Finite.surjective_of_injective (pointMap_injective r)⟩

theorem rep_rows : ∀ (r : RepIndex) (i : Fin 12) (j : Point),
    word (genMasks.getD i.val 0) (pointMap r j) = word (encodeNat (message r i).val) j := by
  decide +kernel

theorem perm_of_forward (p : Perm) (h : ∀ w, IsGolayWord w → IsGolayWord (fun i => w (p i))) :
    IsCodePermutation p := by
  let f (w : Codeword) : Codeword := ⟨fun i => w.val (p i), h w.val w.property⟩
  have hi : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    funext j
    obtain ⟨i, rfl⟩ := p.surjective j
    exact congrArg (fun w : Codeword => w.val i) he
  intro w
  refine ⟨h w, fun hw => ?_⟩
  obtain ⟨u, hu⟩ := Finite.surjective_of_injective hi ⟨_, hw⟩
  have he : u.val = w := by
    funext j
    obtain ⟨i, rfl⟩ := p.surjective j
    exact congrArg (fun v : Codeword => v.val i) hu
  exact he ▸ u.property

theorem rep_code (r : RepIndex) : IsCodePermutation (rep r) := by
  apply perm_of_forward
  rintro _ ⟨m, _, rfl⟩
  change IsGolayWord (fun j => word (PlaygroundGolay.encodeWith genMasks m) (pointMap r j))
  apply PlaygroundGolay.encodeWith_property genMasks m (fun w => IsGolayWord (fun j => w (pointMap r j)))
  · exact isGolayWord_false
  · intro u v hu hv; exact isGolayWord_xor hu hv
  · intro i hi
    exact ⟨(message r ⟨i, hi⟩).val, (message r ⟨i, hi⟩).isLt,
      funext (fun j => (rep_rows r ⟨i, hi⟩ j).symm)⟩

def level (k : Nat) : Subgroup Perm where
  carrier := {p | IsCodePermutation p ∧ Fixes k p}
  one_mem' := ⟨fun _ => Iff.rfl, fun _ _ => rfl⟩
  mul_mem' := by
    rintro p q ⟨hp, fp⟩ ⟨hq, fq⟩
    exact ⟨fun w => (hp w).trans (hq _), fun j hj => by simp [Equiv.Perm.mul_apply, fp j hj, fq j hj]⟩
  inv_mem' := by
    rintro p ⟨hp, fp⟩
    refine ⟨codePermutation_symm p hp, fun j hj => ?_⟩
    change p.symm (base j) = base j
    exact p.symm_apply_eq.mpr (fp j hj).symm

theorem level_zero_iff (p : Perm) : p ∈ level 0 ↔ IsCodePermutation p :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ hj => (Nat.not_lt_zero _ hj).elim⟩⟩

abbrev ImageAt (k : Fin 7) := {j : Point // allowed k j = true}

theorem rep_hits : ∀ (k : Fin 7) (j : Point), allowed k j = true →
    pointMap (slot k j) (base k.val) = j := by decide +kernel

theorem rep_prefix : ∀ (k : Fin 7) (j : Point), allowed k j = true →
    ∀ i : Fin 7, i.val < k.val → pointMap (slot k j) (base i.val) = base i.val := by decide +kernel

noncomputable def sectionAt (k : Fin 7) (y : ImageAt k) : level k.val :=
  ⟨rep (slot k y.val), rep_code _, fun i hi => rep_prefix k y.val y.property ⟨i, by omega⟩ hi⟩

def imageAt (k : Fin 7) (g : level k.val) : ImageAt k :=
  ⟨g.val (base k.val), allowed_image k g.val g.property.1 g.property.2⟩

theorem sectionAt_hits (k : Fin 7) (y : ImageAt k) : (sectionAt k y).val (base k.val) = y.val :=
  rep_hits k y.val y.property

noncomputable def residual (k : Fin 7) (g : level k.val) : level (k.val+1) := by
  let s := sectionAt k (imageAt k g)
  let h := s⁻¹ * g
  refine ⟨h.val, h.property.1, ?_⟩
  intro i hi
  by_cases he : i = k.val
  · subst i
    change s.val.symm (g.val (base k.val)) = base k.val
    exact s.val.symm_apply_eq.mpr (sectionAt_hits k (imageAt k g)).symm
  · exact h.property.2 i (by omega)

noncomputable def assemble (k : Fin 7) (y : ImageAt k) (h : level (k.val+1)) : level k.val :=
  sectionAt k y * ⟨h.val, h.property.1, fun i hi => h.property.2 i (by omega)⟩

theorem image_assemble (k : Fin 7) (y : ImageAt k) (h : level (k.val+1)) :
    imageAt k (assemble k y h) = y := by
  apply Subtype.ext
  change (sectionAt k y).val (h.val (base k.val)) = y.val
  rw [h.property.2 _ (by omega)]
  exact sectionAt_hits k y

noncomputable def splitLevel (k : Fin 7) : level k.val ≃ ImageAt k × level (k.val+1) where
  toFun g := (imageAt k g, residual k g)
  invFun pair := assemble k pair.1 pair.2
  left_inv g := by
    apply Subtype.ext
    change (sectionAt k (imageAt k g)).val * ((sectionAt k (imageAt k g)).val⁻¹ * g.val) = g.val
    exact mul_inv_cancel_left _ _
  right_inv := by
    rintro ⟨y, h⟩
    refine @Prod.ext (ImageAt k) (↥(level (k.val+1))) (imageAt k (assemble k y h), residual k (assemble k y h))
      (y, h) (image_assemble k y h) ?_
    apply Subtype.ext
    change (sectionAt k (imageAt k (assemble k y h))).val⁻¹ *
      ((sectionAt k y).val * h.val) = h.val
    rw [image_assemble, inv_mul_cancel_left]

def orbitLength (k : Fin 7) : Nat := (#[24,23,22,21,20,3,16] : Array Nat).getD k.val 0

theorem image_card (k : Fin 7) : Nat.card (ImageAt k) = orbitLength k := by
  rw [Nat.card_eq_fintype_card]
  have checked : ∀ j : Fin 7, Fintype.card (ImageAt j) = orbitLength j := by decide +kernel
  exact checked k

theorem card_step (k : Fin 7) : Nat.card (level k.val) = orbitLength k * Nat.card (level (k.val+1)) := by
  rw [Nat.card_congr (splitLevel k), Nat.card_prod, image_card]

theorem card_last : Nat.card (level 7) = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  exact ⟨1, fun g => Subtype.ext (fixed_base _ g.property.1 g.property.2)⟩

/-- The permutation group of this extended binary Golay code has order 244,823,040. -/
theorem card_mathieu : Nat.card (level 0) = 244823040 := by
  have h0 : Nat.card (level 0) = 24 * Nat.card (level 1) := card_step 0
  have h1 : Nat.card (level 1) = 23 * Nat.card (level 2) := card_step 1
  have h2 : Nat.card (level 2) = 22 * Nat.card (level 3) := card_step 2
  have h3 : Nat.card (level 3) = 21 * Nat.card (level 4) := card_step 3
  have h4 : Nat.card (level 4) = 20 * Nat.card (level 5) := card_step 4
  have h5 : Nat.card (level 5) = 3 * Nat.card (level 6) := card_step 5
  have h6 : Nat.card (level 6) = 16 * Nat.card (level 7) := card_step 6
  rw [h0, h1, h2, h3, h4, h5, h6, card_last]

theorem generation_step (k : Fin 7) (G : Subgroup Perm) (hrep : ∀ r, rep r ∈ G)
    (hnext : level (k.val+1) ≤ G) : level k.val ≤ G := by
  intro p hp
  let g : level k.val := ⟨p, hp⟩
  have h := G.mul_mem (hrep (slot k (imageAt k g).val)) (hnext (residual k g).property)
  have he := congrArg Subtype.val ((splitLevel k).left_inv g)
  change (assemble k (imageAt k g) (residual k g)).val = p at he
  rw [← he]
  exact h

/-- The displayed coordinate permutations generate all permutations preserving the code. -/
theorem generators_complete : Subgroup.closure (Set.range rep) = level 0 := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    rintro _ ⟨r, rfl⟩; exact (level_zero_iff _).2 (rep_code r)
  · let G := Subgroup.closure (Set.range rep)
    have step (k : Fin 7) := generation_step k G (fun r => Subgroup.subset_closure (Set.mem_range_self r))
    have last : level 7 ≤ G := by
      intro p hp
      rw [fixed_base p hp.1 hp.2]
      exact G.one_mem
    exact step 0 (step 1 (step 2 (step 3 (step 4 (step 5 (step 6 last))))))

end GolayMathieu
