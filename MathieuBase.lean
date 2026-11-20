import LeechMonomial
import MathieuData

/-! # Seven coordinates determine a permutation preserving the Golay code -/

namespace GolayMathieu

open GolayMatrixDistance LeechLattice LeechCodeCounts LeechSymmetry

abbrev Point := Fin 24
abbrev Perm := Equiv.Perm Point
abbrev Word := Point → Bool

def base (k : Nat) : Point := Fin.ofNat 24 (MathieuData.basePoints.getD k 0)
def block (t : Fin 17) : Word := word (MathieuData.octadMasks.getD t.val 0)
def anchor (t : Fin 17) (i : Fin 5) : Point :=
  Fin.ofNat 24 ((MathieuData.anchorPoints.getD t.val #[]).getD i.val 0)

def Fixes (k : ℕ) (p : Perm) : Prop := ∀ j < k, p (base j) = base j

theorem block_weight : ∀ t, weight (block t) = 8 := by decide +kernel
theorem block_golay (t : Fin 17) : IsGolayWord (block t) := by
  let m (i : Fin 17) := (MathieuData.octadMasks.getD i.val 0).toNat % 4096
  refine ⟨m t, Nat.mod_lt _ (by decide), ?_⟩
  have checked : ∀ i : Fin 17, word (encodeNat (m i)) = block i := by decide +kernel
  exact checked t

theorem weight_relabel (p : Perm) (w : Word) : weight (fun i => w (p i)) = weight w := by
  unfold weight
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquiv p (fun _ => Iff.rfl))

theorem xor_weight (u v : Word) :
    weight (fun i => u i ^^ v i) + 2 * (Finset.univ.filter
      (fun i => u i = true ∧ v i = true)).card = weight u + weight v := by
  simp only [weight, Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases u i <;> cases v i <;> decide

/-- Two octads sharing five positions coincide by the minimum distance of the code. -/
theorem octad_unique {u v : Word} (hu : IsGolayWord u) (hv : IsGolayWord v)
    (wu : weight u = 8) (wv : weight v = 8) (a : Fin 5 → Point)
    (inj : Function.Injective a) (ha : ∀ i, u (a i) = true ∧ v (a i) = true) : u = v := by
  classical
  let inter := Finset.univ.filter (fun i => u i = true ∧ v i = true)
  have hi : 5 ≤ inter.card := by
    have hs : Finset.univ.image a ⊆ inter := by
      intro j hj
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha i⟩
    simpa [Finset.card_image_of_injective _ inj] using Finset.card_le_card hs
  by_contra h
  have hne : ∃ i, (u i ^^ v i) = true := by
    by_contra! h'
    apply h; funext i
    have := h' i
    cases hu' : u i <;> cases hv' : v i <;> simp_all
  have h8 := golay_weight_ge_eight (isGolayWord_xor hu hv) hne
  change 8 ≤ weight (fun i => u i ^^ v i) at h8
  have hw := xor_weight u v
  change weight (fun i => u i ^^ v i) + 2 * inter.card = weight u + weight v at hw
  omega

theorem block_fixed (p : Perm) (hp : IsCodePermutation p) (t : Fin 17)
    (ha : ∀ i, p (anchor t i) = anchor t i) : ∀ j, block t (p j) = block t j := by
  have ai : ∀ r : Fin 17, Function.Injective (anchor r) := by decide +kernel
  have ao : ∀ r i, block r (anchor r i) = true := by decide +kernel
  apply congrFun
  exact octad_unique ((hp _).1 (block_golay t)) (block_golay t)
    ((weight_relabel p _).trans (block_weight t)) (block_weight t) (anchor t) (ai t)
    (fun i => ⟨by rw [ha, ao], ao t i⟩)

theorem fixed_base (p : Perm) (hp : IsCodePermutation p) (hf : Fixes 7 p) : p = 1 := by
  have anchors : ∀ t : Fin 17, t.val < 16 → ∀ i, ∃ j : Fin 7, anchor t i = base j.val := by
    decide +kernel
  have first : ∀ t : Fin 17, t.val < 16 → ∀ i, block t (p i) = block t i := by
    intro t ht
    apply block_fixed p hp
    intro i
    obtain ⟨j, hj⟩ := anchors t ht i
    rw [hj, hf j.val j.isLt]
  have six : ∀ i : Point, (∀ t : Fin 17, t.val < 16 → block t i = block t 6) → i = 6 := by
    decide +kernel
  have h6 : p 6 = 6 := six _ fun t ht => first t ht 6
  have lastAnchors : ∀ i, anchor 16 i = 6 ∨ ∃ j : Fin 7, anchor 16 i = base j.val := by
    decide +kernel
  have last := block_fixed p hp 16 (fun i => by
    rcases lastAnchors i with h | ⟨j, h⟩
    · rwa [h]
    · rw [h, hf j.val j.isLt])
  have separate : ∀ i j : Point, (∀ t : Fin 17, block t i = block t j) → i = j := by
    decide +kernel
  apply Equiv.ext
  intro i
  apply separate
  intro t
  by_cases ht : t.val < 16
  · exact first t ht i
  · have : t = 16 := Fin.ext (by omega)
    subst t; exact last i

def allowed (k : Fin 7) (j : Point) : Bool :=
  (!(List.range k.val).any (fun i => base i == j)) &&
    (decide (k.val < 5) || (block 0 j == block 0 (base k.val)))

theorem allowed_image (k : Fin 7) (p : Perm) (hp : IsCodePermutation p) (hf : Fixes k.val p) :
    allowed k (p (base k.val)) = true := by
  have distinct : ∀ a b : Fin 7, base a.val = base b.val → a = b := by decide +kernel
  have hn : ∀ i < k.val, base i ≠ p (base k.val) := by
    intro i hi h
    have he := p.injective ((hf i hi).trans h)
    have := distinct ⟨i, by omega⟩ k he
    have hval : i = k.val := congrArg Fin.val this
    omega
  simp only [allowed, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false,
    List.mem_range, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨hn, ?_⟩
  by_cases h5 : k.val < 5
  · exact Or.inl h5
  · right
    apply block_fixed p hp 0
    have ha : ∀ i, ∃ a : Fin 5, anchor 0 i = base a.val := by decide +kernel
    intro i
    obtain ⟨a, he⟩ := ha i
    rw [he, hf a.val (by omega)]

end GolayMathieu
