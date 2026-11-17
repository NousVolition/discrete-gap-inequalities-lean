import Mathlib

/-!
# Harper's vertex-isoperimetric theorem — stage 1: definitions and the squash lemma

Vertices of the `n`-cube are `Fin n → Bool`. The closed neighbourhood `nbhd A` of a vertex set `A`
is every vertex within Hamming distance `1` of a member of `A`.

**Harper's theorem** says that among all `m`-element vertex sets, the first `m` vertices in the
order below have the smallest neighbourhood.

This file sets up:

* **The order.** Vertices with fewer `true`s come first. Among vertices with the same number,
  the one with `true` at the first coordinate where they differ comes first (`key`).
* **Starting segments.** `seg n m` is the first `m` vertices. They are nested (`seg_mono`) and
  have `min m (2 ^ n)` elements (`card_seg`).
* **Squashing along coordinate `i`.** Cut the cube into its two halves `x i = true` and
  `x i = false`. Replace each half of `A` by the starting segment of the same size in the
  remaining coordinates (`squash`). Squashing keeps the size (`card_squash`).
* **The squash lemma** (`squash_nbhd_le`). A squash never makes the neighbourhood bigger. It
  takes two hypotheses about the cube one dimension down:
  - (a) the neighbourhood of a starting segment is a starting segment (stage 2);
  - (b) the theorem itself (the induction hypothesis).

The proof uses the slice formula `slice_nbhd`. The neighbourhood of `A`, restricted to one half,
is the neighbourhood of that half of `A` together with the other half of `A` pushed across.
After squashing, both pieces are starting segments, and starting segments are nested. So their
union has the size of the larger piece, which (b) bounds.
-/

open Finset

noncomputable section

namespace Harper

/-- The `n`-cube. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-! ## Neighbourhoods -/

/-- Closed neighbourhood: every vertex within Hamming distance `1` of a member of `A`. -/
def nbhd {n : ℕ} (A : Finset (Cube n)) : Finset (Cube n) :=
  A.biUnion fun y => univ.filter fun x => hammingDist x y ≤ 1

lemma mem_nbhd {n : ℕ} {A : Finset (Cube n)} {x : Cube n} :
    x ∈ nbhd A ↔ ∃ y ∈ A, hammingDist x y ≤ 1 := by
  simp [nbhd]

lemma subset_nbhd {n : ℕ} (A : Finset (Cube n)) : A ⊆ nbhd A := fun x hx =>
  mem_nbhd.2 ⟨x, hx, by simp⟩

/-! ## The order and starting segments -/

/-- Number of coordinates equal to `true`. -/
def weight {n : ℕ} (x : Cube n) : ℕ := (univ.filter fun i => x i = true).card

/-- Sort key. Fewer `true`s first. With equal counts, the vertex with `true` at the first
coordinate where the two differ comes first. (`Lex` puts `false` first, so it is reversed with
`ᵒᵈ`.) -/
def key {n : ℕ} (x : Cube n) : ℕ ×ₗ (Lex (Fin n → Bool))ᵒᵈ :=
  toLex (weight x, OrderDual.toDual (toLex x))

lemma key_injective {n : ℕ} : Function.Injective (key (n := n)) := by
  intro x y h
  have h2 := congrArg (fun p => ofLex (OrderDual.ofDual (ofLex p).2)) h
  simpa [key] using h2

/-- Position of `x` in the order: the number of vertices before it. -/
def rank {n : ℕ} (x : Cube n) : ℕ := (univ.filter fun y : Cube n => key y < key x).card

/-- The first `m` vertices in the order. -/
def seg (n m : ℕ) : Finset (Cube n) := univ.filter fun x => rank x < m

lemma rank_lt_rank {n : ℕ} {x y : Cube n} (h : key x < key y) : rank x < rank y := by
  unfold rank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨x, by simp [h], by simp⟩
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact hz.trans h

lemma rank_injective {n : ℕ} : Function.Injective (rank (n := n)) := by
  intro x y h
  rcases lt_trichotomy (key x) (key y) with hxy | hxy | hxy
  · exact absurd h (rank_lt_rank hxy).ne
  · exact key_injective hxy
  · exact absurd h (rank_lt_rank hxy).ne'

lemma rank_lt_card {n : ℕ} (x : Cube n) : rank x < Fintype.card (Cube n) := by
  unfold rank
  rw [← Finset.card_univ]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  exact ⟨x, Finset.mem_univ x, by simp⟩

lemma image_rank (n : ℕ) :
    (univ : Finset (Cube n)).image rank = Finset.range (Fintype.card (Cube n)) := by
  apply Finset.eq_of_subset_of_card_le
  · intro r hr
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hr
    exact Finset.mem_range.2 (rank_lt_card x)
  · apply le_of_eq
    rw [Finset.card_range, Finset.card_image_of_injective _ rank_injective, Finset.card_univ]

/-- A starting segment has `min m (2 ^ n)` elements. -/
lemma card_seg (n m : ℕ) : (seg n m).card = min m (Fintype.card (Cube n)) := by
  have h2 : (seg n m).image rank = (Finset.range (Fintype.card (Cube n))).filter (· < m) := by
    ext r
    simp only [seg, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Finset.mem_range.2 (rank_lt_card x), hx⟩
    · rintro ⟨hr, hrm⟩
      rw [← image_rank, Finset.mem_image] at hr
      obtain ⟨x, -, rfl⟩ := hr
      exact ⟨x, hrm, rfl⟩
  have h3 : (Finset.range (Fintype.card (Cube n))).filter (· < m)
      = Finset.range (min m (Fintype.card (Cube n))) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    tauto
  rw [← Finset.card_image_of_injective (seg n m) rank_injective, h2, h3, Finset.card_range]

lemma card_seg_le (n m : ℕ) : (seg n m).card ≤ m := by
  rw [card_seg]
  exact min_le_left _ _

/-- Starting segments are nested. -/
lemma seg_mono {n a b : ℕ} (h : a ≤ b) : seg n a ⊆ seg n b := by
  intro x hx
  simp only [seg, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  omega

/-- The union of two starting segments is the larger one. -/
lemma card_seg_union (n p q : ℕ) :
    (seg n p ∪ seg n q).card = max (seg n p).card (seg n q).card := by
  rcases le_total p q with h | h
  · rw [Finset.union_eq_right.mpr (seg_mono h), max_eq_right (Finset.card_le_card (seg_mono h))]
  · rw [Finset.union_eq_left.mpr (seg_mono h), max_eq_left (Finset.card_le_card (seg_mono h))]

/-! ## Cutting the cube along coordinate `i` -/

/-- The half of `A` whose coordinate `i` equals `b`, with that coordinate removed. -/
def slice {k : ℕ} (A : Finset (Cube (k + 1))) (i : Fin (k + 1)) (b : Bool) : Finset (Cube k) :=
  univ.filter fun u => (Fin.insertNth i b u : Cube (k + 1)) ∈ A

lemma sum_split {k : ℕ} {M : Type*} [AddCommMonoid M] (i : Fin (k + 1)) (g : Cube (k + 1) → M) :
    ∑ x, g x
      = ∑ u : Cube k, g (Fin.insertNth i true u) + ∑ u : Cube k, g (Fin.insertNth i false u) := by
  rw [← (Fin.insertNthEquiv (fun _ => Bool) i).sum_comp g, Fintype.sum_prod_type,
    Fintype.sum_bool]
  rfl

/-- A vertex set is split exactly in two by coordinate `i`. -/
lemma card_split {k : ℕ} (i : Fin (k + 1)) (S : Finset (Cube (k + 1))) :
    S.card = (slice S i true).card + (slice S i false).card := by
  have hS : S.card = ∑ x, if x ∈ S then 1 else 0 := by
    rw [← Finset.card_filter, Finset.filter_univ_mem]
  rw [hS]
  unfold slice
  rw [Finset.card_filter, Finset.card_filter]
  exact sum_split i (fun x => if x ∈ S then 1 else 0)

lemma hammingDist_insertNth {k : ℕ} (i : Fin (k + 1)) (a b : Bool) (u v : Cube k) :
    hammingDist (Fin.insertNth i a u : Cube (k + 1)) (Fin.insertNth i b v)
      = (if a = b then 0 else 1) + hammingDist u v := by
  unfold hammingDist
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  congr 1
  by_cases h : a = b <;> simp [h]

/-- **Slice formula.** Restricted to the half `x i = b`, the neighbourhood of `A` is the
neighbourhood of that half of `A`, together with the other half of `A` pushed across. -/
lemma slice_nbhd {k : ℕ} (i : Fin (k + 1)) (A : Finset (Cube (k + 1))) (b : Bool) :
    slice (nbhd A) i b = nbhd (slice A i b) ∪ slice A i (!b) := by
  ext u
  simp only [slice, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, mem_nbhd]
  constructor
  · rintro ⟨y, hy, hd⟩
    obtain ⟨c, v, rfl⟩ : ∃ (c : Bool) (v : Cube k), y = (Fin.insertNth i c v : Cube (k + 1)) :=
      ⟨y i, Fin.removeNth i y, (Fin.insertNth_self_removeNth i y).symm⟩
    rw [hammingDist_insertNth] at hd
    by_cases hbc : b = c
    · subst hbc
      left
      exact ⟨v, hy, by simpa using hd⟩
    · right
      rw [ite_eq_right hbc] at hd
      have huv : u = v := hammingDist_eq_zero.mp (by omega)
      have hc : c = !b := by
        revert hbc
        cases b <;> cases c <;> decide
      rw [← huv, hc] at hy
      exact hy
  · rintro (⟨v, hv, hd⟩ | h)
    · exact ⟨_, hv, by rw [hammingDist_insertNth]; simpa using hd⟩
    · exact ⟨_, h, by rw [hammingDist_insertNth]; cases b <;> simp⟩

/-! ## Squashing -/

/-- Squash `A` along coordinate `i`: replace each half by the starting segment of the same size
in the other coordinates. -/
def squash {k : ℕ} (i : Fin (k + 1)) (A : Finset (Cube (k + 1))) : Finset (Cube (k + 1)) :=
  univ.filter fun x => Fin.removeNth i x ∈ seg k (slice A i (x i)).card

lemma slice_squash {k : ℕ} (i : Fin (k + 1)) (A : Finset (Cube (k + 1))) (b : Bool) :
    slice (squash i A) i b = seg k (slice A i b).card := by
  ext u
  unfold slice squash
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Fin.removeNth_insertNth, Fin.insertNth_apply_same]
  rfl

/-- Squashing keeps the number of vertices. -/
theorem card_squash {k : ℕ} (i : Fin (k + 1)) (A : Finset (Cube (k + 1))) :
    (squash i A).card = A.card := by
  rw [card_split i (squash i A), card_split i A, slice_squash, slice_squash, card_seg, card_seg,
    min_eq_left (Finset.card_le_univ _), min_eq_left (Finset.card_le_univ _)]

/-- **Squash lemma.** A squash never makes the neighbourhood bigger.

Hypotheses, about the cube one dimension down:
* `hseg` — (a) the neighbourhood of every starting segment is a starting segment (stage 2);
* `hmin` — (b) a starting segment has the smallest neighbourhood among sets of its size
  (the induction hypothesis). -/
theorem squash_nbhd_le {k : ℕ} (i : Fin (k + 1)) (A : Finset (Cube (k + 1)))
    (hseg : ∀ m, ∃ m', nbhd (seg k m) = seg k m')
    (hmin : ∀ B : Finset (Cube k), (nbhd (seg k B.card)).card ≤ (nbhd B).card) :
    (nbhd (squash i A)).card ≤ (nbhd A).card := by
  have half : ∀ b : Bool,
      (slice (nbhd (squash i A)) i b).card ≤ (slice (nbhd A) i b).card := by
    intro b
    rw [slice_nbhd, slice_nbhd, slice_squash, slice_squash]
    obtain ⟨m', hm'⟩ := hseg (slice A i b).card
    rw [hm', card_seg_union, ← hm']
    calc max (nbhd (seg k (slice A i b).card)).card (seg k (slice A i (!b)).card).card
        ≤ max (nbhd (slice A i b)).card (slice A i (!b)).card :=
          max_le_max (hmin _) (card_seg_le _ _)
      _ ≤ (nbhd (slice A i b) ∪ slice A i (!b)).card :=
          max_le (Finset.card_le_card Finset.subset_union_left)
            (Finset.card_le_card Finset.subset_union_right)
  rw [card_split i (nbhd (squash i A)), card_split i (nbhd A)]
  exact add_le_add (half true) (half false)

end Harper
