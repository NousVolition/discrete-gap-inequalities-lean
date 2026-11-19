/-
Copyright © 2026 NousVolition. All rights reserved.
-/
import Mathlib
import GolayMatrixDistance

/-!
# The Leech lattice from the Golay code, and its smallest length

This file builds the 24-dimensional **Leech lattice** out of the extended binary Golay code
proved in `GolayMatrixDistance.lean`, and proves that its shortest nonzero vectors have squared
length 32 (in the usual coordinates scaled up by `√8`).

## The Golay code as a set of 24-bit words

`GolayMatrixDistance` encodes a 12-bit message `m < 4096` as a 24-bit word `encodeNat m`. Here a
word `w : Fin 24 → Bool` is a **Golay codeword** (`IsGolayWord w`) when it equals the bits of
`encodeNat m` for some `m < 4096`, read with the same bit test that `popcount24` uses. So this is
the very same code, not a new one. From the existing theorems we get:

* `encodeNat_xor`: encoding respects adding messages bit by bit, so the code is closed under
  adding words (`isGolayWord_xor`); it contains the all-zero and the all-one words, so it is also
  closed under flipping every bit (`isGolayWord_not`).
* `card_true_of_isGolayWord`: the number of `true` positions of a codeword is `popcount24` of
  that codeword, so every codeword has a multiple of 4 of them (`golay_weight_mod_four`) and every
  nonzero codeword has at least 8 (`golay_weight_ge_eight`). Both come straight from
  `golay_doubly_even_and_d_min_8` and `golay_min_distance_bound`.

## The Leech lattice

We use the construction in Conway and Sloane, *Sphere Packings, Lattices and Groups*,
chapter 4, section 11 (the Leech lattice scaled by `√8`). A vector `x` of 24 whole numbers is in
the lattice when, for `m = 0` or `m = 1`:

1. every `x i` leaves remainder `m` on division by 2 (all even, or all odd);
2. the total `∑ x i` leaves remainder `4 m` on division by 8;
3. for every remainder `k` on division by 4, the positions `i` with `x i ≡ k (mod 4)` form a
   Golay codeword.

That is `InLeech`, written exactly in this "for every remainder" form. `inLeech_iff` shows it
comes down to a simpler test: in the even case the positions with `x i ≡ 2 (mod 4)` form a
codeword, and in the odd case the positions with `x i ≡ 3 (mod 4)` form a codeword (the other
remainders then take care of themselves, because flipping every bit of a codeword gives a
codeword and the empty set is a codeword).

`leechLattice` packages this as an `AddSubgroup` of `Fin 24 → ℤ`: it contains `0` and is closed
under adding and negating vectors.

## The smallest length

`leech_norm_ge_32`: every nonzero vector of the lattice has `∑ (x i)² ≥ 32`. The proof splits
into three cases:

* **All odd.** Each `(x i)² ≥ 1`. If every entry were `±1`, the `-1` entries would sit on a
  codeword, so there would be a multiple of 4 of them, and then `∑ x i` would leave remainder 0 on
  division by 8, not 4. So some entry has `|x i| ≥ 3`, giving at least `9 + 23 = 32`.
* **All even, some entry `≡ 2 (mod 4)`.** Those entries sit on a nonzero codeword, so there are at
  least 8 of them, each with square at least 4.
* **All entries multiples of 4.** A single nonzero entry would have to be a multiple of 8 (from
  the total), giving at least 64; otherwise two nonzero entries give at least `16 + 16`.

`leech_min_norm` shows 32 is really reached, and states the result as "32 is the least squared
length of a nonzero lattice vector". As a check that the definition is the standard one, the file
also shows one vector of each of the three standard shapes is in the lattice
(`(4, 4, 0, …)`, `2` on an octad, `(-3, 1, …, 1)`), and two nearby vectors are not
(`(4, 0, …)` and `(1, …, 1)`).

## What is not proved here

This file does **not** sort the length-32 vectors into the three shapes `(±4)² 0²²`,
`(±2)⁸ 0¹⁶` and `(∓3)(±1)²³`, or count them. So it does not yet prove that the lattice has
exactly 196,560 shortest vectors; that count is checked as arithmetic only, in
`GolayLeechBridge.lean`. It also does not prove other standard facts about the lattice, such as
its determinant (it is unimodular after dividing by `√8`) or its symmetry group. It uses the one
form of the Golay code fixed in `GolayMatrixDistance.lean`; other published forms give the same
lattice up to reordering the coordinates, but that is not proved here either.
-/

namespace LeechLattice

open GolayMatrixDistance

/-! ## Bits of a 24-bit word -/

/-- Bit `k` of a word, read with the same test that `popcount24` uses. -/
def bitAt (u : UInt32) (k : Nat) : Bool := (u >>> k.toUInt32) &&& 1 == 1

/-- The word `u` as a function on the 24 positions. -/
def word (u : UInt32) : Fin 24 → Bool := fun k => bitAt u k.val

theorem natBit_eq (m i : Nat) : ((m >>> i) &&& 1 == 1) = m.testBit i := by
  rw [Nat.testBit, Nat.and_comm]
  rcases Nat.and_one_is_mod (m >>> i) ▸ Nat.mod_two_eq_zero_or_one (m >>> i) with h | h <;>
    simp [Nat.and_comm, h]

theorem bitAt_eq_testBit (u : UInt32) (k : Nat) (hk : k < 32) :
    bitAt u k = u.toNat.testBit k := by
  have h1 : ((u >>> k.toUInt32) &&& 1 == 1) = ((u.toNat >>> k) &&& 1 == 1) := by
    have : (k.toUInt32).toNat % 32 = k := by
      simp [Nat.toUInt32]; omega
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]
    rw [← UInt32.toNat_inj, UInt32.toNat_and, UInt32.toNat_shiftRight, this]; rfl
  rw [bitAt, h1, natBit_eq]

theorem bitAt_xor (u v : UInt32) (k : Nat) (hk : k < 32) :
    bitAt (u ^^^ v) k = (bitAt u k ^^ bitAt v k) := by
  rw [bitAt_eq_testBit _ _ hk, bitAt_eq_testBit _ _ hk, bitAt_eq_testBit _ _ hk,
    UInt32.toNat_xor, Nat.testBit_xor]

theorem popcount_foldl (u : UInt32) (l : List Nat) (acc : Nat) :
    l.foldl (fun acc b => if (u >>> b.toUInt32) &&& 1 == 1 then acc + 1 else acc) acc
      = acc + l.countP (fun b => bitAt u b) := by
  induction l generalizing acc with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons, ih, List.countP_cons]
    by_cases h : bitAt u b = true
    · have h' : ((u >>> b.toUInt32) &&& 1 == 1) = true := h
      simp only [h', h, ite_true]; omega
    · have h' : ((u >>> b.toUInt32) &&& 1 == 1) = false := by simpa [bitAt] using h
      simp only [h', Bool.false_eq_true, ite_false]
      simp [h]

theorem popcount24_eq_card_bitAt (u : UInt32) :
    popcount24 u = (Finset.univ.filter (fun k : Fin 24 => bitAt u k.val = true)).card := by
  rw [popcount24, popcount_foldl, zero_add, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun k => if bitAt u k = true then 1 else 0) 24,
    Finset.sum_boole]
  simp only [Nat.cast_id]
  rw [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card, List.countP_eq_length_filter]
  simp

/-- `popcount24` counts the `true` positions of the word. -/
theorem popcount24_eq_card (u : UInt32) :
    popcount24 u = (Finset.univ.filter (fun k : Fin 24 => word u k = true)).card :=
  popcount24_eq_card_bitAt u

/-! ## Encoding respects adding messages -/

/-- One step of `encodeNat`. -/
def encodeStep (m : Nat) (acc : UInt32) (i : Nat) : UInt32 :=
  if (m >>> i) &&& 1 == 1 then acc ^^^ (genMasks.getD i 0) else acc

theorem encodeNat_eq_foldl (m : Nat) :
    encodeNat m = (List.range 12).foldl (encodeStep m) 0 := rfl

theorem u32_xor_left_comm (a b c : UInt32) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← UInt32.xor_assoc, UInt32.xor_comm a b, UInt32.xor_assoc]

theorem foldl_encodeStep_xor (m m' : Nat) (l : List Nat) (a b : UInt32) :
    l.foldl (encodeStep (m ^^^ m')) (a ^^^ b)
      = l.foldl (encodeStep m) a ^^^ l.foldl (encodeStep m') b := by
  induction l generalizing a b with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    simp only [encodeStep, natBit_eq, Nat.testBit_xor]
    cases m.testBit i <;> cases m'.testBit i <;>
      simp [UInt32.xor_assoc, UInt32.xor_comm, u32_xor_left_comm]

/-- Encoding the bitwise sum of two messages gives the bitwise sum of their codewords. -/
theorem encodeNat_xor (m m' : Nat) : encodeNat (m ^^^ m') = encodeNat m ^^^ encodeNat m' := by
  rw [encodeNat_eq_foldl, encodeNat_eq_foldl, encodeNat_eq_foldl, ← foldl_encodeStep_xor]
  rfl

theorem encodeNat_zero : encodeNat 0 = 0 := by decide

/-- Message `4095` (all twelve bits set) encodes to the all-one word. -/
theorem word_encodeNat_4095 : word (encodeNat 4095) = fun _ => true := by
  funext k
  revert k
  decide +kernel

theorem word_zero : word 0 = fun _ => false := by
  funext k
  revert k
  decide

/-! ## Golay codewords -/

/-- A word is a **Golay codeword** when it is the codeword of some message `m < 4096` in
`GolayMatrixDistance`. -/
def IsGolayWord (w : Fin 24 → Bool) : Prop :=
  ∃ m < 4096, word (encodeNat m) = w

theorem isGolayWord_false : IsGolayWord (fun _ => false) :=
  ⟨0, by norm_num, by rw [encodeNat_zero, word_zero]⟩

theorem isGolayWord_true : IsGolayWord (fun _ => true) :=
  ⟨4095, by norm_num, word_encodeNat_4095⟩

/-- Golay codewords are closed under adding words bit by bit. -/
theorem isGolayWord_xor {w v : Fin 24 → Bool} (hw : IsGolayWord w) (hv : IsGolayWord v) :
    IsGolayWord (fun k => w k ^^ v k) := by
  obtain ⟨m, hm, rfl⟩ := hw
  obtain ⟨m', hm', rfl⟩ := hv
  refine ⟨m ^^^ m', Nat.xor_lt_two_pow (n := 12) hm hm', ?_⟩
  funext k
  simp only [word]
  rw [encodeNat_xor, bitAt_xor _ _ _ (by omega)]

/-- Flipping every bit of a Golay codeword gives a Golay codeword. -/
theorem isGolayWord_not {w : Fin 24 → Bool} (hw : IsGolayWord w) :
    IsGolayWord (fun k => !w k) := by
  have := isGolayWord_xor hw isGolayWord_true
  simpa using this

/-- The number of `true` positions of a codeword is the `popcount24` of the codeword. -/
theorem card_true_of_isGolayWord {w : Fin 24 → Bool} (hw : IsGolayWord w) :
    ∃ m < 4096, (Finset.univ.filter (fun k => w k = true)).card = popcount24 (encodeNat m) := by
  obtain ⟨m, hm, rfl⟩ := hw
  exact ⟨m, hm, (popcount24_eq_card _).symm⟩

/-- Every Golay codeword has a multiple of 4 `true` positions
(from `golay_doubly_even_and_d_min_8`). -/
theorem golay_weight_mod_four {w : Fin 24 → Bool} (hw : IsGolayWord w) :
    (Finset.univ.filter (fun k => w k = true)).card % 4 = 0 := by
  obtain ⟨m, hm, hc⟩ := card_true_of_isGolayWord hw
  rw [hc]
  have h := golay_doubly_even_and_d_min_8
  simp only [checkAllCodewords, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    beq_iff_eq] at h
  exact (h m hm).1

/-- Every nonzero Golay codeword has at least 8 `true` positions
(from `golay_min_distance_bound`). -/
theorem golay_weight_ge_eight {w : Fin 24 → Bool} (hw : IsGolayWord w) (hne : ∃ k, w k = true) :
    8 ≤ (Finset.univ.filter (fun k => w k = true)).card := by
  obtain ⟨m, hm, rfl⟩ := hw
  rw [← popcount24_eq_card]
  apply golay_min_distance_bound m _ hm
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    obtain ⟨k, hk⟩ := hne
    rw [encodeNat_zero, word_zero] at hk
    exact absurd hk (by simp)
  · omega

/-! ## The Leech lattice -/

/-- The positions `i` where `x i` leaves the same remainder as `k` on division by 4. -/
def residueSet (x : Fin 24 → ℤ) (k : ℤ) : Fin 24 → Bool := fun i => decide (x i % 4 = k % 4)

/-- **The Leech lattice condition** (Conway and Sloane, *Sphere Packings, Lattices and Groups*,
chapter 4, section 11, coordinates scaled by `√8`): for `m = 0` or `1`, every coordinate leaves
remainder `m` on division by 2, the total leaves remainder `4 m` on division by 8, and for every
remainder `k` on division by 4 the positions where `x i ≡ k (mod 4)` form a Golay codeword. -/
def InLeech (x : Fin 24 → ℤ) : Prop :=
  ∃ m : ℤ, (m = 0 ∨ m = 1) ∧ (∀ i, x i % 2 = m) ∧ (∑ i, x i) % 8 = 4 * m ∧
    ∀ k : ℤ, IsGolayWord (residueSet x k)

/-- The even case, in its short form. -/
def EvenLeech (x : Fin 24 → ℤ) : Prop :=
  (∀ i, x i % 2 = 0) ∧ (∑ i, x i) % 8 = 0 ∧ IsGolayWord (residueSet x 2)

/-- The odd case, in its short form. -/
def OddLeech (x : Fin 24 → ℤ) : Prop :=
  (∀ i, x i % 2 = 1) ∧ (∑ i, x i) % 8 = 4 ∧ IsGolayWord (residueSet x 3)

/-- **Short form of the condition:** in the even case only the positions with `x i ≡ 2 (mod 4)`
need checking, and in the odd case only the positions with `x i ≡ 3 (mod 4)`. -/
theorem inLeech_iff (x : Fin 24 → ℤ) : InLeech x ↔ EvenLeech x ∨ OddLeech x := by
  constructor
  · rintro ⟨m, hm | hm, hpar, hsum, hg⟩ <;> subst hm
    · exact Or.inl ⟨hpar, by simpa using hsum, hg 2⟩
    · exact Or.inr ⟨hpar, by simpa using hsum, hg 3⟩
  · rintro (⟨hpar, hsum, hg⟩ | ⟨hpar, hsum, hg⟩)
    · refine ⟨0, Or.inl rfl, hpar, by simpa using hsum, fun k => ?_⟩
      have hk : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
      rcases hk with hk | hk | hk | hk
      · have : residueSet x k = fun i => !residueSet x 2 i := by
          funext i
          have := hpar i
          simp only [residueSet, hk, Int.reduceMod]
          by_cases h : x i % 4 = 2 <;> simp [h]
          omega
        rw [this]; exact isGolayWord_not hg
      · have : residueSet x k = fun _ => false := by
          funext i
          have := hpar i
          simp only [residueSet, hk]
          simp; omega
        rw [this]; exact isGolayWord_false
      · have : residueSet x k = residueSet x 2 := by
          funext i
          simp only [residueSet, hk, Int.reduceMod]
        rw [this]; exact hg
      · have : residueSet x k = fun _ => false := by
          funext i
          have := hpar i
          simp only [residueSet, hk]
          simp; omega
        rw [this]; exact isGolayWord_false
    · refine ⟨1, Or.inr rfl, hpar, by simpa using hsum, fun k => ?_⟩
      have hk : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
      rcases hk with hk | hk | hk | hk
      · have : residueSet x k = fun _ => false := by
          funext i
          have := hpar i
          simp only [residueSet, hk]
          simp; omega
        rw [this]; exact isGolayWord_false
      · have : residueSet x k = fun i => !residueSet x 3 i := by
          funext i
          have := hpar i
          simp only [residueSet, hk, Int.reduceMod]
          by_cases h : x i % 4 = 3 <;> simp [h]
          omega
        rw [this]; exact isGolayWord_not hg
      · have : residueSet x k = fun _ => false := by
          funext i
          have := hpar i
          simp only [residueSet, hk]
          simp; omega
        rw [this]; exact isGolayWord_false
      · have : residueSet x k = residueSet x 3 := by
          funext i
          simp only [residueSet, hk, Int.reduceMod]
        rw [this]; exact hg

theorem sum_add' (x y : Fin 24 → ℤ) : ∑ i, (x + y) i = ∑ i, x i + ∑ i, y i := by
  simp [Finset.sum_add_distrib]

theorem sum_neg' (x : Fin 24 → ℤ) : ∑ i, (-x) i = -∑ i, x i := by
  simp [Finset.sum_neg_distrib]

theorem evenLeech_add {x y : Fin 24 → ℤ} (hx : EvenLeech x) (hy : EvenLeech y) :
    EvenLeech (x + y) := by
  obtain ⟨hpx, hsx, hgx⟩ := hx
  obtain ⟨hpy, hsy, hgy⟩ := hy
  refine ⟨fun i => by have := hpx i; have := hpy i; simp; omega,
    by rw [sum_add']; omega, ?_⟩
  have : residueSet (x + y) 2 = fun i => residueSet x 2 i ^^ residueSet y 2 i := by
    funext i
    have := hpx i; have := hpy i
    simp only [residueSet, Pi.add_apply, Int.reduceMod]
    by_cases h1 : x i % 4 = 2 <;> by_cases h2 : y i % 4 = 2 <;> simp [h1, h2] <;> omega
  rw [this]; exact isGolayWord_xor hgx hgy

theorem oddLeech_add {x y : Fin 24 → ℤ} (hx : OddLeech x) (hy : OddLeech y) :
    EvenLeech (x + y) := by
  obtain ⟨hpx, hsx, hgx⟩ := hx
  obtain ⟨hpy, hsy, hgy⟩ := hy
  refine ⟨fun i => by have := hpx i; have := hpy i; simp; omega,
    by rw [sum_add']; omega, ?_⟩
  have : residueSet (x + y) 2 = fun i => !(residueSet x 3 i ^^ residueSet y 3 i) := by
    funext i
    have := hpx i; have := hpy i
    simp only [residueSet, Pi.add_apply, Int.reduceMod]
    by_cases h1 : x i % 4 = 3 <;> by_cases h2 : y i % 4 = 3 <;> simp [h1, h2] <;> omega
  rw [this]; exact isGolayWord_not (isGolayWord_xor hgx hgy)

theorem odd_even_add {x y : Fin 24 → ℤ} (hx : OddLeech x) (hy : EvenLeech y) :
    OddLeech (x + y) := by
  obtain ⟨hpx, hsx, hgx⟩ := hx
  obtain ⟨hpy, hsy, hgy⟩ := hy
  refine ⟨fun i => by have := hpx i; have := hpy i; simp; omega,
    by rw [sum_add']; omega, ?_⟩
  have : residueSet (x + y) 3 = fun i => residueSet x 3 i ^^ residueSet y 2 i := by
    funext i
    have := hpx i; have := hpy i
    simp only [residueSet, Pi.add_apply, Int.reduceMod]
    by_cases h1 : x i % 4 = 3 <;> by_cases h2 : y i % 4 = 2 <;> simp [h1, h2] <;> omega
  rw [this]; exact isGolayWord_xor hgx hgy

theorem evenLeech_neg {x : Fin 24 → ℤ} (hx : EvenLeech x) : EvenLeech (-x) := by
  obtain ⟨hp, hs, hg⟩ := hx
  refine ⟨fun i => by have := hp i; simp; omega, by rw [sum_neg']; omega, ?_⟩
  have : residueSet (-x) 2 = residueSet x 2 := by
    funext i
    simp only [residueSet, Pi.neg_apply, decide_eq_decide]
    omega
  rw [this]; exact hg

theorem oddLeech_neg {x : Fin 24 → ℤ} (hx : OddLeech x) : OddLeech (-x) := by
  obtain ⟨hp, hs, hg⟩ := hx
  refine ⟨fun i => by have := hp i; simp; omega, by rw [sum_neg']; omega, ?_⟩
  have : residueSet (-x) 3 = fun i => !residueSet x 3 i := by
    funext i
    have := hp i
    simp only [residueSet, Pi.neg_apply, Int.reduceMod]
    by_cases h : x i % 4 = 3 <;> simp [h] <;> omega
  rw [this]; exact isGolayWord_not hg

/-- **The Leech lattice** (scaled by `√8`) as an additive subgroup of `ℤ²⁴`: it contains `0`
and is closed under adding and negating vectors. -/
def leechLattice : AddSubgroup (Fin 24 → ℤ) where
  carrier := {x | InLeech x}
  zero_mem' := by
    show InLeech 0
    rw [inLeech_iff]
    left
    refine ⟨fun i => by simp, by simp, ?_⟩
    have : residueSet 0 2 = fun _ => false := by
      funext i; simp [residueSet]
    rw [this]; exact isGolayWord_false
  add_mem' := by
    intro x y hx hy
    show InLeech (x + y)
    have hx' := (inLeech_iff x).1 hx
    have hy' := (inLeech_iff y).1 hy
    rw [inLeech_iff]
    rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy'
    · exact Or.inl (evenLeech_add hx' hy')
    · exact Or.inr (add_comm x y ▸ odd_even_add hy' hx')
    · exact Or.inr (odd_even_add hx' hy')
    · exact Or.inl (oddLeech_add hx' hy')
  neg_mem' := by
    intro x hx
    show InLeech (-x)
    have hx' := (inLeech_iff x).1 hx
    rw [inLeech_iff]
    rcases hx' with hx' | hx'
    · exact Or.inl (evenLeech_neg hx')
    · exact Or.inr (oddLeech_neg hx')

theorem mem_leechLattice (x : Fin 24 → ℤ) : x ∈ leechLattice ↔ InLeech x := Iff.rfl

/-! ## The smallest length -/

/-- **All odd:** a lattice vector with all odd entries has squared length at least 32. -/
theorem oddLeech_norm_ge {x : Fin 24 → ℤ} (hx : OddLeech x) : 32 ≤ ∑ i, x i ^ 2 := by
  obtain ⟨hp, hs, hg⟩ := hx
  by_cases hbig : ∃ j, x j ≠ 1 ∧ x j ≠ -1
  · obtain ⟨j, hj1, hj2⟩ := hbig
    have hj : 9 ≤ x j ^ 2 := by
      have := hp j
      have : x j ≥ 3 ∨ x j ≤ -3 := by omega
      rcases this with h | h <;> nlinarith
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hrest : ∑ i ∈ Finset.univ.erase j, (1 : ℤ) ≤ ∑ i ∈ Finset.univ.erase j, x i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have := hp i
      have : x i ≥ 1 ∨ x i ≤ -1 := by omega
      rcases this with h | h <;> nlinarith
    have hcard : ∑ i ∈ Finset.univ.erase j, (1 : ℤ) = 23 := by
      simp [Finset.card_erase_of_mem]
    linarith
  · -- Every entry is `1` or `-1`; the `-1` entries sit on a codeword.
    push Not at hbig
    exfalso
    have hpt : ∀ i, x i = 1 - 2 * (if residueSet x 3 i = true then 1 else 0) := by
      intro i
      by_cases h : x i = 1
      · simp [residueSet, h]
      · have h' : x i = -1 := hbig i h
        simp [residueSet, h']
    have hsum : ∑ i, x i =
        24 - 2 * ((Finset.univ.filter (fun i => residueSet x 3 i = true)).card : ℤ) := by
      rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_boole]
      simp
    have h4 := golay_weight_mod_four hg
    rw [hsum] at hs
    omega

/-- **All even, some entry `≡ 2 (mod 4)`:** those entries sit on a nonzero codeword, so there
are at least 8 of them, each with square at least 4. -/
theorem evenLeech_norm_ge_of_two {x : Fin 24 → ℤ} (hx : EvenLeech x)
    (hne : ∃ i, residueSet x 2 i = true) : 32 ≤ ∑ i, x i ^ 2 := by
  have h8 := golay_weight_ge_eight hx.2.2 hne
  have hle : ∑ i, 4 * (if residueSet x 2 i = true then (1 : ℤ) else 0) ≤ ∑ i, x i ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs with h
    · simp only [residueSet, Int.reduceMod, decide_eq_true_eq] at h
      have : x i ≥ 2 ∨ x i ≤ -2 := by omega
      rcases this with h | h <;> nlinarith
    · simp only [mul_zero]; positivity
  rw [← Finset.mul_sum, Finset.sum_boole] at hle
  have h8' : (8 : ℤ) ≤ ((Finset.univ.filter (fun i => residueSet x 2 i = true)).card : ℤ) := by
    exact_mod_cast h8
  linarith

/-- **All entries multiples of 4:** a nonzero vector has two nonzero entries (at least
`16 + 16`), or one entry that the total forces to be a multiple of 8 (at least 64). -/
theorem evenLeech_norm_ge_of_four {x : Fin 24 → ℤ} (hx : EvenLeech x)
    (hno : ∀ i, residueSet x 2 i = false) (h0 : x ≠ 0) : 32 ≤ ∑ i, x i ^ 2 := by
  have h4 : ∀ i, x i % 4 = 0 := by
    intro i
    have h1 := hx.1 i
    have h2 := hno i
    simp only [residueSet, Int.reduceMod, decide_eq_false_iff_not] at h2
    omega
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (funext h)
  have hsq : ∀ i, x i ≠ 0 → 16 ≤ x i ^ 2 := by
    intro i hi
    have := h4 i
    have : x i ≥ 4 ∨ x i ≤ -4 := by omega
    rcases this with h | h <;> nlinarith
  by_cases hk : ∃ k, k ≠ j ∧ x k ≠ 0
  · obtain ⟨k, hkj, hk⟩ := hk
    have hpair : x j ^ 2 + x k ^ 2 ≤ ∑ i, x i ^ 2 := by
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => x i ^ 2)
        (Finset.subset_univ {j, k}) (fun i _ _ => sq_nonneg (x i))
      rwa [Finset.sum_pair (Ne.symm hkj)] at this
    linarith [hsq j hj, hsq k hk]
  · push Not at hk
    have hs : ∑ i, x i = x j :=
      Finset.sum_eq_single j (fun i _ hi => hk i hi) (by simp)
    have h8 := hx.2.1
    rw [hs] at h8
    have : x j ≥ 8 ∨ x j ≤ -8 := by omega
    have hj2 : 64 ≤ x j ^ 2 := by rcases this with h | h <;> nlinarith
    have := Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg (x i))
      (Finset.mem_univ j)
    linarith

/-- **Smallest length (lower bound):** every nonzero vector of the Leech lattice (scaled by
`√8`) has squared length at least 32. -/
theorem leech_norm_ge_32 (x : Fin 24 → ℤ) (hx : x ∈ leechLattice) (h0 : x ≠ 0) :
    32 ≤ ∑ i, x i ^ 2 := by
  rcases (inLeech_iff x).1 hx with he | ho
  · by_cases hne : ∃ i, residueSet x 2 i = true
    · exact evenLeech_norm_ge_of_two he hne
    · push Not at hne
      exact evenLeech_norm_ge_of_four he (fun i => by simpa using hne i) h0
  · exact oddLeech_norm_ge ho

/-! ## One vector of each standard shape, and two that are not in the lattice -/

/-- The vector `(4, 4, 0, …, 0)`. -/
def vecFourFour : Fin 24 → ℤ := fun i => if i.val < 2 then 4 else 0

/-- The vector with `2` on the octad `encodeNat 2` and `0` elsewhere. -/
def vecOctad : Fin 24 → ℤ := fun i => if word (encodeNat 2) i then 2 else 0

/-- The vector `(-3, 1, 1, …, 1)`. -/
def vecThree : Fin 24 → ℤ := fun i => if i.val = 0 then -3 else 1

/-- The vector `(4, 0, …, 0)`. -/
def vecFour : Fin 24 → ℤ := fun i => if i.val = 0 then 4 else 0

/-- The all-one vector `(1, 1, …, 1)`. -/
def vecOnes : Fin 24 → ℤ := fun _ => 1

theorem vecFourFour_mem : vecFourFour ∈ leechLattice := by
  rw [mem_leechLattice, inLeech_iff]
  left
  refine ⟨fun i => ?_, by decide, ?_⟩
  · simp only [vecFourFour]; split_ifs <;> norm_num
  · have : residueSet vecFourFour 2 = fun _ => false := by
      funext i; revert i; decide
    rw [this]; exact isGolayWord_false

theorem vecFourFour_norm : ∑ i, vecFourFour i ^ 2 = 32 := by decide

theorem vecOctad_mem : vecOctad ∈ leechLattice := by
  rw [mem_leechLattice, inLeech_iff]
  left
  refine ⟨fun i => ?_, by decide +kernel, ?_⟩
  · simp only [vecOctad]; split_ifs <;> norm_num
  · have : residueSet vecOctad 2 = word (encodeNat 2) := by
      funext i; revert i; decide +kernel
    rw [this]; exact ⟨2, by norm_num, rfl⟩

theorem vecOctad_norm : ∑ i, vecOctad i ^ 2 = 32 := by decide +kernel

theorem vecThree_mem : vecThree ∈ leechLattice := by
  rw [mem_leechLattice, inLeech_iff]
  right
  refine ⟨fun i => ?_, by decide, ?_⟩
  · simp only [vecThree]; split_ifs <;> norm_num
  · have : residueSet vecThree 3 = fun _ => false := by
      funext i; revert i; decide
    rw [this]; exact isGolayWord_false

theorem vecThree_norm : ∑ i, vecThree i ^ 2 = 32 := by decide

/-- `(4, 0, …, 0)` is not in the lattice: its total is 4, not a multiple of 8. -/
theorem vecFour_not_mem : vecFour ∉ leechLattice := by
  rw [mem_leechLattice, inLeech_iff]
  rintro (⟨_, hs, _⟩ | ⟨hp, _, _⟩)
  · revert hs; decide
  · have := hp 1; revert this; decide

/-- `(1, 1, …, 1)` is not in the lattice: its total is 24, which leaves remainder 0 on division
by 8, not 4. -/
theorem vecOnes_not_mem : vecOnes ∉ leechLattice := by
  rw [mem_leechLattice, inLeech_iff]
  rintro (⟨hp, _, _⟩ | ⟨_, hs, _⟩)
  · have := hp 0; revert this; decide
  · revert hs; decide

/-- **Smallest length (exact):** 32 is the least squared length of a nonzero vector of the
Leech lattice (scaled by `√8`); `(4, 4, 0, …, 0)` reaches it. -/
theorem leech_min_norm :
    IsLeast {n : ℤ | ∃ x ∈ leechLattice, x ≠ 0 ∧ ∑ i, x i ^ 2 = n} 32 := by
  refine ⟨⟨vecFourFour, vecFourFour_mem, ?_, vecFourFour_norm⟩, ?_⟩
  · intro h
    have := congrFun h 0
    revert this; decide
  · rintro n ⟨x, hx, h0, rfl⟩
    exact leech_norm_ge_32 x hx h0

end LeechLattice
