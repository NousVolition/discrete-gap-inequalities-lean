/-
Copyright © 2026 NousVolition. All rights reserved.
-/
import Mathlib
import LeechLattice

/-!
# A basis of the Leech lattice, and why it is unimodular

`LeechLattice.lean` defines the Leech lattice `leechLattice` inside `ℤ²⁴`, with coordinates scaled
up by `√8`. Mathlib has no notion of the volume of a lattice, so this file states unimodularity in
concrete terms, through an explicit basis.

## The basis

`leechBasis` lists 24 vectors (the rows of the matrix `basisMatrix`):

* row 0: `(1, 1, …, 1, -3)`, an odd lattice vector;
* rows 1 to 11: twice the Golay generator rows 1 to 11 from `GolayMatrixDistance.golayGen`;
* rows 12 to 22: `4 eᵢ + 4 e₂₃`;
* row 23: `8 e₂₃`.

Row `i` has its first nonzero entry in column `i`, so the matrix is upper triangular, with
diagonal `1`, then `2` eleven times, then `4` eleven times, then `8`.

## What is proved

* `leechBasis_mem`: every basis vector is in the lattice.
* `closure_leechBasis`: the whole-number combinations of the basis vectors are exactly the
  lattice (`AddSubgroup.closure (Set.range leechBasis) = leechLattice`). The proof takes a lattice
  vector, removes the odd basis vector if its entries are odd, then removes twice the Golay rows
  picked out by its first 12 entries. What is left has every entry a multiple of 4 and total a
  multiple of 8, and such a vector is a combination of `4 eₖ - 4 e₂₃` and `8 e₂₃`. The step "a
  codeword that is zero on its first 12 positions is zero" rests on a check over all 4,096
  messages (`encodeNat_mod_check`). The building blocks (twice each Golay row, `4 eₖ - 4 e₂₃`) are
  written as explicit whole-number combinations of the basis, found by back substitution and
  checked with `decide +kernel`.
* `basisMatrix_det`: the determinant of the basis matrix is `8¹²` (it is upper triangular, so the
  determinant is the product of the diagonal). `leechBasis_linearIndependent`: the 24 vectors are
  linearly independent.
* `leech_unimodular`: the Gram matrix `G = M Mᵀ` (all dot products of basis vectors) has every
  entry divisible by 8, `G / 8` has determinant 1, and every diagonal entry of `G` is divisible by
  16. After dividing the coordinates by `√8`, this says the lattice is unimodular and even.
* `leech_inner_dvd_eight` and `leech_norm_dvd_sixteen`: for any two lattice vectors the dot
  product is divisible by 8, and every lattice vector has squared length divisible by 16. So the
  whole lattice, not only its basis, is integral and even after scaling.

## What is not proved here

The symmetry group of the lattice (Conway's group `Co₀`) is not touched, and this basis is not
compared with other published bases of the Leech lattice.
-/

namespace LeechBasis

open GolayMatrixDistance LeechLattice

/-! ## The basis -/

/-- The 24 basis vectors of the Leech lattice (scaled by `√8`). -/
def leechBasis (i : Fin 24) : Fin 24 → ℤ := fun j =>
  if i.val = 0 then (if j.val = 23 then -3 else 1)
  else if h : i.val < 12 then (if golayGen ⟨i.val, h⟩ j then 2 else 0)
  else if i.val < 23 then (if j = i ∨ j.val = 23 then 4 else 0)
  else (if j.val = 23 then 8 else 0)

/-- The basis as a 24 × 24 matrix (row `i` is `leechBasis i`). -/
def basisMatrix : Matrix (Fin 24) (Fin 24) ℤ := Matrix.of fun i j => leechBasis i j

/-- The Golay message whose codeword marks the entries `≡ 2 (mod 4)` of an even basis vector. -/
def basisMsg (i : Fin 24) : Nat := if i.val < 12 then 2 ^ i.val else 0

theorem leechBasis_zero_odd :
    (∀ j, leechBasis 0 j % 2 = 1) ∧ (∑ j, leechBasis 0 j) % 8 = 4 ∧
      ∀ j, residueSet (leechBasis 0) 3 j = false := by
  decide +kernel

theorem leechBasis_even_facts : ∀ i : Fin 24, i.val ≠ 0 →
    (∀ j, leechBasis i j % 2 = 0) ∧ (∑ j, leechBasis i j) % 8 = 0 ∧ basisMsg i < 4096 ∧
      ∀ j, residueSet (leechBasis i) 2 j = word (encodeNat (basisMsg i)) j := by
  decide +kernel

/-- **Every basis vector is in the lattice.** -/
theorem leechBasis_mem (i : Fin 24) : leechBasis i ∈ leechLattice := by
  rw [mem_leechLattice, inLeech_iff]
  by_cases h0 : i.val = 0
  · have hi : i = 0 := Fin.ext h0
    subst hi
    obtain ⟨hp, hs, hr⟩ := leechBasis_zero_odd
    refine Or.inr ⟨hp, hs, ?_⟩
    have : residueSet (leechBasis 0) 3 = fun _ => false := funext hr
    rw [this]; exact isGolayWord_false
  · obtain ⟨hp, hs, hm, hr⟩ := leechBasis_even_facts i h0
    exact Or.inl ⟨hp, hs, basisMsg i, hm, by funext j; exact (hr j).symm⟩

/-- The subgroup made of the whole-number combinations of the basis vectors. -/
abbrev basisSpan : AddSubgroup (Fin 24 → ℤ) := AddSubgroup.closure (Set.range leechBasis)

theorem basisSpan_le : basisSpan ≤ leechLattice := by
  rw [AddSubgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact leechBasis_mem i

/-- A vector given as an explicit whole-number combination of the basis is in the span. -/
theorem mem_basisSpan_of_coeffs (c : Fin 24 → ℤ) (v : Fin 24 → ℤ)
    (h : ∀ j, ∑ i, c i * leechBasis i j = v j) : v ∈ basisSpan := by
  have hv : v = ∑ i, c i • leechBasis i := by
    funext j
    rw [← h j, Finset.sum_apply]
    simp
  rw [hv]
  exact AddSubgroup.sum_mem _ fun i _ =>
    AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _

/-! ## Building blocks written as combinations of the basis -/

/-- Twice the Golay generator row `k`. -/
def twoRow (k : Fin 12) : Fin 24 → ℤ := fun j => if golayGen k j then 2 else 0

/-- The vector `4 eₖ - 4 e₂₃`. -/
def fourDiff (k : Fin 24) : Fin 24 → ℤ :=
  fun j => (if j = k then 4 else 0) - (if j.val = 23 then 4 else 0)

/-- The vector `8 e₂₃`. -/
def eightLast : Fin 24 → ℤ := fun j => if j.val = 23 then 8 else 0

/-- Coefficients writing `twoRow k` in the basis (found by back substitution). -/
def twoRowTable : List (List ℤ) :=
  [[2, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 5, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, -15],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Coefficients writing `fourDiff k` (for `k < 23`) in the basis (found by back substitution). -/
def fourDiffTable : List (List ℤ) :=
  [[4, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2, 10, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, -26],
    [0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 0, -1, -1, -1, 0, 0, 0, -1, 3],
    [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, -1, 0, -1, -1, -1, 0, 0, 0, 2],
    [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, -1, 0, -1, -1, -1, 0, 0, 3],
    [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, -1, 0, -1, -1, -1, 0, 3],
    [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, -1, -1, 0, -1, -1, -1, 3],
    [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, -1, -1, 0, -1, -1, 2],
    [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, -1, -1, 0, 0, 0, -1, 0, -1, -1, 0, -1, 2],
    [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -1, -1, -1, 0, 0, 0, -1, 0, -1, -1, 0, 2],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, -1, -1, -1, -1, 0, 0, 0, -1, 0, -1, -1, 3],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, -1, 0, -1, -1, -1, 0, 0, 0, -1, 0, -1, 2],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, -1, 0, -1, -1, -1, 0, 0, 0, -1, 0, 2],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1]]

/-- Entry `i` of the coefficients for `twoRow k`. -/
def twoRowCoeff (k : Fin 12) (i : Fin 24) : ℤ := (twoRowTable.getD k.val []).getD i.val 0

/-- Entry `i` of the coefficients for `fourDiff k`. -/
def fourDiffCoeff (k : Fin 24) (i : Fin 24) : ℤ := (fourDiffTable.getD k.val []).getD i.val 0

theorem twoRow_coeffs : ∀ k : Fin 12, ∀ j : Fin 24,
    ∑ i, twoRowCoeff k i * leechBasis i j = twoRow k j := by
  decide +kernel

theorem fourDiff_coeffs : ∀ k : Fin 24, k.val < 23 → ∀ j : Fin 24,
    ∑ i, fourDiffCoeff k i * leechBasis i j = fourDiff k j := by
  decide +kernel

theorem twoRow_mem (k : Fin 12) : twoRow k ∈ basisSpan :=
  mem_basisSpan_of_coeffs _ _ (twoRow_coeffs k)

theorem fourDiff_mem (k : Fin 24) : fourDiff k ∈ basisSpan := by
  by_cases hk : k.val < 23
  · exact mem_basisSpan_of_coeffs _ _ (fourDiff_coeffs k hk)
  · have hk' : k = 23 := Fin.ext (by omega)
    subst hk'
    have : fourDiff 23 = 0 := by
      funext j
      simp only [fourDiff, Pi.zero_apply]
      by_cases hj : j = 23
      · subst hj; simp
      · have : j.val ≠ 23 := fun h => hj (Fin.ext h)
        simp [hj, this]
    rw [this]; exact zero_mem _

theorem eightLast_mem : eightLast ∈ basisSpan :=
  AddSubgroup.subset_closure ⟨23, by funext j; simp [leechBasis, eightLast]⟩

/-! ## Spanning -/

theorem fourDiff_eight_apply (c : Fin 24 → ℤ) (a : ℤ) (j : Fin 24) :
    (∑ k, c k • fourDiff k + a • eightLast) j =
      c j * 4 - (if j.val = 23 then ∑ k, c k * 4 else 0) + (if j.val = 23 then a * 8 else 0) := by
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, fourDiff, eightLast,
    mul_sub, Finset.sum_sub_distrib]
  congr 2
  · simp [mul_ite]
  · split_ifs <;> simp
  · split_ifs <;> simp

/-- **Entries all multiples of 4, total a multiple of 8:** such a vector is a combination of
`4 eₖ - 4 e₂₃` and `8 e₂₃`, so it is in the span. -/
theorem mem_span_of_four {x : Fin 24 → ℤ} (h4 : ∀ i, x i % 4 = 0) (h8 : (∑ i, x i) % 8 = 0) :
    x ∈ basisSpan := by
  set c : Fin 24 → ℤ := fun k => if k.val = 23 then 0 else x k / 4 with hc
  have hsum : ∑ k, c k * 4 = ∑ i, x i - x 23 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (23 : Fin 24)),
      ← Finset.add_sum_erase _ (fun i => x i) (Finset.mem_univ (23 : Fin 24))]
    have : ∀ k ∈ Finset.univ.erase (23 : Fin 24), c k * 4 = x k := by
      intro k hk
      have hk' : k.val ≠ 23 := fun h => (Finset.mem_erase.1 hk).1 (Fin.ext h)
      have := h4 k
      simp only [hc, hk', ite_false]
      omega
    rw [Finset.sum_congr rfl this]
    simp [hc]
  have hx : x = ∑ k, c k • fourDiff k + ((∑ i, x i) / 8) • eightLast := by
    funext j
    rw [fourDiff_eight_apply]
    by_cases hj : j.val = 23
    · have hj' : j = 23 := Fin.ext hj
      subst hj'
      simp only [show ((23 : Fin 24).val = 23) from rfl, ite_true, hsum]
      simp only [hc, show ((23 : Fin 24).val = 23) from rfl, ite_true]
      omega
    · simp only [hj, ite_false, hc]
      have := h4 j
      omega
  rw [hx]
  exact add_mem (AddSubgroup.sum_mem _ fun k _ => AddSubgroup.zsmul_mem _ (fourDiff_mem k) _)
    (AddSubgroup.zsmul_mem _ eightLast_mem _)

/-- Encoding keeps the message in the first 12 bits (the generator is `[I₁₂ | B]`); checked over
all 4,096 messages. -/
theorem encodeNat_mod_check :
    (List.range 4096).all (fun m => (encodeNat m).toNat % 4096 == m) = true := by
  decide +kernel

theorem encodeNat_mod_4096 (m : Nat) (hm : m < 4096) : (encodeNat m).toNat % 4096 = m := by
  have h := encodeNat_mod_check
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h m hm

/-- **A codeword that is zero on its first 12 positions is zero.** -/
theorem golay_eq_false_of_first12 {w : Fin 24 → Bool} (hw : IsGolayWord w)
    (h : ∀ k : Fin 24, k.val < 12 → w k = false) : ∀ k, w k = false := by
  obtain ⟨m, hm, rfl⟩ := hw
  have hbits : ∀ i, m.testBit i = false := by
    intro i
    by_cases hi : i < 12
    · have := h ⟨i, by omega⟩ hi
      simp only [word] at this
      rw [bitAt_eq_testBit _ _ (by omega)] at this
      rw [← encodeNat_mod_4096 m hm, show (4096 : Nat) = 2 ^ 12 by norm_num,
        Nat.testBit_mod_two_pow]
      simp [hi, this]
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hm
        (by calc (4096 : Nat) = 2 ^ 12 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hm0 : m = 0 := Nat.eq_of_testBit_eq (fun i => by rw [hbits i, Nat.zero_testBit])
  subst hm0
  intro k
  rw [encodeNat_zero, word_zero]

theorem twoRow_apply_low (k : Fin 12) (j : Fin 24) (hj : j.val < 12) :
    twoRow k j = if k.val = j.val then 2 else 0 := by
  simp [twoRow, golayGen, hj]

/-- **Even lattice vectors are in the span.** -/
theorem mem_span_of_even {x : Fin 24 → ℤ} (hx : EvenLeech x) : x ∈ basisSpan := by
  set y : Fin 24 → ℤ := ∑ k : Fin 12,
    (if residueSet x 2 (Fin.castLE (by norm_num) k) then (1 : ℤ) else 0) • twoRow k with hy
  have hyS : y ∈ basisSpan :=
    AddSubgroup.sum_mem _ fun k _ => AddSubgroup.zsmul_mem _ (twoRow_mem k) _
  have hxL : x ∈ leechLattice := by rw [mem_leechLattice, inLeech_iff]; exact Or.inl hx
  have hzL : x - y ∈ leechLattice := sub_mem hxL (basisSpan_le hyS)
  have hy_apply : ∀ j, y j = ∑ k : Fin 12,
      (if residueSet x 2 (Fin.castLE (by norm_num) k) then (1 : ℤ) else 0) * twoRow k j := by
    intro j; simp only [hy, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hy_even : ∀ j, y j % 2 = 0 := by
    intro j
    apply Int.emod_eq_zero_of_dvd
    rw [hy_apply]
    apply Finset.dvd_sum
    intro k _
    apply Dvd.dvd.mul_left
    simp only [twoRow]
    split_ifs <;> norm_num
  have hy_low : ∀ j : Fin 24, j.val < 12 →
      y j = if residueSet x 2 j then 2 else 0 := by
    intro j hj
    rw [hy_apply]
    simp only [twoRow_apply_low _ _ hj, mul_ite, mul_zero]
    rw [Finset.sum_eq_single ⟨j.val, hj⟩]
    · have : (Fin.castLE (by norm_num) (⟨j.val, hj⟩ : Fin 12) : Fin 24) = j := Fin.ext rfl
      simp only [this, ite_true]
      split_ifs <;> simp
    · intro k _ hk
      have : k.val ≠ j.val := fun h => hk (Fin.ext h)
      simp [this]
    · simp
  have hzE : EvenLeech (x - y) := by
    rcases (inLeech_iff _).1 hzL with h | h
    · exact h
    · exfalso
      have h1 := h.1 0
      have h2 := hx.1 0
      have h3 := hy_even 0
      simp only [Pi.sub_apply] at h1
      omega
  have hz4 : ∀ j, (x - y) j % 4 = 0 := by
    have hlow : ∀ k : Fin 24, k.val < 12 → residueSet (x - y) 2 k = false := by
      intro k hk
      have h1 := hy_low k hk
      have h2 := hx.1 k
      simp only [residueSet, Pi.sub_apply, Int.reduceMod, decide_eq_false_iff_not] at h1 ⊢
      by_cases h : x k % 4 = 2
      · simp only [h, decide_true, ite_true] at h1; omega
      · simp only [h, decide_false, Bool.false_eq_true, ite_false] at h1; omega
    have hall := golay_eq_false_of_first12 hzE.2.2 hlow
    intro j
    have h1 := hall j
    have h2 := hzE.1 j
    simp only [residueSet, Int.reduceMod, decide_eq_false_iff_not] at h1
    omega
  have hz : x - y ∈ basisSpan := mem_span_of_four hz4 hzE.2.1
  have : x = (x - y) + y := by abel
  rw [this]
  exact add_mem hz hyS

/-- **The basis spans the lattice:** the whole-number combinations of the 24 basis vectors are
exactly the Leech lattice. -/
theorem closure_leechBasis : AddSubgroup.closure (Set.range leechBasis) = leechLattice := by
  apply le_antisymm basisSpan_le
  intro x hx
  rcases (inLeech_iff x).1 hx with he | ho
  · exact mem_span_of_even he
  · have hb0 : leechBasis 0 ∈ basisSpan := AddSubgroup.subset_closure ⟨0, rfl⟩
    have hzL : x - leechBasis 0 ∈ leechLattice := sub_mem hx (leechBasis_mem 0)
    have hzE : EvenLeech (x - leechBasis 0) := by
      rcases (inLeech_iff _).1 hzL with h | h
      · exact h
      · exfalso
        have h1 := h.1 0
        have h2 := ho.1 0
        have h3 := leechBasis_zero_odd.1 0
        simp only [Pi.sub_apply] at h1
        omega
    have : x = (x - leechBasis 0) + leechBasis 0 := by abel
    rw [this]
    exact add_mem (mem_span_of_even hzE) hb0

/-! ## The determinant -/

theorem leechBasis_upper : ∀ i j : Fin 24, j < i → leechBasis i j = 0 := by
  decide +kernel

theorem basisMatrix_upper : basisMatrix.IsUpperTriangular := by
  intro i j hij
  exact leechBasis_upper i j hij

theorem leechBasis_diag_prod : ∏ i, leechBasis i i = 8 ^ 12 := by
  decide +kernel

/-- **The determinant of the basis matrix is `8¹²`.** -/
theorem basisMatrix_det : basisMatrix.det = 8 ^ 12 := by
  rw [Matrix.det_of_isUpperTriangular basisMatrix_upper]
  exact leechBasis_diag_prod

/-- **The 24 basis vectors are linearly independent** over the whole numbers. -/
theorem leechBasis_linearIndependent : LinearIndependent ℤ leechBasis := by
  have h := Matrix.linearIndependent_rows_of_det_ne_zero (A := basisMatrix)
    (by rw [basisMatrix_det]; norm_num)
  exact h

/-! ## The Gram matrix and unimodularity -/

/-- The dot product of basis vectors `i` and `j`. -/
def gram (i j : Fin 24) : ℤ := ∑ k, leechBasis i k * leechBasis j k

theorem gram_dvd_eight : ∀ i j : Fin 24, gram i j % 8 = 0 := by
  decide +kernel

theorem gram_diag_dvd_sixteen : ∀ i : Fin 24, gram i i % 16 = 0 := by
  decide +kernel

/-- The Gram matrix divided by 8. -/
def gramDivEight : Matrix (Fin 24) (Fin 24) ℤ := Matrix.of fun i j => gram i j / 8

theorem basisMatrix_mul_transpose : basisMatrix * basisMatrix.transpose = (8 : ℤ) • gramDivEight := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, gramDivEight,
    Matrix.of_apply, basisMatrix]
  have h := gram_dvd_eight i j
  have : gram i j = 8 * (gram i j / 8) := by omega
  rw [smul_eq_mul, ← this]
  rfl

/-- **The Leech lattice is unimodular and even** (stated for the basis, coordinates scaled by
`√8`): every dot product of basis vectors is divisible by 8, the Gram matrix divided by 8 has
determinant 1, and every squared length of a basis vector is divisible by 16. -/
theorem leech_unimodular :
    (∀ i j, 8 ∣ gram i j) ∧ gramDivEight.det = 1 ∧ (∀ i, 16 ∣ gram i i) := by
  refine ⟨fun i j => Int.dvd_of_emod_eq_zero (gram_dvd_eight i j), ?_,
    fun i => Int.dvd_of_emod_eq_zero (gram_diag_dvd_sixteen i)⟩
  have h := congrArg Matrix.det basisMatrix_mul_transpose
  rw [Matrix.det_mul, Matrix.det_transpose, basisMatrix_det, Matrix.det_smul] at h
  simp only [Fintype.card_fin] at h
  have h8 : (8 : ℤ) ^ 24 ≠ 0 := by norm_num
  apply mul_left_cancel₀ h8
  rw [← h]
  norm_num

/-! ## Every lattice vector, not just the basis -/

/-- **Dot products are divisible by 8** for any two lattice vectors. -/
theorem leech_inner_dvd_eight (x y : Fin 24 → ℤ) (hx : x ∈ leechLattice) (hy : y ∈ leechLattice) :
    8 ∣ ∑ k, x k * y k := by
  rw [← closure_leechBasis] at hx hy
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Int.dvd_of_emod_eq_zero (gram_dvd_eight i j)
    | zero => simp
    | add y z _ _ hy hz =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      exact dvd_add hy hz
    | neg y _ hy =>
      simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
      exact (dvd_neg).2 hy
  | zero => simp
  | add x z _ _ hx hz =>
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    exact dvd_add hx hz
  | neg x _ hx =>
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    exact (dvd_neg).2 hx

/-- **Squared lengths are divisible by 16** for every lattice vector. -/
theorem leech_norm_dvd_sixteen (x : Fin 24 → ℤ) (hx : x ∈ leechLattice) :
    16 ∣ ∑ k, x k ^ 2 := by
  rw [← closure_leechBasis] at hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have := Int.dvd_of_emod_eq_zero (gram_diag_dvd_sixteen i)
    simpa [gram, sq] using this
  | zero => simp
  | add x z hxS hzS hx hz =>
    have hsplit : ∑ k, (x + z) k ^ 2 = ∑ k, x k ^ 2 + ∑ k, z k ^ 2 + 2 * ∑ k, x k * z k := by
      simp only [Pi.add_apply, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
      simp only [mul_assoc]
      ring
    rw [hsplit]
    obtain ⟨t, ht⟩ := leech_inner_dvd_eight x z (basisSpan_le hxS) (basisSpan_le hzS)
    rw [ht]
    exact dvd_add (dvd_add hx hz) ⟨t, by ring⟩
  | neg x _ hx =>
    simpa using hx

end LeechBasis
