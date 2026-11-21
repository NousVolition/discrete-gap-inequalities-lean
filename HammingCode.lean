import Mathlib
import E8PlumbingBridge

/-!
# The extended Hamming code of playground tab 30

Playground tab 30 (the E₈ Inspector) encodes 4-bit messages with the 4×8 generator

```
G = [ I₄ | P ] =
  1 0 0 0  0 1 1 1
  0 1 0 0  1 0 1 1
  0 0 1 0  1 1 0 1
  0 0 0 1  1 1 1 0
```

and then, for each of the 16 codewords, builds 8 half-integer vectors in ℝ⁸. A 1 in
the codeword becomes −1/2 and a 0 becomes +1/2; the other seven vectors are obtained
by flipping the signs in coordinates 0 and k, for k = 1, …, 7.

This file checks those claims, step by step, on the same generator. Every check
runs over a small finite set, inside Lean's kernel. The file also shows that the
128 vectors are exactly the points of `{±1/2}⁸` with an even number of minus signs,
the same 128 even-parity vertices counted in `E8PlumbingBridge.card_spinor_roots`.
It does not prove that those vectors are roots of the lattice attached to the
plumbing matrix `E8_matrix`.
-/

open Matrix
open E8PlumbingBridge (Cube8 isEvenParity)

namespace HammingCode

/-! ## 1. The generator, the encode map, and the 16 codewords -/

/-- The [8, 4, 4] generator used by playground tab 30: `G = [I₄ | P]`, with `P`
the 4×4 matrix that is 0 on the diagonal and 1 off it. The four rows are
`10000111`, `01001011`, `00101101` and `00011110`. -/
def G : Matrix (Fin 4) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 1, 1, 1;
     0, 1, 0, 0, 1, 0, 1, 1;
     0, 0, 1, 0, 1, 1, 0, 1;
     0, 0, 0, 1, 1, 1, 1, 0]

/-- Encode a 4-bit message by right-multiplying by `G`. -/
def encode (m : Fin 4 → ZMod 2) : Fin 8 → ZMod 2 :=
  m ᵥ* G

/-- A length-8 word is a codeword when it is `encode m` for some message `m`. -/
def IsCodeword (c : Fin 8 → ZMod 2) : Prop :=
  ∃ m, encode m = c

/-- The set of all codewords, listed as the image of `encode`. -/
def code : Finset (Fin 8 → ZMod 2) :=
  Finset.univ.image encode

/-- Hamming weight: the number of coordinates equal to `1`. -/
def weight (c : Fin 8 → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i => c i = 1)).card

/-- The ordinary inner product of two length-8 words, as a single bit. -/
def dot (c d : Fin 8 → ZMod 2) : ZMod 2 :=
  ∑ i, c i * d i

/-- Distinct messages give distinct codewords, so there are exactly 16 of them. -/
theorem encode_injective : Function.Injective encode := by
  decide +kernel +revert

/-- There are exactly 16 codewords. -/
theorem card_code : code.card = 16 := by
  classical
  rw [code, Finset.card_image_of_injective _ encode_injective, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, ZMod.card]
  norm_num

/-- Membership in the listed set `code` is the same as being `encode m` for some `m`. -/
theorem mem_code_iff (c : Fin 8 → ZMod 2) : c ∈ code ↔ IsCodeword c := by
  simp [code, IsCodeword, Finset.mem_image]

/-- The weights of the 16 codewords are: 1 of weight 0, 14 of weight 4, and 1 of weight 8. -/
theorem weight_distribution :
    ((Finset.univ.filter (fun m : Fin 4 → ZMod 2 => weight (encode m) = 0)).card,
      (Finset.univ.filter (fun m : Fin 4 → ZMod 2 => weight (encode m) = 4)).card,
      (Finset.univ.filter (fun m : Fin 4 → ZMod 2 => weight (encode m) = 8)).card) =
      (1, 14, 1) := by
  decide +kernel +revert

/-- Every codeword has weight divisible by 4 (the code is doubly even). -/
theorem doubly_even (m : Fin 4 → ZMod 2) : 4 ∣ weight (encode m) := by
  decide +kernel +revert

/-- Every nonzero codeword has weight at least 4, so the minimum distance is at least 4. -/
theorem min_distance {m : Fin 4 → ZMod 2} (hm : m ≠ 0) : 4 ≤ weight (encode m) := by
  decide +kernel +revert

/-- The first generator row has weight 4, so the minimum distance is exactly 4. -/
theorem min_distance_sharp : weight (encode ![1, 0, 0, 0]) = 4 := by
  decide +kernel +revert

/-- The generator is self-orthogonal: `G * Gᵀ = 0` over the two-element field. -/
theorem G_mul_transpose : G * G.transpose = 0 := by
  decide +kernel +revert

/-- Every two codewords have even overlap, which follows from `G * Gᵀ = 0`. -/
theorem self_orthogonal (m₁ m₂ : Fin 4 → ZMod 2) : dot (encode m₁) (encode m₂) = 0 := by
  decide +kernel +revert

/-- The code equals its dual: a word is a codeword exactly when it is orthogonal to
every codeword. Together with `encode_injective` (dimension 4 in length 8) this is
self-duality. -/
theorem code_eq_dual (c : Fin 8 → ZMod 2) :
    c ∈ code ↔ ∀ m, dot c (encode m) = 0 := by
  decide +kernel +revert

/-! ## 2. The eight half-integer vectors the tab builds from each codeword -/

/-- The base half-integer vector for a word: a `1` becomes `-1/2` and a `0` becomes `+1/2`. -/
def baseSpinor (c : Fin 8 → ZMod 2) : Fin 8 → ℚ :=
  fun i => if c i = 1 then (-1 / 2) else (1 / 2)

/-- Flip the signs at coordinates `0` and `k`. When `k = 0` this is the identity,
matching the tab's loop (`k = 0` leaves the base vector alone). -/
def flipPair (k : Fin 8) (v : Fin 8 → ℚ) : Fin 8 → ℚ :=
  fun i => if k ≠ 0 ∧ (i = 0 ∨ i = k) then -v i else v i

/-- The eight half-integer vectors the tab builds from a codeword. -/
def tabSpinors (c : Fin 8 → ZMod 2) (k : Fin 8) : Fin 8 → ℚ :=
  flipPair k (baseSpinor c)

/-- The 128 vectors obtained by applying the tab's rule to every codeword. -/
def allTabSpinors : Finset (Fin 8 → ℚ) :=
  Finset.univ.image fun p : (Fin 4 → ZMod 2) × Fin 8 => tabSpinors (encode p.1) p.2

/-- The pattern of minus signs of a half-integer vector, as a vertex of the 8-cube. -/
def minusPattern (v : Fin 8 → ℚ) : Cube8 :=
  fun i => decide (v i = -1 / 2)

/-- The half-integer vector with a minus sign exactly where the 8-cube vertex is `true`. -/
def evenSpinor (x : Cube8) : Fin 8 → ℚ :=
  fun i => if x i then (-1 / 2) else (1 / 2)

/-- The 128 points of `{±1/2}⁸` with an even number of minus signs. -/
def evenSpinors : Finset (Fin 8 → ℚ) :=
  (Finset.univ.filter (fun x : Cube8 => isEvenParity x = true)).image evenSpinor

/-- Each of the tab's 128 vectors has squared length 2. -/
theorem tabSpinor_sqLength (m : Fin 4 → ZMod 2) (k : Fin 8) :
    ∑ i, tabSpinors (encode m) k i * tabSpinors (encode m) k i = 2 := by
  decide +kernel +revert

/-- Different pairs `(message, flip index)` give different vectors, so the 16 × 8
construction produces 128 distinct vectors. -/
theorem tabSpinor_injective :
    Function.Injective fun p : (Fin 4 → ZMod 2) × Fin 8 => tabSpinors (encode p.1) p.2 := by
  decide +kernel +revert

/-- The tab's rule produces exactly 128 distinct vectors. -/
theorem card_allTabSpinors : allTabSpinors.card = 128 := by
  classical
  rw [allTabSpinors, Finset.card_image_of_injective _ tabSpinor_injective, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card, Fintype.card_fin]
  norm_num

/-- Each of the tab's vectors has an even number of minus signs. -/
theorem tabSpinor_evenParity (m : Fin 4 → ZMod 2) (k : Fin 8) :
    isEvenParity (minusPattern (tabSpinors (encode m) k)) = true := by
  decide +kernel +revert

/-- The 128 vectors the tab builds are exactly the points of `{±1/2}⁸` with an even
number of minus signs, which are the 128 even-parity vertices counted by
`E8PlumbingBridge.card_spinor_roots`. -/
theorem allTabSpinors_eq_evenSpinors : allTabSpinors = evenSpinors := by
  decide +kernel +revert

/-- The count of those vectors agrees with `E8PlumbingBridge.card_spinor_roots`. -/
theorem card_allTabSpinors_eq_spinor_roots :
    allTabSpinors.card =
      (Finset.univ.filter (fun x : Cube8 => isEvenParity x = true)).card := by
  rw [card_allTabSpinors, E8PlumbingBridge.card_spinor_roots]

end HammingCode
