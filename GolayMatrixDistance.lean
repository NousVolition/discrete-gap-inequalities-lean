/-!
# The extended binary Golay code

The extended binary Golay code is the length-24, dimension-12 binary code with generator
`G = [I₁₂ | B]`, where the 12×12 parity block `B` is built from the quadratic residues modulo 11:
row 0 is `011111111111`, and rows 1 through 11 are the circulant of the pattern
`[1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0]` coming from `{1, 3, 4, 5, 9}`.

This file checks every one of the 4,096 codewords:

* The generator is self-orthogonal (`golay_self_orthogonal`), so the code is self-dual.
* Every codeword is doubly even, and every nonzero codeword has Hamming weight at least 8
  (`golay_doubly_even_and_d_min_8`, `golay_min_distance_bound`).
* The bound 8 is met (`golay_sharp_weight_8`).
* The weight distribution is 1, 759, 2576, 759, 1 for weights 0, 8, 12, 16, 24
  (`golay_weight_distribution`).

The exhaustive checks use `decide +kernel`. Mathlib has no Golay code.
-/

namespace GolayMatrixDistance

/-- Standard 12x12 parity submatrix B of the Extended Binary Golay Code [24, 12, 8].
    Row 0 is [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    and rows 1..11 form a circulant matrix from quadratic residues mod 11:
    {1, 3, 4, 5, 9} -> pattern [1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0]. -/
def golayParityRow : Fin 12 → Array Bool
  | ⟨0, _⟩  => #[false, true,  true,  true,  true,  true,  true,  true,  true,  true,  true,  true]
  | ⟨1, _⟩  => #[true,  true,  true,  false, true,  true,  true,  false, false, false, true,  false]
  | ⟨2, _⟩  => #[true,  false, true,  true,  false, true,  true,  true,  false, false, false, true]
  | ⟨3, _⟩  => #[true,  true,  false, true,  true,  false, true,  true,  true,  false, false, false]
  | ⟨4, _⟩  => #[true,  false, true,  false, true,  true,  false, true,  true,  true,  false, false]
  | ⟨5, _⟩  => #[true,  false, false, true,  false, true,  true,  false, true,  true,  true,  false]
  | ⟨6, _⟩  => #[true,  false, false, false, true,  false, true,  true,  false, true,  true,  true]
  | ⟨7, _⟩  => #[true,  true,  false, false, false, true,  false, true,  true,  false, true,  true]
  | ⟨8, _⟩  => #[true,  true,  true,  false, false, false, true,  false, true,  true,  false, true]
  | ⟨9, _⟩  => #[true,  true,  true,  true,  false, false, false, true,  false, true,  true,  false]
  | ⟨10, _⟩ => #[true,  false, true,  true,  true,  false, false, false, true,  false, true,  true]
  | ⟨11, _⟩ => #[true,  true,  false, true,  true,  true,  false, false, false, true,  false, true]

/-- Entry (i, j) of the 12x12 parity submatrix B. -/
def B_entry (i j : Fin 12) : Bool :=
  (golayParityRow i).getD j.val false

/-- Entry (i, k) of the full 12x24 Extended Binary Golay generator matrix G = [I_12 | B]. -/
def golayGen (i : Fin 12) (k : Fin 24) : Bool :=
  if h : k.val < 12 then
    decide (i.val = k.val)
  else
    B_entry i ⟨k.val - 12, by omega⟩

/-- Fast 24-bit word representation as a UInt32 for rapid decidable verification across all 4,096 codewords. -/
def genRowMask (i : Fin 12) : UInt32 :=
  (List.range 24).foldl (fun acc idx =>
    if h : idx < 24 then
      if golayGen i ⟨idx, h⟩ then acc ||| (1 <<< idx.toUInt32) else acc
    else acc) 0

/-- Precomputed array of the 12 generator rows as 24-bit masks. -/
def genMasks : Array UInt32 :=
  #[genRowMask 0, genRowMask 1, genRowMask 2, genRowMask 3,
    genRowMask 4, genRowMask 5, genRowMask 6, genRowMask 7,
    genRowMask 8, genRowMask 9, genRowMask 10, genRowMask 11]

/-- Encode a 12-bit message (represented as a natural number m < 4096) into a 24-bit Golay codeword. -/
def encodeNat (m : Nat) : UInt32 :=
  (List.range 12).foldl (fun acc i =>
    if (m >>> i) &&& 1 == 1 then
      acc ^^^ (genMasks.getD i 0)
    else
      acc) 0

/-- Hamming weight (number of 1-bits) of a 24-bit word. -/
def popcount24 (w : UInt32) : Nat :=
  (List.range 24).foldl (fun acc b =>
    if (w >>> b.toUInt32) &&& 1 == 1 then acc + 1 else acc) 0

/-- Exhaustive check across all 4,096 messages m in 0..4095:
    1. Every nonzero codeword has Hamming weight >= 8.
    2. Every codeword has Hamming weight divisible by 4 (doubly-even self-dual property). -/
def checkAllCodewords : Bool :=
  (List.range 4096).all fun m =>
    let cw := encodeNat m
    let wt := popcount24 cw
    (wt % 4 == 0) && (m == 0 || wt >= 8)

/-- Exhaustive check that all pairs of generator rows are orthogonal mod 2. -/
def checkSelfOrthogonal : Bool :=
  (List.range 12).all fun i =>
    (List.range 12).all fun j =>
      let overlap := popcount24 ((genMasks.getD i 0) &&& (genMasks.getD j 0))
      overlap % 2 == 0

/-- Theorem 1: Every generator row pair has even overlap (G * G^T = 0 mod 2), proving self-duality. -/
theorem golay_self_orthogonal : checkSelfOrthogonal = true := by
  decide

/-- Theorem 2: All 4,096 codewords of the Extended Binary Golay Code are doubly-even (weight % 4 = 0)
    and every nonzero codeword has Hamming weight >= 8. -/
theorem golay_doubly_even_and_d_min_8 : checkAllCodewords = true := by
  decide +kernel

/-- Theorem 3: The minimum distance d_min = 8 is achieved sharply (e.g., on message m = 2, row 1). -/
theorem golay_sharp_weight_8 : popcount24 (encodeNat 2) = 8 := by
  decide

/-- Corollary: Every nonzero message m (1 <= m < 4096) encodes to a codeword of Hamming weight >= 8. -/
theorem golay_min_distance_bound (m : Nat) (hm1 : 1 ≤ m) (hm2 : m < 4096) :
    8 ≤ popcount24 (encodeNat m) := by
  have h := golay_doubly_even_and_d_min_8
  simp only [checkAllCodewords, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at h
  have hm := h m hm2
  rcases hm.2 with hzero | hge
  · omega
  · exact hge

/-- Count the codewords of weight 0, 8, 12, 16, 24 among messages `start .. start+255`.
    (Done in blocks of 256 so Lean's kernel never builds a 4,096-deep sum.) -/
def blockCounts (start : Nat) : Nat × Nat × Nat × Nat × Nat :=
  (List.range 256).foldl (fun (a, b, c, d, e) k =>
    let w := popcount24 (encodeNat (start + k))
    if w == 0 then (a + 1, b, c, d, e)
    else if w == 8 then (a, b + 1, c, d, e)
    else if w == 12 then (a, b, c + 1, d, e)
    else if w == 16 then (a, b, c, d + 1, e)
    else if w == 24 then (a, b, c, d, e + 1)
    else (a, b, c, d, e)) (0, 0, 0, 0, 0)

/-- Weight counts over all 4,096 codewords: (weight 0, 8, 12, 16, 24). -/
def weightCounts : Nat × Nat × Nat × Nat × Nat :=
  (List.range 16).foldl (fun (a, b, c, d, e) blk =>
    let (a', b', c', d', e') := blockCounts (blk * 256)
    (a + a', b + b', c + c', d + d', e + e')) (0, 0, 0, 0, 0)

/-- Theorem 4: The weight distribution, computed from the generator matrix (not typed in):
    1 codeword of weight 0, 759 of weight 8 (octads), 2576 of weight 12 (dodecads),
    759 of weight 16, and 1 of weight 24. Together with Theorem 2 (every weight is a
    multiple of 4 and nonzero weights are at least 8) these account for all 4,096. -/
theorem golay_weight_distribution : weightCounts = (1, 759, 2576, 759, 1) := by
  decide +kernel

end GolayMatrixDistance
