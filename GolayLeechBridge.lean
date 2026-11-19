/-
Copyright © 2026 NousVolition. All rights reserved.
-/
import Mathlib
import GolayMatrixDistance

/-!
# Counting Bridge: the 24-Bit Extended Golay Code and the 24D Leech Lattice

This file checks the **arithmetic** behind the standard description of the
**196,560 shortest vectors** (the kissing number) of the 24-dimensional **Leech lattice**
(`Λ₂₄`), in coordinates built from the **Extended Binary Golay Code** on
`Cube 24 := Fin 24 → Bool`.

What is proved here: the counts add up, and the Golay counts they use are the proved ones.
The weight counts `1, 759, 2576, 759, 1` are written out as the table `golayWeightCount` so the
arithmetic stays quick to check. `golayWeightCount_eq_code` then shows that this table is exactly
the weight distribution proved from the generator matrix in `GolayMatrixDistance.lean`, where all
`4,096` codewords are counted. `leech_kissing_from_code` states the `196,560` count directly in
terms of those proved counts. Nothing here constructs the Leech lattice itself, or proves that the
three shells are exactly its shortest vectors.

The three shells (coordinates scaled by `√8`, so each vector has squared length 32):
* **`(±4)² 0²²` (`1,104`):** any `Nat.choose 24 2 = 276` coordinate pairs, `2²` sign choices.
* **Octad vectors `(±2)⁸ 0¹⁶` (`97,152`):** supported on one of the `759` weight-8 codewords
  (octads), with an even number of minus signs (`759 * 2⁷ = 97,152`).
* **`(∓3)(±1)²³` (`98,304`):** the `-3` in any of the `24` positions, signs flipped on one of
  the `4,096` codewords (`4,096 * 24 = 98,304`).
-/

namespace GolayLeechBridge

/-- The `n`-dimensional hypercube, matching `HypercubeIso.Cube`. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- Extended Binary Golay Code codeword counts by Hamming weight (`0, 8, 12, 16, 24`),
written out as a table; `golayWeightCount_eq_code` shows it matches the proved code counts. -/
def golayWeightCount (w : ℕ) : ℕ :=
  match w with
  | 0 => 1
  | 8 => 759
  | 12 => 2576
  | 16 => 759
  | 24 => 1
  | _ => 0

/-- Sum of the weight table. -/
def golayTotalCodewords : ℕ :=
  golayWeightCount 0 + golayWeightCount 8 + golayWeightCount 12 +
    golayWeightCount 16 + golayWeightCount 24

/-- The weight table adds up to `2¹² = 4,096` (the size of a `[24, 12]` code). -/
theorem golay_total_codewords : golayTotalCodewords = 2 ^ 12 := by
  decide

/-- Number of octads (weight-8 codewords) in the table. -/
def golayOctadCount : ℕ := golayWeightCount 8

theorem golay_octad_count : golayOctadCount = 759 := rfl

/-- Count of shortest vectors of shape `(±4)² 0²²`. -/
def leechShape3Count : ℕ := Nat.choose 24 2 * 2 ^ 2

/-- Count of shortest vectors of shape `(±2)⁸ 0¹⁶` on octads with an even number of minus signs. -/
def leechShape1Count : ℕ := golayOctadCount * 2 ^ 7

/-- Count of shortest vectors of shape `(∓3)(±1)²³`: 24 positions times 4,096 codewords. -/
def leechShape2Count : ℕ := golayTotalCodewords * 24

/-- Sum of the three shell counts. -/
def leechKissingNumber : ℕ :=
  leechShape3Count + leechShape1Count + leechShape2Count

theorem leech_shape3_eq : leechShape3Count = 1104 := by decide

theorem leech_shape1_eq : leechShape1Count = 97152 := by decide

theorem leech_shape2_eq : leechShape2Count = 98304 := by decide

/-- **Main count:** the three shells add up to `196,560`, the Leech kissing number. -/
theorem leech_kissing_decomposition :
    leechShape3Count + leechShape1Count + leechShape2Count = 196560 := by
  decide

/-- **Two counts side by side:** the `E₈` root count (`28 * 4 + 128 = 240`) and the
three-shell Leech count (`196,560`). These are two separate arithmetic facts; the structural
link between them (E₈ from the Hamming code, the Golay code from three copies of the Hamming
code, the Leech lattice from the Golay code) is not formalized here. -/
theorem E8_and_Leech_summary :
    (Nat.choose 8 2 * 2 ^ 2 + 2 ^ 7 = 240) ∧ (leechKissingNumber = 196560) := by
  decide

/-- **The table is the proved code:** the written-out weight table equals the weight
distribution of the code built from the generator matrix in `GolayMatrixDistance.lean`
(weights `0, 8, 12, 16, 24`). -/
theorem golayWeightCount_eq_code :
    (golayWeightCount 0, golayWeightCount 8, golayWeightCount 12,
      golayWeightCount 16, golayWeightCount 24) = GolayMatrixDistance.weightCounts := by
  rw [GolayMatrixDistance.golay_weight_distribution]
  rfl

/-- **The 196,560 count from the proved code:** reading the octad count and the total number
of codewords straight from the proved weight distribution, the three shells add up to `196,560`. -/
theorem leech_kissing_from_code :
    Nat.choose 24 2 * 2 ^ 2 + GolayMatrixDistance.weightCounts.2.1 * 2 ^ 7 +
      (GolayMatrixDistance.weightCounts.1 + GolayMatrixDistance.weightCounts.2.1 +
        GolayMatrixDistance.weightCounts.2.2.1 + GolayMatrixDistance.weightCounts.2.2.2.1 +
        GolayMatrixDistance.weightCounts.2.2.2.2) * 24 = 196560 := by
  rw [GolayMatrixDistance.golay_weight_distribution]
  decide

end GolayLeechBridge
