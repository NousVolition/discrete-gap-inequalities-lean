/-
Copyright © 2026 NousVolition. All rights reserved.
-/
import Mathlib

/-!
# Counting Bridge: the 24-Bit Extended Golay Code and the 24D Leech Lattice

This file checks the **arithmetic** behind the standard description of the
**196,560 shortest vectors** (the kissing number) of the 24-dimensional **Leech lattice**
(`Λ₂₄`), in coordinates built from the **Extended Binary Golay Code** on
`Cube 24 := Fin 24 → Bool`.

What is proved here: the counts add up. The weight counts `1, 759, 2576, 759, 1` of the
Golay code are entered by hand (as the table `golayWeightCount`), and every theorem below is
arithmetic on those numbers. Nothing here constructs the Golay code or the Leech lattice, or
proves that these are their true counts. A first-principles version would define the code from
a generator matrix, enumerate its `4,096` codewords, and count weights.

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
entered by hand (the standard values; not derived in this file). -/
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

end GolayLeechBridge
