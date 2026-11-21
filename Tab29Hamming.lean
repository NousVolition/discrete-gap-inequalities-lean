import HammingCode

open Matrix

/-!
# Tab 29's binary code and Tab 30's existing Hamming code

NEW IN THIS PROJECT: a project-specific formal correspondence, not a novelty claim.
The existing `HammingCode` results are OLD IN THE PROJECT.

This file adds definitions and proofs; it does not change either page encoder or
any existing Lean equation. The separate source-file check establishes that the
page literals match these definitions. Lean does not read the web page.

`writtenG` reads the printed binary literals left to right. `runtimeG` reads the
actual integer masks with bit 0 on the right, as Tab 29's JavaScript does. The
permutations take a target Tab 30 coordinate to its source Tab 29 coordinate.
The four message coordinates always keep their generator-row order.
-/

namespace Tab29Hamming

/-- Tab 29's exact generator masks: 10001110, 01001101, 00101011, 00010111. -/
def rowMasks : Fin 4 → ℕ := ![142, 77, 43, 23]

/-- The same rows in printed left-to-right binary order. -/
def writtenG : Matrix (Fin 4) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 1, 1, 1, 0;
     0, 1, 0, 0, 1, 1, 0, 1;
     0, 0, 1, 0, 1, 0, 1, 1;
     0, 0, 0, 1, 0, 1, 1, 1]

/-- Actual mask-bit order: coordinate b is `(mask >> b) & 1`. -/
def runtimeG (r : Fin 4) (b : Fin 8) : ZMod 2 :=
  if (rowMasks r).testBit b.val then 1 else 0

/-- Keep the first four written positions and reverse the final four. -/
def writtenP : Equiv.Perm (Fin 8) where
  toFun := ![0, 1, 2, 3, 7, 6, 5, 4]
  invFun := ![0, 1, 2, 3, 7, 6, 5, 4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- Account for Tab 29's least-significant-bit-first runtime order. -/
def runtimeP : Equiv.Perm (Fin 8) where
  toFun := ![7, 6, 5, 4, 0, 1, 2, 3]
  invFun := ![4, 5, 6, 7, 3, 2, 1, 0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- Every written generator entry becomes the existing Tab 30 entry. -/
theorem writtenG_relabel (r : Fin 4) (j : Fin 8) :
    writtenG r (writtenP j) = HammingCode.G r j := by
  fin_cases r <;> fin_cases j <;>
    norm_num [writtenG, writtenP, HammingCode.G] <;> decide

/-- The same correspondence for the actual integer-mask bit order. -/
theorem runtimeG_relabel (r : Fin 4) (j : Fin 8) :
    runtimeG r (runtimeP j) = HammingCode.G r j := by
  fin_cases r <;> fin_cases j <;> rfl

def writtenEncode (m : Fin 4 → ZMod 2) : Fin 8 → ZMod 2 :=
  m ᵥ* writtenG

def runtimeEncode (m : Fin 4 → ZMod 2) : Fin 8 → ZMod 2 :=
  m ᵥ* runtimeG

/-- Every message agrees for the fixed generators and printed-coordinate permutation. -/
theorem written_encode_relabel (m : Fin 4 → ZMod 2) (j : Fin 8) :
    writtenEncode m (writtenP j) = HammingCode.encode m j := by
  change (∑ r : Fin 4, m r * writtenG r (writtenP j)) =
    ∑ r : Fin 4, m r * HammingCode.G r j
  simp only [writtenG_relabel]

/-- Every message agrees for the fixed generators and runtime-coordinate permutation. -/
theorem runtime_encode_relabel (m : Fin 4 → ZMod 2) (j : Fin 8) :
    runtimeEncode m (runtimeP j) = HammingCode.encode m j := by
  change (∑ r : Fin 4, m r * runtimeG r (runtimeP j)) =
    ∑ r : Fin 4, m r * HammingCode.G r j
  simp only [runtimeG_relabel]

def writtenCode : Finset (Fin 8 → ZMod 2) :=
  Finset.univ.image writtenEncode

def runtimeCode : Finset (Fin 8 → ZMod 2) :=
  Finset.univ.image runtimeEncode

/-- Equality of the complete written code after relabeling, in both directions. -/
theorem written_code_relabel :
    writtenCode.image (fun v j => v (writtenP j)) = HammingCode.code := by
  classical
  unfold writtenCode HammingCode.code
  rw [Finset.image_image]
  congr 1
  funext m j
  exact written_encode_relabel m j

/-- Equality of the complete runtime code after relabeling, in both directions. -/
theorem runtime_code_relabel :
    runtimeCode.image (fun v j => v (runtimeP j)) = HammingCode.code := by
  classical
  unfold runtimeCode HammingCode.code
  rw [Finset.image_image]
  congr 1
  funext m j
  exact runtime_encode_relabel m j

/-- Transfer injectivity from the existing Tab 30 encoder. -/
theorem runtime_encode_injective : Function.Injective runtimeEncode := by
  intro a b h
  apply HammingCode.encode_injective
  funext j
  rw [← runtime_encode_relabel a j, ← runtime_encode_relabel b j]
  exact congrFun h (runtimeP j)

/-- Hence the mask-based code contains exactly sixteen distinct words. -/
theorem card_runtimeCode : runtimeCode.card = 16 := by
  classical
  rw [runtimeCode, Finset.card_image_of_injective _ runtime_encode_injective,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  norm_num

end Tab29Hamming
