import LeechThreeE8Data
import LeechBasis
import LeechKissing
import PlaygroundLeech
import E8PlumbingBridge

/-!
# Three orthogonal E₈ lattices, glued to give the Leech lattice

Coordinates retain the project's √8 scale. Each of the three base lattices is
4E₈, so the Gram matrix of its simple roots is −16 times the existing plumbing
matrix. In ordinary Leech units the base is (√2 E₈)³.

The twelve explicit glue vectors and the base generate precisely `leechLattice`.
The finite integer tables are witnesses. Lean's kernel checks them.
The script that found them is not trusted.
-/

namespace LeechThreeE8

open LeechLattice LeechBasis

/-- Three disjoint blocks of eight, written in the existing lattice's coordinates. -/
def coordinate (i : Fin 24) : Fin 24 := Fin.ofNat 24 (coordinateOrder[i.val]?.getD 0)

theorem coordinate_bijective : Function.Bijective coordinate := by decide +kernel

noncomputable def coordinateEquiv : Fin 24 ≃ Fin 24 := Equiv.ofBijective coordinate coordinate_bijective

/-- Splitting into the three coordinate blocks preserves squared length. -/
theorem block_norm (x : Vec) : (∑ i, x (coordinate i) ^ 2) = ∑ i, x i ^ 2 := by
  apply Fintype.sum_equiv coordinateEquiv
  intro i
  rfl

/-- The base is three copies of the eight simple roots above, one per block. -/
theorem base_blocks : ∀ i j : Fin 24,
    base i (coordinate j) = if i.val / 8 = j.val / 8 then
      e8Root (Fin.ofNat 8 i.val) (Fin.ofNat 8 j.val) else 0 := by decide +kernel

/-- The positive E₈ root Gram matrix is the negative of the plumbing form, scaled by 16. -/
theorem e8_gram : ∀ i j : Fin 8,
    (∑ k, e8Root i k * e8Root j k) = -16 * E8PlumbingBridge.E8_matrix i j := by decide +kernel

/-- The three blocks are orthogonal, including their full E₈ Gram matrices. -/
theorem base_gram : ∀ i j : Fin 24,
    (∑ k, base i k * base j k) = if i.val / 8 = j.val / 8 then
      -16 * E8PlumbingBridge.E8_matrix (Fin.ofNat 8 i.val) (Fin.ofNat 8 j.val) else 0 := by
  decide +kernel

def combination {n : Nat} (v : Fin n → Vec) (c : Fin n → ℤ) : Vec := ∑ i, c i • v i

theorem combination_mem {n : Nat} (S : AddSubgroup Vec) (v : Fin n → Vec)
    (hv : ∀ i, v i ∈ S) (c : Fin n → ℤ) : combination v c ∈ S :=
  AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _ (hv i) _

theorem base_in_leech_check : ∀ i j : Fin 24,
    (∑ k, baseInLeech i k * leechBasis k j) = base i j := by decide +kernel

theorem glue_in_leech_check : ∀ i : Fin 12,
    ∃ k : Fin 24, ∀ j, glue i j = leechBasis k j := by decide +kernel

theorem leech_in_glued_check : ∀ i j : Fin 24,
    (∑ k, leechInBase i k * base k j) + (∑ k, leechInGlue i k * glue k j) = leechBasis i j := by
  decide +kernel

theorem twice_glue_check : ∀ i : Fin 12, ∀ j : Fin 24,
    (∑ k, twiceGlue i k * base k j) = 2 * glue i j := by decide +kernel

def baseLattice : AddSubgroup Vec := AddSubgroup.closure (Set.range base)

/-- The construction: integer combinations of three E₈ blocks and twelve glue vectors. -/
def gluedLattice : AddSubgroup Vec := AddSubgroup.closure (Set.range base ∪ Set.range glue)

theorem base_mem (i : Fin 24) : base i ∈ leechLattice := by
  rw [← closure_leechBasis]
  exact mem_basisSpan_of_coeffs (baseInLeech i) (base i) (base_in_leech_check i)

theorem glue_mem (i : Fin 12) : glue i ∈ leechLattice := by
  obtain ⟨k, hk⟩ := glue_in_leech_check i
  rw [show glue i = leechBasis k from funext hk]
  exact leechBasis_mem k

/-- **The three-E₈ construction gives the existing Leech lattice, in both directions.** -/
theorem glued_eq_leech : gluedLattice = leechLattice := by
  apply le_antisymm
  · rw [gluedLattice, AddSubgroup.closure_le]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact base_mem i
    · exact glue_mem i
  · rw [← closure_leechBasis, AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    have h : leechBasis i = combination base (leechInBase i) + combination glue (leechInGlue i) := by
      funext j
      simpa [combination, Finset.sum_apply] using (leech_in_glued_check i j).symm
    rw [h]
    exact add_mem
      (combination_mem _ base (fun k => AddSubgroup.subset_closure (Or.inl ⟨k, rfl⟩)) _)
      (combination_mem _ glue (fun k => AddSubgroup.subset_closure (Or.inr ⟨k, rfl⟩)) _)

theorem twice_glue_mem (i : Fin 12) : (2 : ℤ) • glue i ∈ baseLattice := by
  have h : (2 : ℤ) • glue i = combination base (twiceGlue i) := by
    funext j
    simpa [combination, Finset.sum_apply] using (twice_glue_check i j).symm
  rw [h]
  exact combination_mem baseLattice base
    (fun k => AddSubgroup.subset_closure (Set.mem_range_self k)) _

/-- The old lower bound applies to every vector of the construction, not just a saved list. -/
theorem glued_norm_ge_32 (x : Vec) (hx : x ∈ gluedLattice) (hne : x ≠ 0) :
    32 ≤ ∑ i, x i ^ 2 := by
  rw [glued_eq_leech] at hx
  exact leech_norm_ge_32 x hx hne

/-- Compose with the already proved playground coordinate relabeling. -/
theorem playground_correspondence (x : Vec) :
    PlaygroundLeech.InPlayLeech x ↔ PlaygroundGolay.toLean x ∈ gluedLattice := by
  rw [glued_eq_leech]
  exact PlaygroundLeech.lattice_correspondence x

/-- Reuse the existing basis and determinant; no new volume calculation is needed. -/
theorem glued_basis_and_volume :
    AddSubgroup.closure (Set.range leechBasis) = gluedLattice ∧ basisMatrix.det = 8 ^ 12 := by
  exact ⟨closure_leechBasis.trans glued_eq_leech.symm, basisMatrix_det⟩

abbrev GluedMinimalVectors := {x : Vec // x ∈ gluedLattice ∧ LeechMinimal.normSq x = 32}

noncomputable def gluedMinimalEquiv : GluedMinimalVectors ≃ LeechMinimal.MinimalVectors :=
  Equiv.subtypeEquivRight (fun x => by rw [glued_eq_leech]; rfl)

noncomputable instance : Fintype GluedMinimalVectors :=
  Fintype.ofEquiv LeechMinimal.MinimalVectors gluedMinimalEquiv.symm

/-- Transfer the established shell count through the equality of lattices. -/
theorem glued_kissing_number : Fintype.card GluedMinimalVectors = 196560 := by
  rw [Fintype.card_congr gluedMinimalEquiv, LeechMinimal.leech_kissing_number]

theorem glued_even (x : Vec) (hx : x ∈ gluedLattice) : 16 ∣ ∑ i, x i ^ 2 := by
  rw [glued_eq_leech] at hx
  exact leech_norm_dvd_sixteen x hx

end LeechThreeE8
