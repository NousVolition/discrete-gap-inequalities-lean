import LeechThreeE8

/-! # The 4,096 allowed shifts of the three E₈ blocks

Every lattice vector belongs to one and only one of the binary glue cosets.
The proof uses twelve integer readouts modulo 8, with all evaluations checked
inside Lean. No external enumeration of the infinite lattice is assumed.
-/
namespace LeechThreeE8

abbrev GlueBits := Fin 12 → Bool

def offset (b : GlueBits) : Vec := ∑ i, if b i then glue i else 0

def readout (k : Fin 12) : Vec →+ ZMod 8 where
  toFun x := ∑ j, (readoutCoeff k j : ZMod 8) * (x j : ZMod 8)
  map_zero' := by simp
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]

theorem readout_base_check : ∀ k : Fin 12, ∀ i : Fin 24, readout k (base i) = 0 := by
  decide +kernel

theorem readout_glue_check : ∀ k i : Fin 12,
    readout k (glue i) = if k = i then 4 else 0 := by decide +kernel

theorem readout_base_zero {x : Vec} (hx : x ∈ baseLattice) (k : Fin 12) :
    readout k x = 0 := by
  have h : baseLattice ≤ (readout k).ker := by
    rw [baseLattice, AddSubgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact readout_base_check k i
  exact h hx

theorem readout_offset (b : GlueBits) (k : Fin 12) :
    readout k (offset b) = if b k then 4 else 0 := by
  rw [offset, map_sum]
  rw [Finset.sum_eq_single k]
  · cases b k <;> simp [readout_glue_check]
  · intro i _ hi
    have hk : k ≠ i := Ne.symm hi
    cases b i <;> simp [readout_glue_check, hk]
  · simp

theorem offset_zero : offset (fun _ => false) = 0 := by simp [offset]

theorem offset_mem_glued (b : GlueBits) : offset b ∈ gluedLattice := by
  apply AddSubgroup.sum_mem
  intro i _
  cases b i <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact zero_mem _
  · exact AddSubgroup.subset_closure (Or.inr ⟨i, rfl⟩)

theorem twice_offset_mem (b : GlueBits) : (2 : ℤ) • offset b ∈ baseLattice := by
  rw [offset, Finset.smul_sum]
  apply AddSubgroup.sum_mem
  intro i _
  cases b i <;> simp only [Bool.false_eq_true, ite_false, ite_true, smul_zero]
  · exact zero_mem _
  · exact twice_glue_mem i

theorem offset_add_carry (b c : GlueBits) :
    offset b + offset c - offset (fun i => b i ^^ c i) ∈ baseLattice := by
  rw [offset, offset, offset, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply AddSubgroup.sum_mem
  intro i _
  cases b i <;> cases c i <;> simp only [Bool.false_xor,
    Bool.true_xor, Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
    zero_add, add_zero, sub_self, sub_zero]
  · exact zero_mem _
  · exact zero_mem _
  · exact zero_mem _
  · simpa [two_smul] using twice_glue_mem i

/-- A union of the 4,096 binary translates of the base. Closure follows from 2g ∈ base. -/
def cosetLattice : AddSubgroup Vec where
  carrier := {x | ∃ b : GlueBits, x - offset b ∈ baseLattice}
  zero_mem' := ⟨fun _ => false, by rw [offset_zero, sub_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro x y ⟨b, hb⟩ ⟨c, hc⟩
    refine ⟨fun i => b i ^^ c i, ?_⟩
    have h := add_mem (add_mem hb hc) (offset_add_carry b c)
    convert h using 1; abel
  neg_mem' := by
    rintro x ⟨b, hb⟩
    refine ⟨b, ?_⟩
    have h := sub_mem (neg_mem hb) (twice_offset_mem b)
    convert h using 1; simp only [two_smul]; abel

theorem base_le_glued : baseLattice ≤ gluedLattice := by
  rw [baseLattice, AddSubgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact AddSubgroup.subset_closure (Or.inl ⟨i, rfl⟩)

theorem coset_eq_glued : cosetLattice = gluedLattice := by
  apply le_antisymm
  · rintro x ⟨b, hb⟩
    have h := add_mem (base_le_glued hb) (offset_mem_glued b)
    simpa using h
  · rw [gluedLattice, AddSubgroup.closure_le]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · refine ⟨fun _ => false, ?_⟩
      rw [offset_zero, sub_zero]
      exact AddSubgroup.subset_closure ⟨i, rfl⟩
    · refine ⟨fun j => decide (j = i), ?_⟩
      have h : offset (fun j => decide (j = i)) = glue i := by simp [offset]
      rw [h, sub_self]
      exact zero_mem _

/-- Different bit strings give different translates of the three-E₈ base. -/
theorem offset_cosets_distinct (b c : GlueBits) (h : offset b - offset c ∈ baseLattice) : b = c := by
  funext k
  have hk := readout_base_zero h k
  rw [map_sub, readout_offset, readout_offset] at hk
  cases hb : b k <;> cases hc : c k <;> simp_all
  all_goals exact (by decide +kernel : (4 : ZMod 8) ≠ 0) hk

/-- **Every Leech vector has a unique binary glue label.** -/
theorem leech_unique_glue (x : Vec) :
    x ∈ LeechLattice.leechLattice ↔ ∃! b : GlueBits, x - offset b ∈ baseLattice := by
  rw [← glued_eq_leech, ← coset_eq_glued]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, hb, ?_⟩
    intro c hc
    apply offset_cosets_distinct c b
    have h := sub_mem hb hc
    convert h using 1; abel
  · rintro ⟨b, hb, _⟩
    exact ⟨b, hb⟩

theorem glue_label_count : Fintype.card GlueBits = 4096 := by decide +kernel

end LeechThreeE8
