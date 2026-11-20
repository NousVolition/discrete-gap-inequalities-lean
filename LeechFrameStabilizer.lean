import LeechMonomial

/-!
# The stabilizer of the standard coordinate frame

Every frame-preserving symmetry factors into a Golay sign change and a
coordinate permutation preserving the code. Identifying the latter group with
a specified generating presentation of M₂₄ is a separate, unfinished step.
-/

namespace LeechSymmetry

open LeechLattice LeechMinimal LeechBasis LeechCodeCounts

def PreservesFrame (g : Aut) : Prop :=
  ∀ i, ∃ j, (g (latticeAxis i)).val = axis j ∨ (g (latticeAxis i)).val = -(axis j)

theorem frame_signed_coordinates (g : Aut) (hg : PreservesFrame g) :
    ∃ p : Equiv.Perm (Fin 24), ∃ b : Fin 24 → Bool,
      ∀ x : Lattice, ∀ i, (g x).val (p i) = if b i then -x.val i else x.val i := by
  classical
  choose p hp using hg
  have hb : ∀ i, ∃ b : Bool, (g (latticeAxis i)).val = if b then -(axis (p i)) else axis (p i) := by
    intro i
    rcases hp i with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  choose b hb using hb
  have hinj : Function.Injective p := by
    intro i j hpij
    by_contra hij
    have hd := map_dot g (latticeAxis i) (latticeAxis j)
    change dot (g (latticeAxis i)).val (g (latticeAxis j)).val = dot (axis i) (axis j) at hd
    rw [hb i, hb j, hpij] at hd
    cases hbi : b i <;> cases hbj : b j <;>
      simp [hbi, hbj, dot, axis, Ne.symm hij, Finset.sum_neg_distrib] at hd
  let e := Equiv.ofBijective p ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨e, b, ?_⟩
  intro x i
  have hd := map_dot g x (latticeAxis i)
  change dot (g x).val (g (latticeAxis i)).val = dot x.val (axis i) at hd
  rw [hb i] at hd
  change (g x).val (p i) = if b i then -x.val i else x.val i
  cases hbi : b i <;> simp [hbi, dot, axis, Finset.sum_neg_distrib] at hd ⊢ <;> omega

theorem residue_isCode {x : Vec} (hx : InLeech x) (k : ℤ) : IsGolayWord (residueSet x k) := by
  obtain ⟨_, _, _, _, h⟩ := hx
  exact h k

theorem signed_coordinates_code (g : Aut) (p : Equiv.Perm (Fin 24)) (b : Fin 24 → Bool)
    (hc : ∀ x : Lattice, ∀ i, (g x).val (p i) = if b i then -x.val i else x.val i) :
    IsCodePermutation p := by
  intro w
  constructor
  · intro hw
    let y : Lattice := ⟨twiceWord w, twiceWord_mem hw⟩
    let z := g⁻¹ y
    have hz : g z = y := g.val.apply_symm_apply y
    have hr : residueSet z.val 2 = fun i => w (p i) := by
      funext i
      have hi := hc z i
      rw [hz] at hi
      change twiceWord w (p i) = if b i then -z.val i else z.val i at hi
      apply Bool.eq_iff_iff.2
      cases hbi : b i <;> cases hwi : w (p i) <;>
        simp [twiceWord, residueSet, hbi, hwi] at hi ⊢ <;> omega
    rw [← hr]
    exact residue_isCode z.property 2
  · intro hw
    let y : Lattice := ⟨twiceWord (fun i => w (p i)), twiceWord_mem hw⟩
    have hr : residueSet (g y).val 2 = w := by
      funext j
      obtain ⟨i, rfl⟩ := p.surjective j
      have hi := hc y i
      change (g y).val (p i) = if b i then -twiceWord (fun i => w (p i)) i
        else twiceWord (fun i => w (p i)) i at hi
      apply Bool.eq_iff_iff.2
      cases hbi : b i <;> cases hwi : w (p i) <;>
        simp [twiceWord, residueSet, hbi, hwi] at hi ⊢ <;> omega
    rw [← hr]
    exact residue_isCode (g y).property 2

theorem signed_coordinates_signs (g : Aut) (p : Equiv.Perm (Fin 24)) (b : Fin 24 → Bool)
    (hc : ∀ x : Lattice, ∀ i, (g x).val (p i) = if b i then -x.val i else x.val i) :
    IsGolayWord b := by
  let y : Lattice := ⟨leechBasis 0, leechBasis_mem 0⟩
  let z := g⁻¹ y
  have hz : g z = y := g.val.apply_symm_apply y
  have hbase : ∀ j : Fin 24, leechBasis 0 j % 4 = 1 := by decide +kernel
  have hr : residueSet z.val 3 = b := by
    funext i
    have hi := hc z i
    rw [hz] at hi
    change leechBasis 0 (p i) = if b i then -z.val i else z.val i at hi
    have hm := hbase (p i)
    apply Bool.eq_iff_iff.2
    cases hbi : b i <;> simp [residueSet, hbi] at hi ⊢ <;> omega
  rw [← hr]
  exact residue_isCode z.property 3

/-- A frame symmetry is a code permutation composed with a Golay sign change. -/
theorem frame_symmetry_factors (g : Aut) (hg : PreservesFrame g) :
    ∃ p : Equiv.Perm (Fin 24), ∃ hp : IsCodePermutation p, ∃ b : Codeword,
      g = permutationAut p.symm (codePermutation_symm p hp) * signAut b := by
  obtain ⟨p, b, hc⟩ := frame_signed_coordinates g hg
  have hp := signed_coordinates_code g p b hc
  have hb := signed_coordinates_signs g p b hc
  refine ⟨p, hp, ⟨b, hb⟩, ?_⟩
  apply Subtype.ext
  ext x i
  have hi := hc x (p.symm i)
  change (g x).val i = if b (p.symm i) then -x.val (p.symm i) else x.val (p.symm i)
  simpa only [Equiv.apply_symm_apply] using hi

theorem signedPermutation_preserves_frame (p : Equiv.Perm (Fin 24))
    (hp : IsCodePermutation p) (b : Codeword) :
    PreservesFrame (permutationAut p.symm (codePermutation_symm p hp) * signAut b) := by
  intro i
  refine ⟨p i, ?_⟩
  have heq : (permutationAut p.symm (codePermutation_symm p hp) * signAut b) (latticeAxis i) =
      if b.val i then -latticeAxis (p i) else latticeAxis (p i) := by
    apply Subtype.ext
    funext j
    change signFlip b.val (axis i) (p.symm j) =
      (if b.val i then -(latticeAxis (p i)) else latticeAxis (p i)).val j
    by_cases hj : j = p i
    · subst j; cases hbi : b.val i <;> simp [axis, signFlip, latticeAxis, hbi]
    · have hpi : p.symm j ≠ i := by intro h; exact hj (by simpa using congrArg p h)
      cases hbi : b.val i <;> simp [axis, signFlip, latticeAxis, hj, hpi]
  cases hbi : b.val i
  · left; simpa [hbi, latticeAxis] using congrArg (fun x : Lattice => x.val) heq
  · right; simpa [hbi, latticeAxis] using congrArg (fun x : Lattice => x.val) heq

theorem frame_stabilizer_iff (g : Aut) : PreservesFrame g ↔
    ∃ p : Equiv.Perm (Fin 24), ∃ hp : IsCodePermutation p, ∃ b : Codeword,
      g = permutationAut p.symm (codePermutation_symm p hp) * signAut b := by
  constructor
  · exact frame_symmetry_factors g
  · rintro ⟨p, hp, b, rfl⟩
    exact signedPermutation_preserves_frame p hp b

/-- A sufficient completeness criterion. Norm-64 transitivity is a hypothesis, not a result here. -/
theorem eq_top_of_norm64_transitive (G : Subgroup Aut)
    (hs : ∀ b : Codeword, signAut b ∈ G)
    (hp : ∀ p : Equiv.Perm (Fin 24), ∀ h : IsCodePermutation p, permutationAut p h ∈ G)
    (ht : ∀ x : Lattice, normSq x.val = 64 → ∃ h : Aut, h ∈ G ∧ h (latticeAxis 0) = x) :
    G = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨h, hh, heq⟩ := ht (g (latticeAxis 0)) ((map_norm g _).trans (axis_norm 0))
  have hfix : (h⁻¹ * g) (latticeAxis 0) = latticeAxis 0 := by
    change h.val.symm (g (latticeAxis 0)) = latticeAxis 0
    rw [← heq]
    exact h.val.symm_apply_apply _
  have hf : PreservesFrame (h⁻¹ * g) := fixes_axis_preserves_frame _ hfix
  obtain ⟨p, hp', b, hk⟩ := frame_symmetry_factors _ hf
  have hmem : h⁻¹ * g ∈ G := by
    rw [hk]
    exact G.mul_mem (hp _ _) (hs b)
  have := G.mul_mem hh hmem
  simpa using this

end LeechSymmetry
