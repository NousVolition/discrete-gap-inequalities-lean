import ConwayTransitivity

/-! # A finite generating family for the full lattice symmetry group -/

namespace ConwayGenerators

open GolayMathieu ConwayMoves LeechSymmetry LeechSextet LeechCodeCounts

def liftPerm : level 0 →* Aut where
  toFun p := permutationAut p.val.symm (codePermutation_symm p.val p.property.1)
  map_one' := by apply Subtype.ext; apply Equiv.ext; intro x; rfl
  map_mul' _ _ := by apply Subtype.ext; apply Equiv.ext; intro x; rfl

noncomputable def listedPerm (r : RepIndex) : Aut :=
  liftPerm ⟨rep r, (level_zero_iff _).2 (rep_code r)⟩

def listed : Set Aut := Set.range signAut ∪ Set.range listedPerm ∪ {symmetry}

/-- The Golay sign changes, the 129 listed reorderings and the sextet involution
generate all origin-fixing lattice symmetries. -/
theorem listed_generate : Subgroup.closure listed = ⊤ := by
  let H := Subgroup.closure listed
  let K := (H.comap liftPerm).map (level 0).subtype
  have incl : level 0 ≤ K := by
    rw [← generators_complete]
    apply (Subgroup.closure_le _).2
    rintro _ ⟨r,rfl⟩
    refine ⟨⟨rep r,(level_zero_iff _).2 (rep_code r)⟩,?_,rfl⟩
    exact Subgroup.subset_closure (Or.inl (Or.inr ⟨r,rfl⟩) : listedPerm r ∈ listed)
  have contains : ∀ p : level 0, liftPerm p ∈ H := by
    intro p
    obtain ⟨q,hq,he⟩ := incl p.property
    have eq : q=p := Subtype.ext he
    exact eq ▸ hq
  have all : G ≤ H := by
    apply (Subgroup.closure_le _).2
    rintro g ((⟨w,rfl⟩|⟨p,hp,rfl⟩)|h)
    · exact Subgroup.subset_closure (Or.inl (Or.inl ⟨w,rfl⟩) : signAut w ∈ listed)
    · exact contains ⟨p.symm,(level_zero_iff _).2 (codePermutation_symm p hp)⟩
    · exact Subgroup.subset_closure (Or.inr h : g ∈ listed)
  rw [generators_span_aut] at all
  exact top_unique all

end ConwayGenerators
