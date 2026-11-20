import ConwayOrder
import ConwayTransitivity

/-! # Coordinate frames of the Leech lattice

A frame contains 48 lattice vectors of squared length 64 in one class modulo
twice the lattice. The vectors include both signs of each of the 24 axes.
-/

namespace LeechCoordinateFrames

open LeechSymmetry LeechMinimal LeechLattice LeechCodeCounts GolayMathieu
open ConwayStabilizer

/-- An unordered set of 48 norm-64 lattice vectors, all congruent modulo twice the lattice. -/
def IsCoordinateFrame (s : Finset Lattice) : Prop :=
  s.card = 48 ∧ (∀ x ∈ s, normSq x.val = 64) ∧
    ∀ x ∈ s, ∀ y ∈ s, SameModTwo x.val y.val

abbrev Frame := {s : Finset Lattice // IsCoordinateFrame s}

private theorem congr_symm {x y : Vec} (h : SameModTwo x y) : SameModTwo y x := by
  obtain ⟨z,hz⟩ := h
  refine ⟨-z, ?_⟩
  change y - x = 2 • (-z.val)
  rw [smul_neg, ← hz, neg_sub]

private def toLattice : StandardFrame ↪ Lattice where
  toFun x := ⟨x.val, by
    obtain ⟨i,h|h⟩ := (standard_class_iff _).1 x.property
    · rw [h]; exact axis_mem i
    · rw [h]; exact leechLattice.neg_mem (axis_mem i)⟩
  inj' := fun _ _ h => Subtype.ext (congrArg (fun y : Lattice => y.val) h)

private noncomputable def axes : Finset Lattice := Finset.univ.map toLattice

private theorem mem_axes (x : Lattice) :
    x ∈ axes ↔ normSq x.val = 64 ∧ SameModTwo x.val (axis 0) := by
  constructor
  · intro h
    obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp h
    exact a.property
  · intro h
    exact Finset.mem_map.mpr ⟨⟨x.val,h⟩,Finset.mem_univ _,rfl⟩

noncomputable def standard : Frame :=
  ⟨axes, by
    refine ⟨?_,fun x hx => ((mem_axes x).1 hx).1,?_⟩
    · rw [axes,Finset.card_map,Finset.card_univ,card_standardFrame]
    · intro x hx y hy
      exact sameModTwo_trans ((mem_axes x).1 hx).2 (congr_symm ((mem_axes y).1 hy).2)⟩

private def transport (g : Aut) (f : Frame) : Frame :=
  ⟨f.val.map g.val.toEmbedding, by
    refine ⟨(Finset.card_map _).trans f.property.1,?_,?_⟩
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hy
      exact (map_norm g x).trans (f.property.2.1 x hx)
    · intro y hy z hz
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hy
      obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hz
      exact map_sameModTwo g (f.property.2.2 a ha b hb)⟩

instance : MulAction Aut Frame where
  smul := transport
  one_smul f := by
    apply Subtype.ext
    exact Finset.map_refl
  mul_smul g h f := by
    apply Subtype.ext
    change f.val.map (g*h).val.toEmbedding = (f.val.map h.val.toEmbedding).map g.val.toEmbedding
    rw [Finset.map_map]; rfl

private theorem axis_in_standard (i : Fin 24) : latticeAxis i ∈ standard.val :=
  (mem_axes _).2 ⟨axis_norm i,axes_sameModTwo i 0⟩

private theorem shared_member {f : Frame} {x : Lattice}
    (hf : x ∈ f.val) (hs : x ∈ standard.val) : f = standard := by
  apply Subtype.ext
  apply Finset.eq_of_subset_of_card_le _ (le_of_eq (standard.property.1.trans f.property.1.symm))
  intro y hy
  exact (mem_axes y).2 ⟨f.property.2.1 y hy,
    sameModTwo_trans (f.property.2.2 y hy x hf) ((mem_axes x).1 hs).2⟩

/-- Every set satisfying the frame definition is an image of the standard frame. -/
theorem frame_transitive (f : Frame) : ∃ g : Aut, g • standard = f := by
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < f.val.card by rw [f.property.1]; decide)
  obtain ⟨g,_,hg⟩ := ConwayMoves.norm64_transitive x (f.property.2.1 x hx)
  have hmem : latticeAxis 0 ∈ (g⁻¹ • f).val := by
    exact Finset.mem_map.mpr ⟨x,hx,g.val.symm_apply_eq.mpr hg.symm⟩
  obtain he := shared_member hmem (axis_in_standard 0)
  rw [← he]
  exact ⟨g,smul_inv_smul g f⟩

private theorem fixes_standard_iff (g : Aut) : g • standard = standard ↔ PreservesFrame g := by
  have inside (i : Fin 24) : g (latticeAxis i) ∈ (g • standard).val :=
    Finset.mem_map.mpr ⟨_,axis_in_standard i,rfl⟩
  constructor
  · intro h i
    have hi := inside i
    rw [h] at hi
    exact (standard_class_iff _).1 ((mem_axes _).1 hi)
  · intro h
    exact shared_member (inside 0) ((mem_axes _).2 ((standard_class_iff _).2 (h 0)))

private def signedMap (p : level 0 × Codeword) : MulAction.stabilizer Aut standard :=
  ⟨monomial p.1.val p.1.property.1 p.2,
    (fixes_standard_iff _).2 (signedPermutation_preserves_frame p.1.val p.1.property.1 p.2)⟩

private theorem signedMap_bijective : Function.Bijective signedMap := by
  constructor
  · rintro ⟨p,w⟩ ⟨q,v⟩ h
    have he (i : Point) : (p.val i,w.val i) = (q.val i,v.val i) := by
      apply frameVector_injective; apply Subtype.ext
      rw [← monomial_axis p.val p.property.1 w, ← monomial_axis q.val q.property.1 v]
      exact congrArg (fun z : MulAction.stabilizer Aut standard => (z.val (latticeAxis i)).val) h
    apply Prod.ext
    · apply Subtype.ext; apply Equiv.ext; intro i; exact congrArg Prod.fst (he i)
    · apply Subtype.ext; funext i; exact congrArg Prod.snd (he i)
  · rintro ⟨g,hg⟩
    obtain ⟨p,hp,w,rfl⟩ := frame_symmetry_factors g ((fixes_standard_iff g).1 hg)
    exact ⟨(⟨p,(level_zero_iff p).2 hp⟩,w),rfl⟩

theorem card_frame_stabilizer : Nat.card (MulAction.stabilizer Aut standard) = 244823040 * 4096 := by
  rw [← Nat.card_congr (Equiv.ofBijective signedMap signedMap_bijective), Nat.card_prod,
    card_mathieu,Nat.card_eq_fintype_card (α := Codeword),card_codeword]

/-- Count all unordered 48-element sets satisfying the norm and congruence conditions. -/
theorem card_coordinate_frames :
    Nat.card {s : Finset Lattice // IsCoordinateFrame s} = 8292375 := by
  have ho : MulAction.orbit Aut standard = Set.univ := Set.eq_univ_of_forall frame_transitive
  have hc : Nat.card (MulAction.orbit Aut standard) = Nat.card Frame := by
    rw [ho]; exact Nat.card_congr (Equiv.Set.univ _)
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Aut standard)
  rw [Nat.card_prod,hc,card_frame_stabilizer,ConwayOrder.card_aut] at h
  change Nat.card Frame = 8292375
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 244823040 * 4096) h

/-- Every lattice vector of squared length 64 belongs to a unique coordinate frame. -/
theorem existsUnique_frame_of_norm64 (x : Lattice) (hx : normSq x.val = 64) :
    ∃! f : Frame, x ∈ f.val := by
  obtain ⟨g, _, hg⟩ := ConwayMoves.norm64_transitive x hx
  refine ⟨g • standard, Finset.mem_map.mpr ⟨latticeAxis 0, axis_in_standard 0, hg⟩, ?_⟩
  intro f hf
  have haxis : latticeAxis 0 ∈ (g⁻¹ • f).val :=
    Finset.mem_map.mpr ⟨x, hf, g.val.symm_apply_eq.mpr hg.symm⟩
  have hstandard := shared_member haxis (axis_in_standard 0)
  rw [← hstandard, smul_inv_smul]

/-- Counting the 48 members of every frame gives the size of the squared-length-64 shell. -/
theorem card_norm64_vectors :
    Nat.card {x : Lattice // normSq x.val = 64} = 398034000 := by
  let forget : (Σ f : Frame, ↥f.val) → {x : Lattice // normSq x.val = 64} :=
    fun ⟨f, x⟩ => ⟨x.val, f.property.2.1 x.val x.property⟩
  have bij : Function.Bijective forget := by
    constructor
    · rintro ⟨f, x⟩ ⟨g, y⟩ h
      have hxy : x.val = y.val := congrArg Subtype.val h
      have hu := existsUnique_frame_of_norm64 x.val (f.property.2.1 x.val x.property)
      have hfg : f = g := hu.unique x.property (hxy ▸ y.property)
      subst g
      exact congrArg (Sigma.mk f) (Subtype.ext hxy)
    · intro x
      obtain ⟨f, hf, _⟩ := existsUnique_frame_of_norm64 x.val x.property
      exact ⟨⟨f, x.val, hf⟩, Subtype.ext rfl⟩
  let positions : (Σ f : Frame, ↥f.val) ≃ Frame × Fin 48 :=
    Equiv.sigmaEquivProdOfEquiv fun f : Frame => Finset.equivFinOfCardEq f.property.1
  calc
    Nat.card {x : Lattice // normSq x.val = 64} =
        Nat.card (Frame × Fin 48) :=
      Nat.card_congr ((Equiv.ofBijective forget bij).symm.trans positions)
    _ = 8292375 * 48 := by rw [Nat.card_prod, card_coordinate_frames, Nat.card_fin]
    _ = 398034000 := by decide

end LeechCoordinateFrames
