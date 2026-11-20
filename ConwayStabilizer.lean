import ConwayMoves

/-! # The pointwise stabilizer of two coordinate axes -/

namespace ConwayStabilizer

open GolayMathieu ConwayMoves LeechSymmetry LeechLattice LeechCodeCounts

abbrev Signs := {w : Codeword // w.val 0 = false ∧ w.val 1 = false}
abbrev FixAxes := {g : Aut // g (latticeAxis 0) = latticeAxis 0 ∧ g (latticeAxis 1) = latticeAxis 1}

def bits (w : Codeword) : Bool × Bool := (w.val 0,w.val 1)

noncomputable def mask (p : Bool × Bool) : Codeword :=
  (four_signs (fun i => if i=0 then p.1 else p.2)).choose

theorem mask_bits (p : Bool × Bool) : bits (mask p) = p := by
  have h := (four_signs (fun i => if i=0 then p.1 else p.2)).choose_spec
  exact Prod.ext (h 0) (h 1)

def flip (w v : Codeword) : Codeword :=
  ⟨fun i => w.val i ^^ v.val i, isGolayWord_xor w.property v.property⟩

noncomputable def splitSigns : Codeword ≃ (Bool × Bool) × Signs where
  toFun w := ⟨bits w, ⟨flip w (mask (bits w)), by
    have h := mask_bits (bits w)
    have h0 := congrArg Prod.fst h
    have h1 := congrArg Prod.snd h
    change (mask (bits w)).val 0 = w.val 0 at h0
    change (mask (bits w)).val 1 = w.val 1 at h1
    change (w.val 0 ^^ _) = false ∧ (w.val 1 ^^ _) = false
    simp [h0,h1]⟩⟩
  invFun p := flip p.2.val (mask p.1)
  left_inv w := by apply Subtype.ext; funext i; simp [flip]
  right_inv := by
    rintro ⟨p,w⟩
    have hb : bits (flip w.val (mask p)) = p := by
      refine Eq.trans ?_ (mask_bits p)
      apply Prod.ext <;> simp [bits,flip,w.property.1,w.property.2]
    apply Prod.ext hb
    apply Subtype.ext; apply Subtype.ext; funext i
    change (w.val.val i ^^ (mask p).val i ^^ (mask (bits (flip w.val (mask p)))).val i) = _
    simp [hb]

theorem card_signs : Nat.card Signs = 1024 := by
  have h := Nat.card_congr splitSigns
  rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
    Nat.card_eq_fintype_card (α := Codeword),card_codeword] at h
  omega

theorem card_reorderings_fix_two : Nat.card (level 2) = 443520 := by
  have h0 : Nat.card (level 0) = 24 * Nat.card (level 1) := card_step 0
  have h1 : Nat.card (level 1) = 23 * Nat.card (level 2) := card_step 1
  have h := card_mathieu
  omega

def monomial (p : Perm) (hp : IsCodePermutation p) (w : Codeword) : Aut :=
  permutationAut p.symm (codePermutation_symm p hp) * signAut w

theorem monomial_axis (p : Perm) (hp : IsCodePermutation p) (w : Codeword) (i : Point) :
    (monomial p hp w (latticeAxis i)).val = (frameVector (p i,w.val i)).val := by
  funext j
  obtain ⟨k,rfl⟩ := p.surjective j
  change signFlip w.val (axis i) (p.symm (p k)) = _
  rw [p.symm_apply_apply]
  by_cases h : k=i
  · subst k; cases hw : w.val i <;> simp [frameVector,signFlip,axis,hw]
  · cases hw : w.val i <;> cases hk : w.val k <;> simp [frameVector,signFlip,axis,hk,h]

theorem monomial_fixes_iff (p : Perm) (hp : IsCodePermutation p) (w : Codeword) (i : Point) :
    monomial p hp w (latticeAxis i) = latticeAxis i ↔ p i = i ∧ w.val i = false := by
  constructor
  · intro h
    have he : frameVector (p i,w.val i) = frameVector (i,false) :=
      Subtype.ext ((monomial_axis p hp w i).symm.trans (congrArg Subtype.val h))
    exact Prod.mk.inj (frameVector_injective he)
  · rintro ⟨h,k⟩; apply Subtype.ext; rw [monomial_axis,h,k]; rfl

def assemble (p : level 2 × Signs) : FixAxes :=
  ⟨monomial p.1.val p.1.property.1 p.2.val,
    (monomial_fixes_iff ..).2 ⟨p.1.property.2 0 (by decide),p.2.property.1⟩,
    (monomial_fixes_iff ..).2 ⟨p.1.property.2 1 (by decide),p.2.property.2⟩⟩

theorem assemble_bijective : Function.Bijective assemble := by
  constructor
  · rintro ⟨p,w⟩ ⟨q,v⟩ h
    have he (i : Point) : (p.val i,w.val.val i) = (q.val i,v.val.val i) := by
      apply frameVector_injective; apply Subtype.ext
      rw [← monomial_axis p.val p.property.1 w.val, ← monomial_axis q.val q.property.1 v.val]
      exact congrArg (fun z : FixAxes => (z.val (latticeAxis i)).val) h
    apply Prod.ext
    · apply Subtype.ext; apply Equiv.ext; intro i; exact congrArg Prod.fst (he i)
    · apply Subtype.ext; apply Subtype.ext; funext i; exact congrArg Prod.snd (he i)
  · rintro ⟨g,hg0,hg1⟩
    obtain ⟨p,hp,w,rfl⟩ := frame_symmetry_factors g (fixes_axis_preserves_frame g hg0)
    obtain ⟨h0,b0⟩ := (monomial_fixes_iff p hp w 0).1 hg0
    obtain ⟨h1,b1⟩ := (monomial_fixes_iff p hp w 1).1 hg1
    have fixes : Fixes 2 p := by
      intro i hi
      have h : i=0 ∨ i=1 := by omega
      rcases h with rfl|rfl
      · exact h0
      · exact h1
    exact ⟨(⟨p,hp,fixes⟩,⟨w,b0,b1⟩),rfl⟩

theorem card_fix_axes : Nat.card FixAxes = 454164480 := by
  rw [← Nat.card_congr (Equiv.ofBijective assemble assemble_bijective),
    Nat.card_prod,card_reorderings_fix_two,card_signs]

end ConwayStabilizer
