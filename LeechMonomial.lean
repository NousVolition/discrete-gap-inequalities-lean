import LeechSymmetry

/-!
# Golay sign changes and coordinate permutations

The existing integrality theorem supplies the sum congruence for Golay sign
changes. The proofs apply to every lattice vector. No group order for the Golay
coordinate permutations or the full Leech symmetry group is asserted here.
-/

namespace LeechSymmetry

open LeechLattice LeechMinimal LeechBasis LeechCodeCounts

def twiceWord (w : Fin 24 → Bool) : Vec := fun i => if w i then 2 else 0

theorem twiceWord_mem {w : Fin 24 → Bool} (hw : IsGolayWord w) :
    twiceWord w ∈ leechLattice := by
  rw [mem_leechLattice, inLeech_iff]
  left
  refine ⟨?_, ?_, ?_⟩
  · intro i; cases h : w i <;> simp [twiceWord, h]
  · have hc := golay_weight_mod_four hw
    have hs : (∑ i, twiceWord w i) =
        2 * ((Finset.univ.filter (fun i => w i = true)).card : ℤ) := by
      simp [twiceWord, Finset.sum_ite, Finset.sum_const, mul_comm]
    rw [hs]
    omega
  · have hr : residueSet (twiceWord w) 2 = w := by
      funext i; cases h : w i <;> simp [residueSet, twiceWord, h]
    rwa [hr]

def signFlip (w : Fin 24 → Bool) (x : Vec) : Vec := fun i => if w i then -x i else x i

theorem signFlip_involutive (w : Fin 24 → Bool) : Function.Involutive (signFlip w) := by
  intro x; funext i; cases h : w i <;> simp [signFlip, h]

theorem signFlip_norm (w : Fin 24 → Bool) (x : Vec) : normSq (signFlip w x) = normSq x := by
  apply Finset.sum_congr rfl
  intro i _; cases h : w i <;> simp [signFlip, h]

theorem signFlip_add (w : Fin 24 → Bool) (x y : Vec) :
    signFlip w (x + y) = signFlip w x + signFlip w y := by
  funext i; cases h : w i <;> simp [signFlip, h, add_comm]

/-- Integrality of the existing lattice makes each codeword's selected sum divisible by four. -/
theorem selected_sum_dvd_four {w : Fin 24 → Bool} (hw : IsGolayWord w)
    {x : Vec} (hx : InLeech x) : 4 ∣ ∑ i, if w i then x i else 0 := by
  obtain ⟨t, ht⟩ := leech_inner_dvd_eight x (twiceWord w) hx (twiceWord_mem hw)
  have hd : (∑ i, x i * twiceWord w i) = 2 * (∑ i, if w i then x i else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; cases h : w i <;> simp [twiceWord, h, mul_comm]
  rw [hd] at ht
  exact ⟨t, by omega⟩

theorem signFlip_sum_mod_eight {w : Fin 24 → Bool} (hw : IsGolayWord w)
    {x : Vec} (hx : InLeech x) : (∑ i, signFlip w x i) % 8 = (∑ i, x i) % 8 := by
  obtain ⟨t, ht⟩ := selected_sum_dvd_four hw hx
  have hs : (∑ i, signFlip w x i) = (∑ i, x i) - 2 * (∑ i, if w i then x i else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _; cases h : w i <;> simp [signFlip, h] <;> ring
  rw [hs, ht]
  omega

/-- Every Golay sign change preserves lattice membership, for vectors of any length. -/
theorem signFlip_mem {w : Fin 24 → Bool} (hw : IsGolayWord w)
    {x : Vec} (hx : InLeech x) : InLeech (signFlip w x) := by
  have hs := signFlip_sum_mod_eight hw hx
  rcases (inLeech_iff x).1 hx with he | ho
  · apply (inLeech_iff _).2; left
    refine ⟨?_, hs.trans he.2.1, ?_⟩
    · intro i; have hp := he.1 i
      cases h : w i <;> simp only [signFlip, h, Bool.false_eq_true, ↓reduceIte] <;> omega
    · have hr : residueSet (signFlip w x) 2 = residueSet x 2 := by
        funext i
        apply Bool.eq_iff_iff.2
        cases h : w i <;> simp [residueSet, signFlip, h] <;> omega
      rw [hr]; exact he.2.2
  · apply (inLeech_iff _).2; right
    refine ⟨?_, hs.trans ho.2.1, ?_⟩
    · intro i; have hp := ho.1 i
      cases h : w i <;> simp only [signFlip, h, Bool.false_eq_true, ↓reduceIte] <;> omega
    · have hr : residueSet (signFlip w x) 3 = fun i => residueSet x 3 i ^^ w i := by
        funext i
        apply Bool.eq_iff_iff.2
        have hp := ho.1 i
        cases h : w i <;> simp [residueSet, signFlip, h] <;> omega
      rw [hr]; exact isGolayWord_xor ho.2.2 hw

def signAut (w : Codeword) : Aut :=
  ⟨{ toFun := fun x => ⟨signFlip w.val x.val, signFlip_mem w.property x.property⟩
     invFun := fun x => ⟨signFlip w.val x.val, signFlip_mem w.property x.property⟩
     left_inv := fun x => Subtype.ext (signFlip_involutive w.val x.val)
     right_inv := fun x => Subtype.ext (signFlip_involutive w.val x.val) },
    (fun x y => Subtype.ext (signFlip_add w.val x.val y.val)),
    fun x => signFlip_norm w.val x.val⟩

theorem signAut_injective : Function.Injective signAut := by
  intro w v h
  apply Subtype.ext
  funext i
  have hi := congrArg (fun g : Aut => (g (latticeAxis i)).val i) h
  change signFlip w.val (axis i) i = signFlip v.val (axis i) i at hi
  cases hw : w.val i <;> cases hv : v.val i <;> simp_all [signFlip, axis]

theorem signAut_sq (w : Codeword) : signAut w * signAut w = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact Subtype.ext (signFlip_involutive w.val x.val)

theorem signAut_xor (w v : Codeword) :
    signAut ⟨fun i => w.val i ^^ v.val i, isGolayWord_xor w.property v.property⟩ =
      signAut w * signAut v := by
  apply Subtype.ext
  ext x i
  change signFlip (fun j => w.val j ^^ v.val j) x.val i = signFlip w.val (signFlip v.val x.val) i
  cases hw : w.val i <;> cases hv : v.val i <;> simp [signFlip, hw, hv]

def signSubgroup : Subgroup Aut where
  carrier := Set.range signAut
  one_mem' := ⟨⟨fun _ => false, isGolayWord_false⟩, by
    apply Subtype.ext; ext x i; rfl⟩
  mul_mem' := by
    rintro _ _ ⟨w, rfl⟩ ⟨v, rfl⟩
    exact ⟨⟨fun i => w.val i ^^ v.val i, isGolayWord_xor w.property v.property⟩, signAut_xor w v⟩
  inv_mem' := by
    rintro _ ⟨w, rfl⟩
    exact ⟨w, (eq_inv_iff_mul_eq_one).2 (signAut_sq w)⟩

noncomputable def signEquiv : Codeword ≃ signSubgroup :=
  Equiv.ofBijective (fun w => ⟨signAut w, w, rfl⟩)
    ⟨fun _ _ h => signAut_injective (congrArg Subtype.val h),
      fun ⟨_, w, hw⟩ => ⟨w, Subtype.ext hw⟩⟩

noncomputable instance : Fintype signSubgroup := Fintype.ofEquiv Codeword signEquiv

/-- There are 4,096 different Golay sign changes, and they form a subgroup. -/
theorem card_signSubgroup : Fintype.card signSubgroup = 4096 := by
  rw [← Fintype.card_congr signEquiv, card_codeword]

/-- Coordinate permutations preserving the already defined Golay code. -/
def IsCodePermutation (p : Equiv.Perm (Fin 24)) : Prop :=
  ∀ w : Fin 24 → Bool, IsGolayWord w ↔ IsGolayWord (fun i => w (p i))

def permute (p : Equiv.Perm (Fin 24)) (x : Vec) : Vec := fun i => x (p i)

theorem permute_sum (p : Equiv.Perm (Fin 24)) (x : Vec) :
    (∑ i, permute p x i) = ∑ i, x i := Equiv.sum_comp p x

theorem permute_norm (p : Equiv.Perm (Fin 24)) (x : Vec) :
    normSq (permute p x) = normSq x := Equiv.sum_comp p (fun i => x i ^ 2)

theorem permute_mem (p : Equiv.Perm (Fin 24)) (hp : IsCodePermutation p)
    {x : Vec} (hx : InLeech x) : InLeech (permute p x) := by
  obtain ⟨m, hm, hpar, hsum, hcode⟩ := hx
  refine ⟨m, hm, fun i => hpar (p i), ?_, fun k => (hp _).1 (hcode k)⟩
  rwa [permute_sum]

theorem codePermutation_symm (p : Equiv.Perm (Fin 24)) (hp : IsCodePermutation p) :
    IsCodePermutation p.symm := by
  intro w
  have h := hp (fun i => w (p.symm i))
  simpa using h.symm

def permutationAut (p : Equiv.Perm (Fin 24)) (hp : IsCodePermutation p) : Aut :=
  ⟨{ toFun := fun x => ⟨permute p x.val, permute_mem p hp x.property⟩
     invFun := fun x => ⟨permute p.symm x.val, permute_mem p.symm (codePermutation_symm p hp) x.property⟩
     left_inv := fun x => by apply Subtype.ext; funext i; simp [permute]
     right_inv := fun x => by apply Subtype.ext; funext i; simp [permute] },
    (fun _ _ => rfl), fun x => permute_norm p x.val⟩

end LeechSymmetry
