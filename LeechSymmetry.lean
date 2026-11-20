import LeechBasis
import LeechKissing

/-!
# Symmetries of the defined Leech lattice

The coordinates retain the project's √8 scale. The group below consists of
additive bijections of the whole lattice that preserve squared length.
It is not restricted to integer matrices acting on the ambient integer grid.

This file supplies the shortest-vector and coordinate-frame reductions for a
classification of the group. It does not assert a generating set or group order.
-/

namespace LeechSymmetry

open LeechLattice LeechMinimal LeechBasis

abbrev Lattice := ↥leechLattice

def dot (x y : Vec) : ℤ := ∑ i, x i * y i

theorem normSq_add (x y : Vec) :
    normSq (x + y) = normSq x + normSq y + 2 * dot x y := by
  simp only [normSq, dot, Pi.add_apply]
  calc
    ∑ i, (x i + y i) ^ 2 = ∑ i, (x i ^ 2 + y i ^ 2 + 2 * (x i * y i)) := by
      apply Finset.sum_congr rfl; intro i _; ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]

theorem normSq_neg (x : Vec) : normSq (-x) = normSq x := by
  simp [normSq]

theorem normSq_sub (x y : Vec) :
    normSq (x - y) = normSq x + normSq y - 2 * dot x y := by
  rw [sub_eq_add_neg, normSq_add, normSq_neg]
  simp [dot, mul_neg, sub_eq_add_neg]

theorem normSq_two_smul (x : Vec) : normSq (2 • x) = 4 * normSq x := by
  simp only [normSq, Pi.smul_apply, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _; ring

/-- The full group of additive, length-preserving bijections of this lattice. -/
def autGroup : Subgroup (Equiv.Perm Lattice) where
  carrier := {g | (∀ x y, g (x + y) = g x + g y) ∧
    ∀ x, normSq (g x).val = normSq x.val}
  one_mem' := ⟨by intros; rfl, by intros; rfl⟩
  mul_mem' := by
    rintro g h ⟨ga, gn⟩ ⟨ha, hn⟩
    exact ⟨fun x y => by simp only [Equiv.Perm.mul_apply, ha, ga],
      fun x => (gn (h x)).trans (hn x)⟩
  inv_mem' := by
    rintro g ⟨ga, gn⟩
    constructor
    · intro x y
      apply g.injective
      change g (g.symm (x + y)) = g (g.symm x + g.symm y)
      simp only [Equiv.apply_symm_apply, ga]
    · intro x
      have h := gn (g.symm x)
      simpa using h.symm

abbrev Aut := ↥autGroup

instance : CoeFun Aut (fun _ => Lattice → Lattice) := ⟨fun g => g.val⟩

def toAddEquiv (g : Aut) : Lattice ≃+ Lattice :=
  { g.val with map_add' := g.property.1 }

theorem map_norm (g : Aut) (x : Lattice) : normSq (g x).val = normSq x.val :=
  g.property.2 x

theorem map_dot (g : Aut) (x y : Lattice) : dot (g x).val (g y).val = dot x.val y.val := by
  have h := map_norm g (x + y)
  rw [g.property.1] at h
  change normSq ((g x).val + (g y).val) = normSq (x.val + y.val) at h
  rw [normSq_add, normSq_add, map_norm, map_norm] at h
  omega

theorem basis_norm32 : ∀ i : Fin 24, i ≠ 23 → normSq (leechBasis i) = 32 := by
  decide +kernel

def shortestSet : Set Vec := {x | InLeech x ∧ normSq x = 32}

/-- The 196,560 shortest vectors generate the whole lattice over the integers. -/
theorem shortest_span : AddSubgroup.closure shortestSet = leechLattice := by
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).2
    intro x hx
    exact hx.1
  · rw [← closure_leechBasis]
    apply (AddSubgroup.closure_le _).2
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = 23
    · subst i
      let p : Vec := fun j => if j = 0 ∨ j = 23 then 4 else 0
      let q : Vec := fun j => if j = 0 then 4 else if j = 23 then -4 else 0
      have hp : p ∈ shortestSet := four_mem_norm (by unfold FourShape; decide +kernel : FourShape p)
      have hq : q ∈ shortestSet := four_mem_norm (by unfold FourShape; decide +kernel : FourShape q)
      have heq : leechBasis 23 = p - q := by decide +kernel
      rw [heq]
      exact sub_mem (AddSubgroup.subset_closure hp) (AddSubgroup.subset_closure hq)
    · exact AddSubgroup.subset_closure ⟨leechBasis_mem i, basis_norm32 i hi⟩

/-- An axis vector in the integer coordinates, with squared length 64. -/
def axis (i : Fin 24) : Vec := fun j => if j = i then 8 else 0

theorem axis_mem (i : Fin 24) : axis i ∈ leechLattice := by
  rw [← closure_leechBasis]
  apply mem_span_of_four
  · intro j; simp [axis]; split_ifs <;> norm_num
  · simp [axis]

theorem axis_norm (i : Fin 24) : normSq (axis i) = 64 := by
  simp [normSq, axis, ite_pow]

theorem dot_axis (x : Vec) (i : Fin 24) : dot x (axis i) = 8 * x i := by
  simp [dot, axis, mul_ite, mul_comm]

/-- Congruence modulo twice the lattice, with the half-difference retained as a witness. -/
def SameModTwo (x y : Vec) : Prop := ∃ z : Lattice, x - y = 2 • z.val

theorem axes_sameModTwo (i j : Fin 24) : SameModTwo (axis i) (axis j) := by
  let z : Vec := fun k => (if k = i then 4 else 0) - (if k = j then 4 else 0)
  have hz : z ∈ leechLattice := by
    rw [← closure_leechBasis]
    apply mem_span_of_four
    · intro k; dsimp [z]; split_ifs <;> norm_num
    · simp [z, Finset.sum_sub_distrib]
  refine ⟨⟨z, hz⟩, ?_⟩
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, axis, z]
  split_ifs <;> norm_num

/-- Distinct, nonopposite norm-64 vectors in one class modulo 2Λ are orthogonal. -/
theorem norm64_sameModTwo_orthogonal {x y : Vec}
    (hy : InLeech y) (hx64 : normSq x = 64) (hy64 : normSq y = 64)
    (hxy : SameModTwo x y) (hne : x ≠ y) (hneg : x ≠ -y) : dot x y = 0 := by
  obtain ⟨z, hz⟩ := hxy
  have hz0 : z.val ≠ 0 := by
    intro h
    rw [h, smul_zero, sub_eq_zero] at hz
    exact hne hz
  have hz32 : 32 ≤ normSq z.val := leech_norm_ge_32 _ z.property hz0
  have hplus : x + y = 2 • (z.val + y) := by
    have : x = 2 • z.val + y := (sub_eq_iff_eq_add).1 hz
    rw [this, two_smul, two_smul]
    abel
  have hp0 : z.val + y ≠ 0 := by
    intro h
    rw [h, smul_zero, add_eq_zero_iff_eq_neg] at hplus
    exact hneg hplus
  have hp32 : 32 ≤ normSq (z.val + y) :=
    leech_norm_ge_32 _ (add_mem z.property hy) hp0
  have hm := congrArg normSq hz
  have hp := congrArg normSq hplus
  rw [normSq_sub, normSq_two_smul, hx64, hy64] at hm
  rw [normSq_add, normSq_two_smul, hx64, hy64] at hp
  omega

theorem sameModTwo_trans {x y z : Vec} (hxy : SameModTwo x y)
    (hyz : SameModTwo y z) : SameModTwo x z := by
  obtain ⟨u, hu⟩ := hxy
  obtain ⟨v, hv⟩ := hyz
  refine ⟨u + v, ?_⟩
  change x - z = 2 • (u.val + v.val)
  rw [smul_add, ← hu, ← hv]
  abel

/-- The norm-64 vectors in the standard class are the 24 axes and their negatives. -/
theorem standard_class {x : Vec} (hx : normSq x = 64)
    (hc : SameModTwo x (axis 0)) : ∃ i, x = axis i ∨ x = -(axis i) := by
  by_contra h
  push Not at h
  have hz : x = 0 := by
    funext i
    have hd := norm64_sameModTwo_orthogonal (axis_mem i) hx (axis_norm i)
      (sameModTwo_trans hc (axes_sameModTwo 0 i)) (h i).1 (h i).2
    rw [dot_axis] at hd
    change x i = 0
    omega
  simp [hz, normSq] at hx

def latticeAxis (i : Fin 24) : Lattice := ⟨axis i, axis_mem i⟩

theorem map_sameModTwo (g : Aut) {x y : Lattice}
    (h : SameModTwo x.val y.val) : SameModTwo (g x).val (g y).val := by
  obtain ⟨z, hz⟩ := h
  have hs : x - y = 2 • z := Subtype.ext hz
  have hg := congrArg (toAddEquiv g) hs
  rw [map_sub, map_nsmul] at hg
  exact ⟨g z, congrArg Subtype.val hg⟩

/-- Fixing one axis forces a symmetry to preserve the entire standard frame. -/
theorem fixes_axis_preserves_frame (g : Aut) (hg : g (latticeAxis 0) = latticeAxis 0)
    (i : Fin 24) : ∃ j, (g (latticeAxis i)).val = axis j ∨
      (g (latticeAxis i)).val = -(axis j) := by
  apply standard_class
  · rw [map_norm]
    exact axis_norm i
  · have h := map_sameModTwo g (x := latticeAxis i) (y := latticeAxis 0)
      (axes_sameModTwo i 0)
    rwa [hg] at h

def onShortest (g : Aut) : Equiv.Perm MinimalVectors where
  toFun x := ⟨(g ⟨x.val, x.property.1⟩).val,
    (g ⟨x.val, x.property.1⟩).property, (map_norm g _).trans x.property.2⟩
  invFun x := ⟨(g⁻¹ ⟨x.val, x.property.1⟩).val,
    (g⁻¹ ⟨x.val, x.property.1⟩).property, (map_norm g⁻¹ _).trans x.property.2⟩
  left_inv x := by
    apply Subtype.ext
    change (g.val.symm (g.val ⟨x.val, x.property.1⟩)).val = x.val
    exact congrArg (fun y : Lattice => y.val) (g.val.symm_apply_apply ⟨x.val, x.property.1⟩)
  right_inv x := by
    apply Subtype.ext
    change (g.val (g.val.symm ⟨x.val, x.property.1⟩)).val = x.val
    exact congrArg (fun y : Lattice => y.val) (g.val.apply_symm_apply ⟨x.val, x.property.1⟩)

/-- The action on the proved 196,560-element shortest shell. -/
def shortestAction : Aut →* Equiv.Perm MinimalVectors where
  toFun := onShortest
  map_one' := by ext x i; rfl
  map_mul' _ _ := by ext x i; rfl

/-- Two lattice symmetries agreeing on every shortest vector agree everywhere. -/
theorem shortestAction_injective : Function.Injective shortestAction := by
  intro g h heq
  have hshort : ∀ x : Vec, ∀ hx : x ∈ shortestSet,
      g ⟨x, hx.1⟩ = h ⟨x, hx.1⟩ := by
    intro x hx
    have := congrArg (fun e : Equiv.Perm MinimalVectors => (e ⟨x, hx⟩).val) heq
    exact Subtype.ext this
  have hall : ∀ x : Vec, ∀ hx : x ∈ leechLattice, g ⟨x, hx⟩ = h ⟨x, hx⟩ := by
    intro x hx
    have hs : x ∈ AddSubgroup.closure shortestSet := by rwa [shortest_span]
    have hind : ∀ y : Vec, y ∈ AddSubgroup.closure shortestSet →
        ∀ hy : y ∈ leechLattice, g ⟨y, hy⟩ = h ⟨y, hy⟩ := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy => intro _; exact hshort y hy
      | zero => intro _; exact (toAddEquiv g).map_zero.trans (toAddEquiv h).map_zero.symm
      | add a b ha hb iha ihb =>
        intro _
        have haL : a ∈ leechLattice := by rwa [shortest_span] at ha
        have hbL : b ∈ leechLattice := by rwa [shortest_span] at hb
        change g (⟨a, haL⟩ + ⟨b, hbL⟩) = h (⟨a, haL⟩ + ⟨b, hbL⟩)
        rw [g.property.1, h.property.1, iha haL, ihb hbL]
      | neg a ha iha =>
        intro _
        have haL : a ∈ leechLattice := by rwa [shortest_span] at ha
        change toAddEquiv g (-⟨a, haL⟩) = toAddEquiv h (-⟨a, haL⟩)
        rw [map_neg, map_neg]
        exact congrArg Neg.neg (iha haL)
    exact hind x hs hx
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact hall x.val x.property

/-- Finiteness follows from the faithful action, without an asserted Conway-group order. -/
instance : Finite Aut := Finite.of_injective shortestAction shortestAction_injective

theorem aut_finite : Finite Aut := inferInstance

theorem dot_add_left (x y z : Vec) : dot (x + y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

/-- The definition includes every distance-preserving lattice bijection fixing zero. -/
theorem mem_autGroup_iff (f : Equiv.Perm Lattice) : f ∈ autGroup ↔
    f 0 = 0 ∧ ∀ x y, normSq ((f x).val - (f y).val) = normSq (x.val - y.val) := by
  constructor
  · intro hf
    let g : Aut := ⟨f, hf⟩
    refine ⟨(toAddEquiv g).map_zero, ?_⟩
    intro x y
    have h := map_norm g (x - y)
    have hs := (toAddEquiv g).map_sub x y
    change g (x - y) = g x - g y at hs
    rw [hs] at h
    exact h
  · rintro ⟨h0, hd⟩
    have hn : ∀ x, normSq (f x).val = normSq x.val := by
      intro x
      simpa [h0] using hd x 0
    have hi : ∀ x y, dot (f x).val (f y).val = dot x.val y.val := by
      intro x y
      have h := hd x y
      rw [normSq_sub, normSq_sub, hn, hn] at h
      omega
    refine ⟨?_, hn⟩
    intro x y
    apply Subtype.ext
    funext i
    let z := f.symm (latticeAxis i)
    have hz : (f z).val = axis i := congrArg Subtype.val (f.apply_symm_apply _)
    have h := hi (x + y) z
    change dot (f (x + y)).val (f z).val = dot (x.val + y.val) z.val at h
    rw [dot_add_left, ← hi x z, ← hi y z, hz, dot_axis, dot_axis, dot_axis] at h
    change (f (x + y)).val i = (f x).val i + (f y).val i
    omega

/-- Negating every coordinate is a lattice symmetry. -/
def centralNegation : Aut :=
  ⟨(AddEquiv.neg Lattice).toEquiv,
    (AddEquiv.neg Lattice).map_add, fun x => normSq_neg x.val⟩

theorem centralNegation_sq : centralNegation * centralNegation = 1 := by
  apply Subtype.ext
  ext x i
  change -(-x.val i) = x.val i
  exact neg_neg _

theorem centralNegation_commutes (g : Aut) : centralNegation * g = g * centralNegation := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact ((toAddEquiv g).map_neg x).symm

theorem centralNegation_ne_one : centralNegation ≠ 1 := by
  intro h
  have hi := congrArg (fun g : Aut => (g (latticeAxis 0)).val 0) h
  change -(axis 0 0) = axis 0 0 at hi
  norm_num [axis] at hi

theorem axis_neg_sameModTwo (i j : Fin 24) : SameModTwo (-(axis i)) (axis j) := by
  have h : SameModTwo (-(axis i)) (axis i) := by
    refine ⟨-latticeAxis i, ?_⟩
    change -(axis i) - axis i = 2 • (-(axis i))
    rw [two_smul]; abel
  exact sameModTwo_trans h (axes_sameModTwo i j)

theorem standard_class_iff (x : Vec) :
    normSq x = 64 ∧ SameModTwo x (axis 0) ↔ ∃ i, x = axis i ∨ x = -(axis i) := by
  constructor
  · rintro ⟨hn, hc⟩; exact standard_class hn hc
  · rintro ⟨i, rfl | rfl⟩
    · exact ⟨axis_norm i, axes_sameModTwo i 0⟩
    · exact ⟨(normSq_neg _).trans (axis_norm i), axis_neg_sameModTwo i 0⟩

abbrev StandardFrame := {x : Vec // normSq x = 64 ∧ SameModTwo x (axis 0)}

def frameVector (p : Fin 24 × Bool) : StandardFrame :=
  if p.2 then ⟨-(axis p.1), (normSq_neg _).trans (axis_norm _), axis_neg_sameModTwo _ 0⟩
  else ⟨axis p.1, axis_norm _, axes_sameModTwo _ 0⟩

theorem frameVector_injective : Function.Injective frameVector := by
  intro p q h
  have hv := congrArg Subtype.val h
  have hc := congrFun hv p.1
  rcases p with ⟨i, b⟩
  rcases q with ⟨j, c⟩
  cases b <;> cases c <;> simp only [frameVector, Bool.false_eq_true, ↓reduceIte] at hc hv
  all_goals by_cases hij : i = j
  all_goals simp [axis, hij] at hc
  all_goals subst j; rfl

theorem frameVector_surjective : Function.Surjective frameVector := by
  rintro ⟨x, hx⟩
  rcases (standard_class_iff x).1 hx with ⟨i, rfl | rfl⟩
  · exact ⟨(i, false), rfl⟩
  · exact ⟨(i, true), rfl⟩

noncomputable def frameEquiv : Fin 24 × Bool ≃ StandardFrame :=
  Equiv.ofBijective frameVector ⟨frameVector_injective, frameVector_surjective⟩

noncomputable instance : Fintype StandardFrame := Fintype.ofEquiv _ frameEquiv

theorem card_standardFrame : Fintype.card StandardFrame = 48 := by
  rw [← Fintype.card_congr frameEquiv]
  decide

end LeechSymmetry
