import MathieuGroup
import LeechSextet

/-! # Four-coordinate moves in the Leech lattice -/

namespace ConwayMoves

open GolayMathieu LeechSextet LeechSymmetry LeechLattice LeechMinimal LeechCodeCounts
open GolayMatrixDistance Matrix

def first (i : Fin 4) : Point := Fin.castLE (by decide) i

theorem four_transitive (f : Fin 4 ↪ Point) :
    ∃ p : Perm, IsCodePermutation p ∧ ∀ i, p (first i) = f i := by
  have build : ∀ n ≤ 4, ∃ p : Perm, IsCodePermutation p ∧
      ∀ i : Fin 4, i.val < n → p (base i.val) = f i := by
    intro n; induction n with
    | zero => exact fun _ => ⟨1, (level_zero_iff _).1 (level 0).one_mem, fun i hi => by omega⟩
    | succ n ih =>
      intro hn
      obtain ⟨p, hp, hf⟩ := ih (by omega)
      let a : Fin 4 := ⟨n, by omega⟩
      let k : Fin 7 := ⟨n, by omega⟩
      let y := p.symm (f a)
      have hy : allowed k y = true := by
        have h5 : k.val < 5 := by dsimp [k]; omega
        simp [allowed, h5, List.any_eq_false]
        intro j hj he
        have hpi := hf ⟨j, by omega⟩ hj
        have heq : p (base j) = f a := by rw [he]; exact p.apply_symm_apply _
        have hab := f.injective (hpi.symm.trans heq)
        exact (Nat.ne_of_lt hj) (congrArg Fin.val hab)
      let s := sectionAt k ⟨y,hy⟩
      refine ⟨p * s.val, ((level 0).mul_mem ((level_zero_iff _).2 hp)
        ((level_zero_iff _).2 s.property.1)).1, ?_⟩
      intro i hi
      by_cases h : i.val = n
      · have he : i = a := Fin.ext h
        subst i
        change p (s.val (base k.val)) = f a
        rw [show s.val (base k.val) = y from sectionAt_hits k ⟨y, hy⟩]
        exact p.apply_symm_apply _
      · have hj : i.val < n := by omega
        change p (s.val (base i.val)) = f i
        rw [s.property.2 _ hj, hf i hj]
  obtain ⟨p, hp, hf⟩ := build 4 (by decide)
  have he : ∀ i : Fin 4, first i = base i.val := by decide +kernel
  exact ⟨p, hp, fun i => (he i ▸ hf i i.isLt)⟩

theorem four_signs (b : Fin 4 → Bool) : ∃ w : Codeword, ∀ i, w.val (first i) = b i := by
  have bits : ∀ a b c d : Bool, ∃ m : Fin 16, word (encodeNat m.val) 0 = a ∧
      word (encodeNat m.val) 1 = b ∧ word (encodeNat m.val) 2 = c ∧ word (encodeNat m.val) 3 = d := by
    decide +kernel
  obtain ⟨m, ha, hb, hc, hd⟩ := bits (b 0) (b 1) (b 2) (b 3)
  refine ⟨⟨word (encodeNat m.val), m.val, by omega, rfl⟩, ?_⟩
  intro i; fin_cases i
  · exact ha
  · exact hb
  · exact hc
  · exact hd

def moves : Set Aut := Set.range signAut ∪
    {g | ∃ p : Perm, ∃ hp : IsCodePermutation p, permutationAut p hp = g} ∪ {symmetry}
def G : Subgroup Aut := Subgroup.closure moves

theorem sign_mem (w : Codeword) : signAut w ∈ G :=
  Subgroup.subset_closure (Or.inl (Or.inl ⟨w, rfl⟩) : signAut w ∈ moves)
theorem perm_mem (p : Perm) (hp : IsCodePermutation p) : permutationAut p hp ∈ G :=
  Subgroup.subset_closure (Or.inl (Or.inr ⟨p,hp,rfl⟩) : permutationAut p hp ∈ moves)
theorem sextet_mem : symmetry ∈ G := Subgroup.subset_closure (Or.inr rfl : symmetry ∈ moves)

def Reaches (x y : Lattice) : Prop := ∃ g : Aut, g ∈ G ∧ g x = y

theorem reaches_refl (x : Lattice) : Reaches x x := ⟨1, G.one_mem, rfl⟩
theorem reaches_trans {x y z : Lattice} (h : Reaches x y) (k : Reaches y z) : Reaches x z := by
  obtain ⟨a, ha, rfl⟩ := h; obtain ⟨b, hb, rfl⟩ := k
  exact ⟨b*a,G.mul_mem hb ha,rfl⟩
theorem reaches_symm {x y : Lattice} (h : Reaches x y) : Reaches y x := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a⁻¹,G.inv_mem ha,a.val.symm_apply_apply x⟩
theorem reaches_norm {x y : Lattice} (h : Reaches x y) : normSq y.val = normSq x.val := by
  obtain ⟨a, _, rfl⟩ := h; exact map_norm a x

theorem arrange_four (x : Lattice) (f : Fin 4 ↪ Point) (negative : Fin 4 → Bool) :
    ∃ y, Reaches x y ∧ ∀ i, y.val (first i) =
      if negative i then -|x.val (f i)| else |x.val (f i)| := by
  obtain ⟨p, hp, hf⟩ := four_transitive f
  obtain ⟨w, hw⟩ := four_signs (fun i => decide (x.val (f i) < 0) ^^ negative i)
  let g := signAut w * permutationAut p hp
  refine ⟨g x, ⟨g,G.mul_mem (sign_mem w) (perm_mem p hp),rfl⟩, ?_⟩
  intro i
  change (if w.val (first i) then -x.val (p (first i)) else x.val (p (first i))) = _
  rw [hf, hw]
  by_cases h : x.val (f i) < 0 <;> cases hb : negative i <;>
    simp [h, abs_of_nonneg, abs_of_neg, le_of_not_gt]

theorem first_numer (x : Vec) (i : Fin 4) : numer x (first i) =
    2*x (first i) - ∑ j : Fin 4, x (first j) := by
  have row : ∀ (r : Fin 4) (j : Point), doubled (first r) j =
      (if j = first r then 2 else 0) - ∑ k : Fin 4, (if j = first k then 1 else 0) := by
    decide +kernel
  change (∑ j, doubled (first i) j * x j) = _
  simp only [row, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, ite_mul, zero_mul, one_mul]
  rw [Finset.sum_comm (f := fun (j : Point) (k : Fin 4) => if j = first k then x j else 0)]
  simp

theorem first_norm_move (x : Lattice) (i : Fin 4) :
    2 * (symmetry x).val (first i) = 2*x.val (first i) - ∑ j : Fin 4, x.val (first j) := by
  exact (congrFun (move_mem_double x.property).2 (first i)).symm.trans (first_numer x.val i)

theorem four_sum_bound (x : Lattice) (M : ℤ)
    (hM : ∀ y, Reaches x y → ∀ j, |y.val j| ≤ M) (f : Fin 4 ↪ Point) :
    (∑ i : Fin 4, |x.val (f i)|) ≤ 2*M := by
  obtain ⟨y, hy, he⟩ := arrange_four x f (fun i => decide (i ≠ 0))
  have h := first_norm_move y 0
  have hb := hM (symmetry y) (reaches_trans hy ⟨symmetry,sextet_mem,rfl⟩) (first 0)
  have hle := (le_abs_self _).trans hb
  simp only [Fin.sum_univ_succ, he] at h ⊢
  norm_num at h ⊢
  simp only [show (2 : Fin 4) ≠ 0 by decide, ite_false] at h
  linarith

end ConwayMoves
