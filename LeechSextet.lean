import LeechFrameStabilizer

/-! # A symmetry moving the standard Leech frame

The six tetrads partition the coordinates. On each tetrad subtract half the
sum of its four coordinates from each entry, then negate the second tetrad.
The proof checks the doubled matrix on the existing lattice basis.
-/

namespace LeechSextet

open LeechSymmetry LeechLattice LeechMinimal LeechBasis GolayMatrixDistance Matrix

abbrev Pt := Fin 24

def tetrad (i : Pt) : Nat :=
  (#[0,0,0,0,2,1,1,3,1,4,3,5,3,2,5,2,4,4,1,5,2,3,4,5] : Array Nat).getD i.val 0

def doubled : Matrix Pt Pt ℤ := fun i j =>
  (if tetrad i = 1 then -1 else 1) *
  (if i = j then 1 else if tetrad i = tetrad j then -1 else 0)

theorem symmetric : doubled.transpose = doubled := by
  ext i j
  by_cases ht : tetrad i = tetrad j
  · simp [Matrix.transpose_apply, doubled, ht, eq_comm]
  · have hn : i ≠ j := fun he => ht (congrArg tetrad he)
    simp [Matrix.transpose_apply, doubled, ht, Ne.symm ht, hn, Ne.symm hn]

theorem square : doubled * doubled = (4 : ℤ) • (1 : Matrix Pt Pt ℤ) := by
  ext i j; revert i j; decide +kernel

def numer (x : Vec) : Vec := doubled *ᵥ x
def move (x : Vec) : Vec := fun i => numer x i / 2

theorem numer_twice (x : Vec) : numer (numer x) = (4 : ℤ) • x := by
  rw [numer, numer, mulVec_mulVec, square, smul_mulVec, one_mulVec]

theorem numer_norm (x : Vec) : normSq (numer x) = 4 * normSq x := by
  have h := dotProduct_transpose_mulVec doubled x (numer x)
  rw [symmetric] at h
  change x ⬝ᵥ (numer (numer x)) = (numer x) ⬝ᵥ (numer x) at h
  rw [numer_twice] at h
  simpa [dotProduct, normSq, pow_two, Finset.mul_sum, mul_left_comm] using h.symm

def lowMessage (w : Pt → Bool) : Nat :=
  ∑ i : Fin 12, if w (Fin.castLE (by decide) i) then 2 ^ i.val else 0

def checkMember (x : Vec) : Prop :=
  let m := x 0 % 2
  let v := residueSet x (2+m)
  (∀ i, x i % 2 = m) ∧ (∑ i, x i) % 8 = 4*m ∧
    lowMessage v < 4096 ∧ (∀ i, word (encodeNat (lowMessage v)) i = v i)

instance (x : Vec) : Decidable (checkMember x) := by unfold checkMember; infer_instance

theorem mem_of_check {x : Vec} (h : checkMember x) : x ∈ leechLattice := by
  unfold checkMember at h
  dsimp only at h
  apply (inLeech_iff x).2
  rcases Int.emod_two_eq_zero_or_one (x 0) with hz | hz
  · left; rw [hz] at h
    exact ⟨h.1, by simpa using h.2.1, ⟨_, h.2.2.1, funext h.2.2.2⟩⟩
  · right; rw [hz] at h
    exact ⟨h.1, by simpa using h.2.1, ⟨_, h.2.2.1, funext h.2.2.2⟩⟩

theorem basis_image : ∀ i : Pt, checkMember (move (leechBasis i)) ∧
    ∀ j, numer (leechBasis i) j = 2 * move (leechBasis i) j := by decide +kernel

/-- Dividing the matrix product by two produces a lattice vector for every lattice input. -/
theorem integral_image {x : Vec} (hx : x ∈ leechLattice) :
    ∃ y ∈ leechLattice, numer x = (2 : ℤ) • y := by
  rw [← closure_leechBasis] at hx
  induction hx using AddSubgroup.closure_induction with
  | mem b hb =>
    obtain ⟨i, rfl⟩ := hb
    exact ⟨move (leechBasis i), mem_of_check (basis_image i).1, funext (basis_image i).2⟩
  | zero => exact ⟨0, zero_mem _, by simp [numer]⟩
  | add a b _ _ ha hb =>
    obtain ⟨u, hu, hru⟩ := ha
    obtain ⟨v, hv, hrv⟩ := hb
    exact ⟨u+v, add_mem hu hv, by rw [numer, mulVec_add]; exact (congrArg₂ (· + ·) hru hrv).trans (smul_add ..).symm⟩
  | neg a _ ha =>
    obtain ⟨u, hu, he⟩ := ha
    exact ⟨-u, neg_mem hu, by rw [numer, mulVec_neg, smul_neg]; exact congrArg Neg.neg he⟩

theorem move_mem_double {x : Vec} (hx : x ∈ leechLattice) :
    move x ∈ leechLattice ∧ numer x = (2 : ℤ) • move x := by
  obtain ⟨y, hy, he⟩ := integral_image hx
  have hm : move x = y := by funext i; simp [move, he]
  rwa [hm, and_iff_right hy]

theorem move_add (x y : Lattice) : move (x.val + y.val) = move x.val + move y.val := by
  funext i
  have h : numer (x.val + y.val) = numer x.val + numer y.val := mulVec_add ..
  have a := congrFun (move_mem_double x.property).2 i
  have b := congrFun (move_mem_double y.property).2 i
  have c := congrFun (move_mem_double (x+y).property).2 i
  change numer (x.val + y.val) i = 2 * move (x.val + y.val) i at c
  change numer x.val i = 2 * move x.val i at a
  change numer y.val i = 2 * move y.val i at b
  rw [h] at c
  simp only [Pi.add_apply] at c ⊢
  omega

theorem move_norm (x : Lattice) : normSq (move x.val) = normSq x.val := by
  have h := numer_norm x.val
  have hn : numer x.val = 2 • move x.val := (move_mem_double x.property).2
  rw [hn, normSq_two_smul] at h
  omega

theorem move_square (x : Lattice) : move (move x.val) = x.val := by
  have h := numer_twice x.val
  have h1 := (move_mem_double x.property).2
  have h2 := (move_mem_double (move_mem_double x.property).1).2
  calc
    move (move x.val) = x.val := by
      conv at h => lhs; arg 1; rw [h1]
      change doubled *ᵥ ((2 : ℤ) • move x.val) = _ at h
      rw [mulVec_smul] at h
      change (2 : ℤ) • numer (move x.val) = _ at h
      rw [h2] at h
      funext i
      have hi := congrFun h i
      change 2 * (2 * move (move x.val) i) = 4 * x.val i at hi
      omega

def symmetry : Aut :=
  ⟨{ toFun := fun x => ⟨move x.val, (move_mem_double x.property).1⟩
     invFun := fun x => ⟨move x.val, (move_mem_double x.property).1⟩
     left_inv := fun x => Subtype.ext (move_square x)
     right_inv := fun x => Subtype.ext (move_square x) },
    fun x y => Subtype.ext (move_add x y), move_norm⟩

theorem moves_frame : ¬ PreservesFrame symmetry := by
  intro hf
  obtain ⟨j, hj | hj⟩ := hf 0 <;>
    have h := congrFun hj 0 <;>
    change move (axis 0) 0 = _ at h <;>
    have he : move (axis 0) 0 = 4 := by decide +kernel
  all_goals rw [he] at h; simp [axis] at h; split_ifs at h <;> omega

end LeechSextet
