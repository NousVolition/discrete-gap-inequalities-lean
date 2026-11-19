import LeechLattice
import GolayLeechBridge

/-! # The three families of shortest Leech vectors

All coordinates and squared lengths use the existing `LeechLattice` definitions,
with coordinates scaled by `√8`. -/

namespace LeechMinimal

open LeechLattice GolayMatrixDistance Finset

abbrev Vec := Fin 24 → ℤ

def normSq (x : Vec) : ℤ := ∑ i, x i ^ 2
def support (x : Vec) : Finset (Fin 24) := univ.filter (fun i => x i ≠ 0)
def negatives (x : Vec) : Finset (Fin 24) := univ.filter (fun i => x i < 0)

def FourShape (x : Vec) : Prop :=
  (∀ i, x i = 0 ∨ x i = 4 ∨ x i = -4) ∧ (support x).card = 2

def OctadShape (x : Vec) : Prop :=
  (∀ i, x i = 0 ∨ x i = 2 ∨ x i = -2) ∧
  IsGolayWord (residueSet x 2) ∧ (support x).card = 8 ∧ (negatives x).card % 2 = 0

def oddVector (w : Fin 24 → Bool) (j : Fin 24) : Vec :=
  fun i => if i = j then (if w i then 3 else -3) else (if w i then -1 else 1)

def OddShape (x : Vec) : Prop :=
  ∃ w : Fin 24 → Bool, IsGolayWord w ∧ ∃ j, x = oddVector w j

theorem sum_of_signed_support {q : ℤ} (x : Vec)
    (hx : ∀ i, x i = 0 ∨ x i = q ∨ x i = -q) (hq : 0 < q) :
    ∑ i, x i = q * (support x).card - 2 * q * (negatives x).card := by
  have hpoint : ∀ i, x i = q * (if x i ≠ 0 then 1 else 0) -
      2 * q * (if x i < 0 then 1 else 0) := by
    intro i
    rcases hx i with h | h | h <;> rw [h] <;>
      simp [hq.ne', hq, not_lt_of_ge hq.le] <;> ring
  rw [sum_congr rfl (fun i _ => hpoint i), sum_sub_distrib, ← mul_sum, ← mul_sum]
  rw [sum_boole, sum_boole]
  rfl

theorem norm_of_signed_support {q : ℤ} (x : Vec)
    (hx : ∀ i, x i = 0 ∨ x i = q ∨ x i = -q) (hq : q ≠ 0) :
    normSq x = q ^ 2 * (support x).card := by
  have hpoint : ∀ i, x i ^ 2 = q ^ 2 * (if x i ≠ 0 then 1 else 0) := by
    intro i
    rcases hx i with h | h | h <;> simp [h, hq]
  rw [normSq, sum_congr rfl (fun i _ => hpoint i), ← mul_sum]
  rw [sum_boole]
  rfl

theorem coordinate_sq_le {x : Vec} (hx : normSq x = 32) (i : Fin 24) : x i ^ 2 ≤ 32 := by
  have := single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg (x i)) (mem_univ i)
  change x i ^ 2 ≤ normSq x at this
  rwa [hx] at this

theorem four_classification {x : Vec} (hx : EvenLeech x) (hn : normSq x = 32)
    (hno : ∀ i, residueSet x 2 i = false) : FourShape x := by
  have hs : ∀ i, x i = 0 ∨ x i = 4 ∨ x i = -4 := by
    intro i
    have hp := hx.1 i
    have hr := hno i
    simp only [residueSet, Int.reduceMod, decide_eq_false_iff_not] at hr
    have hb := coordinate_sq_le hn i
    have hlo : -5 ≤ x i := by nlinarith
    have hhi : x i ≤ 5 := by nlinarith
    omega
  refine ⟨hs, ?_⟩
  have h := norm_of_signed_support x hs (by norm_num : (4 : ℤ) ≠ 0)
  rw [hn] at h
  norm_num at h
  omega

theorem octad_classification {x : Vec} (hx : EvenLeech x) (hn : normSq x = 32)
    (hne : ∃ i, residueSet x 2 i = true) : OctadShape x := by
  let w := residueSet x 2
  have h8 := golay_weight_ge_eight hx.2.2 hne
  have hpoint : ∀ i, 4 * (if w i = true then (1 : ℤ) else 0) ≤ x i ^ 2 := by
    intro i
    split_ifs with hi
    · have hi' : x i % 4 = 2 := by simpa [w, residueSet] using hi
      have hcases : 2 ≤ x i ∨ x i ≤ -2 := by omega
      rcases hcases with h | h <;> nlinarith
    · simp; positivity
  have hsum := sum_le_sum (s := univ) (fun i _ => hpoint i)
  rw [← mul_sum, sum_boole] at hsum
  change 4 * ((univ.filter (fun i => w i = true)).card : ℤ) ≤ normSq x at hsum
  rw [hn] at hsum
  have hc : (univ.filter (fun i => w i = true)).card = 8 := by dsimp [w] at *; omega
  have heqsum : ∑ i, 4 * (if w i = true then (1 : ℤ) else 0) = ∑ i, x i ^ 2 := by
    rw [← mul_sum, sum_boole, hc]
    change 4 * (8 : ℤ) = normSq x
    rw [hn]; norm_num
  have heq : ∀ i, 4 * (if w i = true then (1 : ℤ) else 0) = x i ^ 2 :=
    fun i => (sum_eq_sum_iff_of_le (fun i _ => hpoint i)).1 heqsum i (mem_univ i)
  have hs : ∀ i, x i = 0 ∨ x i = 2 ∨ x i = -2 := by
    intro i
    have hi := heq i
    split_ifs at hi <;> norm_num at hi
    · right; exact sq_eq_sq_iff_eq_or_eq_neg.mp (by nlinarith : x i ^ 2 = (2 : ℤ) ^ 2)
    · left; nlinarith [sq_nonneg (x i)]
  have hcard : (support x).card = 8 := by
    have h := norm_of_signed_support x hs (by norm_num : (2 : ℤ) ≠ 0)
    rw [hn] at h; norm_num at h; omega
  refine ⟨hs, hx.2.2, hcard, ?_⟩
  have hsum := sum_of_signed_support x hs (by norm_num : (0 : ℤ) < 2)
  rw [hcard] at hsum
  have hmod := hx.2.1
  rw [hsum] at hmod
  omega

theorem odd_classification {x : Vec} (hx : OddLeech x) (hn : normSq x = 32) : OddShape x := by
  have hone : ∀ i, 1 ≤ x i ^ 2 := by
    intro i
    have hp := hx.1 i
    have h : x i ≥ 1 ∨ x i ≤ -1 := by omega
    rcases h with h | h <;> nlinarith
  obtain ⟨j, hj1, hj2⟩ : ∃ j, x j ≠ 1 ∧ x j ≠ -1 := by
    by_contra h
    push Not at h
    have hsq : ∀ i, x i ^ 2 = 1 := by
      intro i; by_cases hi : x i = 1
      · simp [hi]
      · simp [h i hi]
    have : normSq x = 24 := by simp [normSq, hsq]
    omega
  have hj : 9 ≤ x j ^ 2 := by
    have hp := hx.1 j
    have h : x j ≥ 3 ∨ x j ≤ -3 := by omega
    rcases h with h | h <;> nlinarith
  have hpoint : ∀ i, 1 + (if i = j then (8 : ℤ) else 0) ≤ x i ^ 2 := by
    intro i; by_cases hi : i = j
    · simpa [hi] using hj
    · simpa [hi] using hone i
  have hsum : ∑ i, (1 + (if i = j then (8 : ℤ) else 0)) = ∑ i, x i ^ 2 := by
    change _ = normSq x
    rw [hn]
    simp [sum_add_distrib]
  have heq : ∀ i, 1 + (if i = j then (8 : ℤ) else 0) = x i ^ 2 :=
    fun i => (sum_eq_sum_iff_of_le (fun i _ => hpoint i)).1 hsum i (mem_univ i)
  refine ⟨residueSet x 3, hx.2.2, j, ?_⟩
  funext i
  have hi := heq i
  by_cases hij : i = j
  · subst i
    simp at hi
    have hval : x j = 3 ∨ x j = -3 :=
      sq_eq_sq_iff_eq_or_eq_neg.mp (by nlinarith : x j ^ 2 = (3 : ℤ) ^ 2)
    rcases hval with h | h <;> simp [oddVector, residueSet, h]
  · simp [hij] at hi
    have hval : x i = 1 ∨ x i = -1 :=
      sq_eq_sq_iff_eq_or_eq_neg.mp (by nlinarith : x i ^ 2 = (1 : ℤ) ^ 2)
    rcases hval with h | h <;> simp [oddVector, hij, residueSet, h]

theorem minimal_classification {x : Vec} (hx : InLeech x) (hn : normSq x = 32) :
    FourShape x ∨ OctadShape x ∨ OddShape x := by
  rcases (inLeech_iff x).1 hx with he | ho
  · by_cases hne : ∃ i, residueSet x 2 i = true
    · exact Or.inr (Or.inl (octad_classification he hn hne))
    · push Not at hne
      exact Or.inl (four_classification he hn (fun i => by simpa using hne i))
  · exact Or.inr (Or.inr (odd_classification ho hn))

theorem four_mem_norm {x : Vec} (hx : FourShape x) : InLeech x ∧ normSq x = 32 := by
  constructor
  · rw [inLeech_iff]; left
    refine ⟨fun i => ?_, ?_, ?_⟩
    · rcases hx.1 i with h | h | h <;> simp [h]
    · have hs := sum_of_signed_support x hx.1 (by norm_num : (0 : ℤ) < 4)
      rw [hx.2] at hs
      rw [hs]; omega
    · have hr : residueSet x 2 = fun _ => false := by
        funext i
        rcases hx.1 i with h | h | h <;> simp [residueSet, h]
      rw [hr]; exact isGolayWord_false
  · rw [norm_of_signed_support x hx.1 (by norm_num : (4 : ℤ) ≠ 0), hx.2]
    norm_num

theorem octad_mem_norm {x : Vec} (hx : OctadShape x) : InLeech x ∧ normSq x = 32 := by
  constructor
  · rw [inLeech_iff]; left
    refine ⟨fun i => ?_, ?_, hx.2.1⟩
    · rcases hx.1 i with h | h | h <;> simp [h]
    · have hs := sum_of_signed_support x hx.1 (by norm_num : (0 : ℤ) < 2)
      rw [hx.2.2.1] at hs
      rw [hs]
      have h := hx.2.2.2
      omega
  · rw [norm_of_signed_support x hx.1 (by norm_num : (2 : ℤ) ≠ 0), hx.2.2.1]
    norm_num

theorem oddVector_residue (w : Fin 24 → Bool) (j : Fin 24) :
    residueSet (oddVector w j) 3 = w := by
  funext i
  by_cases hi : i = j
  · subst i; cases hw : w j <;> simp [oddVector, residueSet, hw]
  · cases hw : w i <;> simp [oddVector, residueSet, hi, hw]

theorem oddVector_norm (w : Fin 24 → Bool) (j : Fin 24) : normSq (oddVector w j) = 32 := by
  have hp : ∀ i, oddVector w j i ^ 2 = 1 + (if i = j then (8 : ℤ) else 0) := by
    intro i; by_cases hi : i = j <;> cases hw : w i <;> simp [oddVector, hi, hw]
  simp [normSq, hp, sum_add_distrib]

theorem oddVector_sum (w : Fin 24 → Bool) (j : Fin 24) :
    ∑ i, oddVector w j i = 24 - 2 * ((univ.filter (fun i => w i = true)).card : ℤ) -
      4 * (if w j then -1 else 1) := by
  have hp : ∀ i, oddVector w j i = 1 - 2 * (if w i = true then 1 else 0) -
      (if i = j then 4 * (if w j then -1 else 1) else 0) := by
    intro i
    by_cases hi : i = j
    · subst i; cases hw : w j <;> simp [oddVector, hw]
    · cases hw : w i <;> simp [oddVector, hi, hw]
  rw [sum_congr rfl (fun i _ => hp i), sum_sub_distrib, sum_sub_distrib, ← mul_sum, sum_boole]
  simp

theorem oddVector_mem {w : Fin 24 → Bool} (hw : IsGolayWord w) (j : Fin 24) :
    InLeech (oddVector w j) := by
  rw [inLeech_iff]; right
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = j
    · subst i; cases hwi : w j <;> simp [oddVector, hwi]
    · cases hwi : w i <;> simp [oddVector, hi, hwi]
  · rw [oddVector_sum]
    have hfour := golay_weight_mod_four hw
    cases hj : w j <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
  · rw [oddVector_residue]; exact hw

theorem odd_mem_norm {x : Vec} (hx : OddShape x) : InLeech x ∧ normSq x = 32 := by
  obtain ⟨w, hw, j, rfl⟩ := hx
  exact ⟨oddVector_mem hw j, oddVector_norm w j⟩

theorem minimal_iff (x : Vec) :
    InLeech x ∧ normSq x = 32 ↔ FourShape x ∨ OctadShape x ∨ OddShape x := by
  constructor
  · rintro ⟨hx, hn⟩; exact minimal_classification hx hn
  · rintro (h | h | h)
    · exact four_mem_norm h
    · exact octad_mem_norm h
    · exact odd_mem_norm h

end LeechMinimal
