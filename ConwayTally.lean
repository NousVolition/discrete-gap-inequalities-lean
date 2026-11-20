import ConwayCoordinates

/-! # Signed coordinate equalities in the three shortest-vector families -/

namespace ConwayIncidence

open GolayMathieu LeechMinimal Finset

def score (x : Vec) (i j : Point) (b : Bool) : Nat :=
  if j ≠ i ∧ x i = twoSign b (x j) then 1 else 0
def tally (x : Vec) : Nat := ∑ i : Point, ∑ j : Point, ∑ b : Bool, score x i j b

def indicator (s : Finset Point) (i j : Point) : Nat :=
  if i ∈ s ∧ j ∈ s ∧ j ≠ i then 1 else 0

theorem indicator_sum (s : Finset Point) :
    (∑ i, ∑ j, indicator s i j) = s.card * (s.card-1) := by
  have row (i : Point) : (∑ j, indicator s i j) = if i ∈ s then s.card-1 else 0 := by
    by_cases h : i ∈ s
    · simp only [indicator,h,true_and,ite_true]
      have he (j : Point) : (j ∈ s ∧ j ≠ i) ↔ j ∈ s.erase i := by simp [and_comm]
      simp_rw [he]
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_erase_of_mem h]; rfl
    · simp [indicator,h]
  simp_rw [row]
  simp

theorem tally_even (x : Vec) (q : ℤ) (hq : 0 < q)
    (hv : ∀ i, x i = 0 ∨ x i = q ∨ x i = -q) :
    tally x = (support x).card * ((support x).card-1) +
      2 * ((24 - (support x).card) * (24-(support x).card-1)) := by
  let s := support x
  have row (i j : Point) : (∑ b : Bool, score x i j b) =
      indicator s i j + 2 * indicator (Finset.univ \ s) i j := by
    by_cases h : j = i
    · subst j; simp [score,indicator]
    · have hn : q ≠ -q := by omega
      have hn' : -q ≠ q := Ne.symm hn
      rcases hv i with hi|hi|hi <;> rcases hv j with hj|hj|hj <;>
        simp [score,indicator,s,support,hi,hj,h,twoSign,hq.ne', hq.ne, hn, hn']
  have hc : (Finset.univ \ s).card = 24 - s.card := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]; rfl
  unfold tally
  simp_rw [row, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [indicator_sum, indicator_sum, hc]

theorem tally_odd {x : Vec} (hx : OddShape x) : tally x = 506 := by
  obtain ⟨w, _, k, rfl⟩ := hx
  let s := Finset.univ.erase k
  have row (i j : Point) : (∑ b : Bool, score (oddVector w k) i j b) = indicator s i j := by
    by_cases h : j = i
    · subst j; simp [score,indicator]
    · by_cases hi : i = k <;> by_cases hj : j = k <;> cases hwi : w i <;> cases hwj : w j <;>
        simp_all [score,indicator,s,twoSign,oddVector]
  unfold tally
  simp_rw [row]
  rw [indicator_sum]
  simp [s]


end ConwayIncidence
