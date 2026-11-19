import E8PlumbingBridge

/- A separate check of the own-part and between-part identity for the published
   plumbing matrix. The integral matrix K is the positive sign convention. -/
namespace E8CostMirror

private def K (i j : Fin 8) : ℤ := -E8PlumbingBridge.E8_matrix i j
private def sign : Fin 8 → ℤ := ![1, -1, 1, -1, 1, -1, 1, -1]

def flip (x : Fin 8 → ℝ) (i : Fin 8) : ℝ := (sign i : ℝ) * x i
def cost (x : Fin 8 → ℝ) : ℝ := ∑ i, ∑ j, x i * (K i j : ℝ) * x j

private theorem coefficient_pair : ∀ i j : Fin 8,
    K i j + sign i * K i j * sign j = if j = i then 4 else 0 := by decide

/-- Across all real assignments, flipping the signs on one side of the tree
    reverses every edge contribution and preserves every diagonal contribution. -/
theorem cost_pair (x : Fin 8 → ℝ) :
    cost x + cost (flip x) = 4 * ∑ i, x i ^ 2 := by
  have entry (i j : Fin 8) :
      (K i j : ℝ) + (sign i : ℝ) * K i j * sign j = if j = i then 4 else 0 := by
    have h := congrArg (fun n : ℤ => (n : ℝ)) (coefficient_pair i j)
    by_cases e : j = i <;> simpa [e] using h
  unfold cost
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ i : Fin 8, ∑ j : Fin 8, (if j = i then 4 * x i ^ 2 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = ((K i j : ℝ) + (sign i : ℝ) * K i j * sign j) * (x i * x j) := by
          unfold flip
          ring
        _ = _ := by
          rw [entry]
          by_cases e : j = i <;> simp [e, pow_two]
    _ = _ := by simp [Finset.mul_sum]

#print axioms E8CostMirror.cost_pair
end E8CostMirror
