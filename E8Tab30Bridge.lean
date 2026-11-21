import E8PlumbingBridge

/-!
# Tab 30's rational roots and the existing E₈ matrix

Part A is entirely internal to Lean. `simpleRoots` is an explicit rational matrix.
A separate playground source-file comparison checks the connection to the page's
`SIMPLE_ROOTS` literal; Lean does not read or certify the web page.

Rows and coordinates use zero-based indices. Rows 0 through 5 are eᵢ - eᵢ₊₁,
row 6 is e₅ + e₆, and row 7 has all eight coordinates -1/2.
-/

namespace E8Tab30Bridge

/-- Exact rational coordinates, with one root per row. -/
def simpleRoots : Matrix (Fin 8) (Fin 8) ℚ :=
  !![1, -1, 0, 0, 0, 0, 0, 0;
     0, 1, -1, 0, 0, 0, 0, 0;
     0, 0, 1, -1, 0, 0, 0, 0;
     0, 0, 0, 1, -1, 0, 0, 0;
     0, 0, 0, 0, 1, -1, 0, 0;
     0, 0, 0, 0, 0, 1, -1, 0;
     0, 0, 0, 0, 0, 1, 1, 0;
     -1 / 2, -1 / 2, -1 / 2, -1 / 2, -1 / 2, -1 / 2, -1 / 2, -1 / 2]

/-- The Gram matrix is formed from these vectors, not supplied independently. -/
def G : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => ∑ k : Fin 8, simpleRoots i k * simpleRoots j k

/-- Page indices mapped to the existing plumbing matrix's indices. -/
def p : Equiv.Perm (Fin 8) where
  toFun := ![0, 1, 2, 3, 4, 7, 5, 6]
  invFun := ![0, 1, 2, 3, 4, 6, 7, 5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

/-- Each of the eight specified rational roots has squared length two. -/
theorem simpleRoots_sq_length (i : Fin 8) :
    (∑ k : Fin 8, (simpleRoots i k) ^ 2) = 2 := by
  fin_cases i <;> norm_num [simpleRoots, Fin.sum_univ_succ]

/-- All 64 Gram entries equal the negated, relabelled existing matrix entries. -/
theorem gram_entry (i j : Fin 8) :
    G i j = -(E8PlumbingBridge.E8_matrix (p i) (p j) : ℚ) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [G, simpleRoots, p, E8PlumbingBridge.E8_matrix, Fin.sum_univ_succ] <;>
    decide

/-- The existing integer matrix viewed over the rationals. -/
def E8Q : Matrix (Fin 8) (Fin 8) ℚ :=
  E8PlumbingBridge.E8_matrix.map (fun x : ℤ => (x : ℚ))

/-- The entrywise bridge expressed as a matrix identity. -/
theorem gram_matrix : G = -(E8Q.submatrix p p) := by
  ext i j
  exact gram_entry i j

/-- Transfer the existing determinant theorem from integers to rationals. -/
theorem E8Q_det : E8Q.det = 1 := by
  unfold E8Q
  rw [← Int.cast_det, E8PlumbingBridge.E8_det]
  norm_num

/-- Derived from `E8_det`: simultaneous relabelling preserves determinant,
and negating an eight-by-eight matrix contributes (-1)^8 = 1. -/
theorem det_G : G.det = 1 := by
  rw [gram_matrix, Matrix.det_neg, Matrix.det_submatrix_equiv_self, E8Q_det]
  norm_num

end E8Tab30Bridge
