import LeechNorm48
import LeechShellMoments

/-! # Second and fourth powers on the squared-length-48 shell

For the shortest axis (4, −4, 0, …), the dot product with x is four times
the difference of its first two coordinates.
-/
namespace LeechNorm48Layers

open LeechLattice LeechMinimal LeechSymmetry ConwayMoves ConwayIncidence GolayMathieu Finset

abbrev Shell := LeechShellMoments.Shell 48

noncomputable instance : Fintype Shell := by
  have : Finite Shell := (Nat.card_pos_iff.mp
    (show 0 < Nat.card Shell by rw [LeechNorm48.card_norm48_vectors]; decide)).2
  exact Fintype.ofFinite _

theorem shell_card : Fintype.card Shell = 16773120 :=
  Nat.card_eq_fintype_card.symm.trans LeechNorm48.card_norm48_vectors

def onShell (g : Aut) : Shell ≃ Shell := LeechShellMoments.onShell g

abbrev coord (x : Shell) (i : Point) : ℤ := LeechShellMoments.coord x i

def diff (x : Shell) : ℤ := LeechShellMoments.diff x

/-- Sum (x₀ − x₁)² and (x₀ − x₁)⁴ over the vectors of squared length 48. -/
theorem diff_moments :
    (∑ x : Shell, diff x ^ 2) = 67092480 ∧ (∑ x : Shell, diff x ^ 4) = 743178240 := by
  obtain ⟨h2, h4⟩ := LeechShellMoments.diff_moments 48
  change 12 * (∑ x : Shell, diff x ^ 2) = 48 * (Fintype.card Shell : ℤ) at h2
  change 52 * (∑ x : Shell, diff x ^ 4) = 48 ^ 2 * (Fintype.card Shell : ℤ) at h4
  rw [shell_card] at h2 h4
  constructor <;> omega

end LeechNorm48Layers
