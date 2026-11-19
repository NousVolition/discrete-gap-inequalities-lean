-- GapMirror.lean
-- The gap toy's mirror: fading below the gap and blow-up above it are the same motion, sign flipped.
-- Plain Lean 4 (leanprover/lean4:v4.34.0-rc2), core only, no Mathlib. Numbers are fractions (`Rat`).

/-!
# The gap toy's mirror

The toy, with no spreading: a flat bump of height `u` changes at the rate `u * u - g * u`,
where `g` is the gap. Below the gap the bump fades; above it the bump blows up.

Time enters through one number, the growth factor `r` of a stretch of time. `r = 1` is no time at
all and `r` grows as time passes (for a time `t` the factor is `e^(g t)`; that link to clock time
needs calculus and is not part of this file). `step g r u` is the bump after such a stretch.

What is proved here:

* `step` is the toy's motion: no time changes nothing (`step_one`), two stretches multiply their
  factors (`step_step`), and the change over a stretch is the rate `u * u - g * u` times `r - 1`,
  divided by a number that starts at `g` (`step_change`).
* The mirror variable `z = 1 - g / u` is only multiplied by `r` (`z_step`). The edge `u = g` is
  `z = 0`, blow-up is `z = 1`, half the edge `u = g / 2` is `z = -1`.
* Flipping the sign of `z` pairs each bump above the edge with one below it (`mirror`,
  `z_mirror`), and the pairing does not care when you apply it (`mirror_step`).
* The pair stays matched at every moment (`mirror_sum`):
  `g / (bump above) + g / (bump below) = 2`.
* Above the gap the bump blows up exactly when `r` reaches `A / (A - g)` (`blow_factor`,
  `finite_before`, `blows_up`), and at that same moment its mirror is at half the edge
  (`mirror_time`).
* Below the gap the bump stays above zero, never grows, and shrinks at least like `1 / r`
  (`below_positive`, `below_never_grows`, `below_fades`).
-/

namespace GapMirror

/-- The mirror variable. -/
def z (g u : Rat) : Rat := 1 - g / u

/-- The mirror bump: the height on the other side of the edge with the opposite `z`. -/
def mirror (g A : Rat) : Rat := g * A / (2 * A - g)

/-- The bump after a stretch of time with growth factor `r`, starting from height `u`. -/
def step (g r u : Rat) : Rat := g * u / (r * g - (r - 1) * u)

/-! ## `step` is the toy's motion -/

/-- No time changes nothing. -/
theorem step_one (g u : Rat) (hg : g ≠ 0) : step g 1 u = u := by
  unfold step; grind

/-- Two stretches in a row multiply their growth factors. -/
theorem step_step (g r s u : Rat) (hg : g ≠ 0) (hd : r * g - (r - 1) * u ≠ 0) :
    step g s (step g r u) = step g (s * r) u := by
  unfold step; grind

/-- The change over a stretch is the toy's rate `u * u - g * u` times `r - 1`, divided by a
number that equals `g` when `r = 1`. -/
theorem step_change (g r u : Rat) (hd : r * g - (r - 1) * u ≠ 0) :
    step g r u - u = (r - 1) * (u * u - g * u) / (r * g - (r - 1) * u) := by
  unfold step; grind

/-- A bump that starts exactly on the gap stays there. -/
theorem edge (g r : Rat) (hg : g ≠ 0) : step g r g = g := by
  unfold step; grind

/-! ## The mirror variable -/

/-- The rate of `z` is `g * z`: the toy's rate `u * u - g * u`, carried through `z = 1 - g / u`. -/
theorem rate_mirror (g u : Rat) (hu : u ≠ 0) :
    g / (u * u) * (u * u - g * u) = g * z g u := by
  unfold z; grind

/-- Over a stretch of time, `z` is only multiplied by the growth factor. -/
theorem z_step (g r u : Rat) (hg : g ≠ 0) (hu : u ≠ 0) :
    z g (step g r u) = r * z g u := by
  unfold z step; grind

/-- The mirror bump has the opposite `z`. -/
theorem z_mirror (g A : Rat) (hg : g ≠ 0) (hA : A ≠ 0) (h2 : 2 * A - g ≠ 0) :
    z g (mirror g A) = - z g A := by
  unfold z mirror; grind

theorem mirror_ne_zero (g A : Rat) (hg : g ≠ 0) (hA : A ≠ 0) (h2 : 2 * A - g ≠ 0) :
    mirror g A ≠ 0 := by
  unfold mirror; grind

/-! ## The pair stays matched -/

/-- At every moment, `g / (bump above) + g / (bump below) = 2`. -/
theorem mirror_sum (g r A : Rat) (hg : g ≠ 0) (hA : A ≠ 0) (h2 : 2 * A - g ≠ 0) :
    g / step g r A + g / step g r (mirror g A) = 2 := by
  have h1 : ∀ u : Rat, g / u = 1 - z g u := by intro u; unfold z; grind
  rw [h1, h1, z_step g r A hg hA, z_step g r (mirror g A) hg (mirror_ne_zero g A hg hA h2),
    z_mirror g A hg hA h2]
  grind

/-- Mirror then wait, or wait then mirror: the same bump. `hd` says the bump has not blown up
yet, `hm` says its mirror has not. -/
theorem mirror_step (g r A : Rat) (hg : g ≠ 0) (hA : A ≠ 0) (h2 : 2 * A - g ≠ 0)
    (hd : r * g - (r - 1) * A ≠ 0) (hm : (r + 1) * A - r * g ≠ 0) :
    mirror g (step g r A) = step g r (mirror g A) := by
  have hl : mirror g (step g r A) = g * A / ((r + 1) * A - r * g) := by
    have h3 : 2 * (g * A / (r * g - (r - 1) * A)) - g ≠ 0 := by
      intro h
      apply hm
      grind
    unfold mirror step; grind
  have hr : step g r (mirror g A) = g * A / ((r + 1) * A - r * g) := by
    have h4 : r * g - (r - 1) * (g * A / (2 * A - g)) ≠ 0 := by
      intro h
      apply hm
      grind
    unfold mirror step; grind
  rw [hl, hr]

/-! ## Above the gap: blow-up -/

/-- The bump's denominator reaches zero exactly when the growth factor is `A / (A - g)`. -/
theorem blow_factor (g r A : Rat) (hAg : A - g ≠ 0) :
    r * g - (r - 1) * A = 0 ↔ r = A / (A - g) := by
  grind

/-- Bump times remaining room is constant, so the bump grows without limit as the room runs out. -/
theorem blow_shape (g r A : Rat) (hAg : A - g ≠ 0) (hd : r * g - (r - 1) * A ≠ 0) :
    step g r A * ((A / (A - g) - r) * (A - g)) = g * A := by
  unfold step; grind

/-- Before the blow factor the bump is still finite: its denominator is above zero. -/
theorem finite_before (g r A : Rat) (hA : g < A) (hr : r < A / (A - g)) :
    0 < r * g - (r - 1) * A := by
  have hAg : 0 < A - g := by grind
  have h := (Rat.lt_div_iff hAg).mp hr
  grind

/-- Above the gap the bump reaches every height before the blow factor: for every `M > 0` there
is a growth factor `r`, at least 1 and below `A / (A - g)`, where the bump is exactly `A + M`. -/
theorem blows_up (g A M : Rat) (hg : 0 < g) (hA : g < A) (hM : 0 < M) :
    ∃ r : Rat, 1 ≤ r ∧ r < A / (A - g) ∧ step g r A = A + M := by
  have hA0 : 0 < A := by grind
  have hAg : 0 < A - g := by grind
  have hAM : 0 < A + M := by grind
  have hgM : 0 < g * M := Rat.mul_pos hg hM
  have hgA : 0 < g * A := Rat.mul_pos hg hA0
  have hden : 0 < (A - g) * (A + M) := Rat.mul_pos hAg hAM
  refine ⟨1 + g * M / ((A - g) * (A + M)), ?_, ?_, ?_⟩
  · have : 0 < g * M / ((A - g) * (A + M)) := by
      rw [Rat.lt_div_iff hden]; grind
    grind
  · rw [Rat.lt_div_iff hAg]
    have e : (1 + g * M / ((A - g) * (A + M))) * (A - g) = (A - g) + g * M / (A + M) := by
      grind
    rw [e]
    have : g * M / (A + M) < g := by
      rw [Rat.div_lt_iff hAM]
      have := Rat.mul_pos hg hA0
      grind
    grind
  · have h1 : A - g ≠ 0 := by grind
    have h2 : A + M ≠ 0 := by grind
    have h3 : g ≠ 0 := by grind
    have h4 : A ≠ 0 := by grind
    have hD : (1 + g * M / ((A - g) * (A + M))) * g - (1 + g * M / ((A - g) * (A + M)) - 1) * A
        = g * A / (A + M) := by grind
    unfold step
    rw [hD]
    grind

/-- The bump above blows up exactly when its mirror has fallen to half the edge. -/
theorem mirror_time (g A : Rat) (hg : g ≠ 0) (hA : A ≠ 0) (hAg : A - g ≠ 0) (h2 : 2 * A - g ≠ 0) :
    step g (A / (A - g)) (mirror g A) = g / 2 := by
  unfold step mirror; grind

/-! ## Below the gap: fading -/

theorem below_denominator (g r u : Rat) (hg : 0 < g) (hu : u < g) (hr : 1 ≤ r) :
    0 < r * g - (r - 1) * u := by
  have hp : 0 ≤ (r - 1) * (g - u) := Rat.mul_nonneg (by grind) (by grind)
  grind

/-- Below the gap the bump stays above zero. -/
theorem below_positive (g r u : Rat) (hg : 0 < g) (hu0 : 0 < u) (hu : u < g) (hr : 1 ≤ r) :
    0 < step g r u := by
  have hD := below_denominator g r u hg hu hr
  have hgu : 0 < g * u := Rat.mul_pos hg hu0
  unfold step
  rw [Rat.lt_div_iff hD]
  grind

/-- Below the gap the bump never grows. -/
theorem below_never_grows (g r u : Rat) (hg : 0 < g) (hu0 : 0 < u) (hu : u < g) (hr : 1 ≤ r) :
    step g r u ≤ u := by
  have hD := below_denominator g r u hg hu hr
  have hp : 0 ≤ (r - 1) * (g - u) := Rat.mul_nonneg (by grind) (by grind)
  have hq : 0 ≤ u * ((r - 1) * (g - u)) := Rat.mul_nonneg (by grind) hp
  apply Rat.not_lt.mp
  intro h
  unfold step at h
  rw [Rat.lt_div_iff hD] at h
  grind

/-- Below the gap the bump shrinks at least like `1 / r`: bump times `r` times `(g - u)` never
exceeds `g * u`. Since `r` grows like `e^(g t)`, the bump fades at the gap's own rate. -/
theorem below_fades (g r u : Rat) (hg : 0 < g) (hu0 : 0 < u) (hu : u < g) (hr : 1 ≤ r) :
    step g r u * (r * (g - u)) ≤ g * u := by
  have hD := below_denominator g r u hg hu hr
  have hpos := below_positive g r u hg hu0 hu hr
  have hfull : step g r u * (r * g - (r - 1) * u) = g * u := by
    unfold step; grind
  have hle : r * (g - u) ≤ r * g - (r - 1) * u := by grind
  have := Rat.mul_le_mul_of_nonneg_left hle (Rat.le_of_lt hpos)
  grind

end GapMirror

-- Axiom check: every line must list only standard axioms (no `sorryAx`).
#print axioms GapMirror.step_one
#print axioms GapMirror.step_step
#print axioms GapMirror.step_change
#print axioms GapMirror.edge
#print axioms GapMirror.rate_mirror
#print axioms GapMirror.z_step
#print axioms GapMirror.z_mirror
#print axioms GapMirror.mirror_ne_zero
#print axioms GapMirror.mirror_sum
#print axioms GapMirror.mirror_step
#print axioms GapMirror.blow_factor
#print axioms GapMirror.blow_shape
#print axioms GapMirror.finite_before
#print axioms GapMirror.blows_up
#print axioms GapMirror.mirror_time
#print axioms GapMirror.below_denominator
#print axioms GapMirror.below_positive
#print axioms GapMirror.below_never_grows
#print axioms GapMirror.below_fades
