import RingDecay
import Unify

/-!
# The gap of a Cartesian graph product and the grid made of two rings

For finite simple graphs, `CartesianGraphProduct.boxProd_gap` lifts mean-zero Poincaré bounds
on the factors to their minimum on mathlib's box product `G □ H`. The energy counts each
undirected edge once. If the factor constants are optimal, their minimum is optimal on the
product (`boxProd_gap_sharp`). The weighted theorem `cartesian_gap_iff` characterizes all
product bounds by restricting to functions of a single coordinate.

For a finite family `G i`, vertices of `boxPi G` are dependent tuples. An edge changes one
coordinate along an edge of its factor. For nonempty factors, a constant bounds the product
exactly when it bounds every factor (`boxPi_gap_iff`). For a nonempty index type, the sharp
gap is the minimum of the sharp factor gaps (`boxPi_gap_sharp`). The same conclusions hold
for nonnegative ordered-pair weights. The empty product has one vertex, so every real
constant satisfies its mean-zero inequality.

## The torus specialization

The flat grid `ZMod m × ZMod n` is two rings laid across each other: each point `(i, j)` has a
neighbor one step along the first ring, `(i + 1, j)`, and one step along the second, `(i, j + 1)`.
Its energy is

  `energy f = ∑ (i, j), ((f (i + 1, j) - f (i, j)) ^ 2 + (f (i, j + 1) - f (i, j)) ^ 2)`.

For `f` with `∑ f = 0`,

  `min (gap m) (gap n) * ∑ f ^ 2 ≤ energy f`   (`grid_gap`),

where `gap k = 2 - 2 cos (2π/k) = 4 sin² (π/k)` is the ring gap from `RingDecay.lean`. For
`m, n ≥ 2` the waves `cos (2π i/m)` along the first ring and `cos (2π j/n)` along the second have
mean zero and meet their own ring gap with equality (`rowWave_sharp`, `colWave_sharp`), so the
constant `min (gap m) (gap n)` is attained (`grid_gap_sharp`): the grid settles no slower than its
slower ring, and no faster.

For a nonempty finite family of periods `n i ≥ 2`, `RingGrid.torus_gap_sharp` gives the
minimum of the ring gaps on the corresponding periodic grid in any dimension.

The general proof splits `f` into row means and centered rows. The ring-specific identities
below give this decomposition explicitly, with row means `c i = (∑ j, f (i, j)) / n` and the rest
`g (i, j) = f (i, j) - c i`. Each row of `g` has sum zero, so the cross terms vanish
(`sum_sq_add_of_sum_zero`):

* `∑ f ^ 2 = n ∑ c ^ 2 + ∑ g ^ 2` (`sum_sq_split`);
* steps along the first ring: `≥ n ∑ (c (i + 1) - c i) ^ 2 ≥ n · gap m · ∑ c ^ 2`
  (`first_steps_split`, then the cycle Wirtinger inequality for `c`);
* steps along the second ring: `≥ gap n · ∑ g ^ 2` (the cycle Wirtinger inequality on each row).

The last part is the heat flow on the grid, `f ↦ f - τ * lap f` with `lap f` equal to `4 f` minus the
four neighbors. For `0 ≤ τ ≤ 1/4` and `f` with sum zero, one step gives
`∑ next ² ≤ (1 - 2τ(1 - 4τ) · min (gap m) (gap n)) · ∑ f ^ 2` (`heatStep_decay`), from `grid_gap`
and the Cauchy–Schwarz bound `∑ (lap f) ^ 2 ≤ 8 · energy f` (`sum_lap_sq_le`). After `k` steps the
factor is raised to the power `k` (`iterate_decay`), and for `m, n ≥ 2` and `0 < τ < 1/4` every
value goes to the mean (`iterate_tendsto_mean`).
-/

open Finset
open scoped Real

namespace CartesianGraphProduct

open Unify (energy)

variable {A B : Type*} [Fintype A] [Fintype B]

/-- A Poincaré lower bound for the ordered-pair energy of a finite weighted graph. -/
def GapBound (w : A → A → ℝ) (k : ℝ) : Prop :=
  ∀ f : A → ℝ, ∑ x, f x = 0 → k * ∑ x, f x ^ 2 ≤ energy w f

private lemma GapBound.mono {w : A → A → ℝ} {k l : ℝ} (h : GapBound w l) (hkl : k ≤ l) :
    GapBound w k := fun f hf =>
  (mul_le_mul_of_nonneg_right hkl (Finset.sum_nonneg (fun x _ => sq_nonneg (f x)))).trans (h f hf)

/-- Each factor edge is copied along every vertex of the other factor. -/
noncomputable def cartesianWeight (u : A → A → ℝ) (v : B → B → ℝ)
    (p q : A × B) : ℝ := by
  classical
  exact (if p.2 = q.2 then u p.1 q.1 else 0) + (if p.1 = q.1 then v p.2 q.2 else 0)

/-- The product energy is the sum of the energies on its columns and rows. -/
theorem energy_cartesian (u : A → A → ℝ) (v : B → B → ℝ) (f : A × B → ℝ) :
    energy (cartesianWeight u v) f =
      (∑ b, energy u (fun a => f (a, b))) + ∑ a, energy v (fun b => f (a, b)) := by
  classical
  have h (a : A) (b : B) :
      ∑ q, cartesianWeight u v (a, b) q * (f (a, b) - f q) ^ 2 =
        (∑ x, u a x * (f (a, b) - f (x, b)) ^ 2) +
        ∑ y, v b y * (f (a, b) - f (a, y)) ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp only [cartesianWeight, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib]
    congr 1
    · simp
    · rw [Finset.sum_comm]
      simp
  unfold energy
  rw [Fintype.sum_prod_type]
  simp only [h, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun a b => ∑ x, u a x * (f (a, b) - f (x, b)) ^ 2)]

private noncomputable def average (f : B → ℝ) : ℝ := (∑ b, f b) / Fintype.card B

private lemma centered_sum [Nonempty B] (f : B → ℝ) :
    ∑ b, (f b - average f) = 0 := by
  have hn : (Fintype.card B : ℝ) ≠ 0 := by positivity
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, average]
  field_simp
  ring

private lemma sum_sq_split [Nonempty B] (f : B → ℝ) :
    ∑ b, f b ^ 2 = (Fintype.card B : ℝ) * average f ^ 2 + ∑ b, (f b - average f) ^ 2 := by
  have h (b : B) : f b ^ 2 = average f ^ 2 + 2 * average f * (f b - average f)
      + (f b - average f) ^ 2 := by ring
  calc
    ∑ b, f b ^ 2 = ∑ b, (average f ^ 2 + 2 * average f * (f b - average f)
        + (f b - average f) ^ 2) := Finset.sum_congr rfl (fun b _ => h b)
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, centered_sum, mul_zero, add_zero,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Averaging a row contracts each squared edge difference by Jensen's inequality. -/
private lemma average_edge_le [Nonempty B] (f g : B → ℝ) :
    (Fintype.card B : ℝ) * (average f - average g) ^ 2 ≤ ∑ b, (f b - g b) ^ 2 := by
  have h := sum_sq_split (fun b => f b - g b)
  have ha : average (fun b => f b - g b) = average f - average g := by
    simp only [average, Finset.sum_sub_distrib, sub_div]
  rw [ha] at h
  exact h ▸ le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Tensorization of the Poincaré inequality on finite weighted graphs.
Only the first factor needs an explicit nonnegativity hypothesis. Its rows are averaged
edge by edge, while the second factor bound is applied directly to each centered row. -/
theorem cartesian_gap {u : A → A → ℝ} {v : B → B → ℝ}
    (hu : ∀ x y, 0 ≤ u x y) {k l : ℝ} (hG : GapBound u k) (hH : GapBound v l) :
    GapBound (cartesianWeight u v) (min k l) := by
  intro f hf
  rcases isEmpty_or_nonempty B with hB | hB
  · simp [energy]
  let c (a : A) := average (fun b => f (a, b))
  let r (a : A) (b : B) := f (a, b) - c a
  let N : ℝ := Fintype.card B
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hc : ∑ a, c a = 0 := by
    rw [Fintype.sum_prod_type] at hf
    simp only [c, average, ← Finset.sum_div, hf, zero_div]
  have hs : ∑ p, f p ^ 2 = N * (∑ a, c a ^ 2) + ∑ a, ∑ b, r a b ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => sum_sq_split (fun b => f (a, b)))
  have hcol : N * energy u c ≤ ∑ b, energy u (fun a => f (a, b)) := by
    unfold energy
    rw [Finset.sum_comm (f := fun b a => ∑ x, u a x * (f (a, b) - f (x, b)) ^ 2), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    rw [Finset.sum_comm (f := fun b x => u a x * (f (a, b) - f (x, b)) ^ 2), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    rw [← Finset.mul_sum, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (average_edge_le (fun b => f (a, b)) (fun b => f (x, b))) (hu a x)
  have hrow : min k l * (∑ a, ∑ b, r a b ^ 2) ≤ ∑ a, energy v (fun b => f (a, b)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    have h := hH.mono (min_le_right k l) (r a) (centered_sum (fun b => f (a, b)))
    simpa only [energy, r, sub_sub_sub_cancel_right] using h
  rw [hs, energy_cartesian, mul_add, mul_left_comm (min k l) N]
  exact add_le_add ((mul_le_mul_of_nonneg_left (hG.mono (min_le_left k l) c hc) hN).trans hcol) hrow

private lemma sum_lift_fst (g : A → ℝ) : ∑ p : A × B, g p.1 = Fintype.card B * ∑ a, g a := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp [nsmul_eq_mul]

private lemma sum_lift_snd (g : B → ℝ) : ∑ p : A × B, g p.2 = Fintype.card A * ∑ b, g b := by
  rw [Fintype.sum_prod_type]
  simp [nsmul_eq_mul]

private lemma energy_const (w : A → A → ℝ) (c : ℝ) : energy w (fun _ => c) = 0 := by
  simp [energy]

/-- Testing the product on functions of one coordinate recovers both factor bounds.
Thus a number is a valid product bound exactly when it works on each factor. -/
theorem cartesian_gap_iff [Nonempty A] [Nonempty B] {u : A → A → ℝ} {v : B → B → ℝ}
    (hu : ∀ x y, 0 ≤ u x y) (k : ℝ) :
    GapBound (cartesianWeight u v) k ↔ GapBound u k ∧ GapBound v k := by
  constructor
  · intro h
    constructor
    · intro g hg
      have h0 : ∑ p : A × B, g p.1 = 0 := by rw [sum_lift_fst, hg, mul_zero]
      have htest := h (fun p => g p.1) h0
      rw [sum_lift_fst (fun a => g a ^ 2), energy_cartesian] at htest
      simp only [energy_const, Finset.sum_const_zero, add_zero, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, mul_left_comm k] at htest
      exact le_of_mul_le_mul_left htest (by positivity : (0 : ℝ) < Fintype.card B)
    · intro g hg
      have h0 : ∑ p : A × B, g p.2 = 0 := by rw [sum_lift_snd, hg, mul_zero]
      have htest := h (fun p => g p.2) h0
      rw [sum_lift_snd (fun b => g b ^ 2), energy_cartesian] at htest
      simp only [energy_const, Finset.sum_const_zero, zero_add, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, mul_left_comm k] at htest
      exact le_of_mul_le_mul_left htest (by positivity : (0 : ℝ) < Fintype.card A)
  · rintro ⟨hG, hH⟩
    simpa only [min_self] using cartesian_gap hu hG hH

/-- A sharp gap is the largest constant in the mean-zero Poincaré inequality. -/
def IsSharpGap (w : A → A → ℝ) (k : ℝ) : Prop :=
  IsGreatest {c | GapBound w c} k

/-- The sharp gap of the Cartesian product is the smaller sharp factor gap. -/
theorem cartesian_gap_sharp [Nonempty A] [Nonempty B] {u : A → A → ℝ} {v : B → B → ℝ}
    (hu : ∀ x y, 0 ≤ u x y) {k l : ℝ} (hG : IsSharpGap u k) (hH : IsSharpGap v l) :
    IsSharpGap (cartesianWeight u v) (min k l) := by
  refine ⟨cartesian_gap hu hG.1 hH.1, ?_⟩
  intro t ht
  obtain ⟨h₁, h₂⟩ := (cartesian_gap_iff hu t).mp ht
  exact le_min (hG.2 h₁) (hH.2 h₂)

/-- Half weight on adjacent ordered pairs counts each undirected edge exactly once. -/
noncomputable def simpleWeight (G : SimpleGraph A) (x y : A) : ℝ := by
  classical
  exact if G.Adj x y then 1 / 2 else 0

/-- This normalization gives the quadratic form of the combinatorial Laplacian. -/
theorem energy_eq_lapMatrix (G : SimpleGraph A) [DecidableEq A] [DecidableRel G.Adj] (f : A → ℝ) :
    energy (simpleWeight G) f = Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) f f := by
  rw [SimpleGraph.lapMatrix_toLinearMap₂']
  simp only [energy, simpleWeight, Finset.sum_div]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  by_cases h : G.Adj x y <;> simp [h, div_eq_mul_inv, mul_comm]

omit [Fintype A] in
private lemma simpleWeight_nonneg (G : SimpleGraph A) (x y : A) : 0 ≤ simpleWeight G x y := by
  classical
  unfold simpleWeight
  split <;> norm_num

omit [Fintype A] [Fintype B] in
theorem simpleWeight_boxProd (G : SimpleGraph A) (H : SimpleGraph B) :
    simpleWeight (G □ H) = cartesianWeight (simpleWeight G) (simpleWeight H) := by
  classical
  funext ⟨a, b⟩ ⟨x, y⟩
  by_cases ha : a = x <;> by_cases hb : b = y <;>
    simp_all [simpleWeight, cartesianWeight, SimpleGraph.boxProd_adj]

/-- Poincaré bounds for mathlib's Cartesian product of finite simple graphs. -/
theorem boxProd_gap {G : SimpleGraph A} {H : SimpleGraph B} {k l : ℝ}
    (hG : GapBound (simpleWeight G) k) (hH : GapBound (simpleWeight H) l) :
    GapBound (simpleWeight (G □ H)) (min k l) := by
  rw [simpleWeight_boxProd]
  exact cartesian_gap (simpleWeight_nonneg G) hG hH

/-- If the two factor gaps are optimal, so is their minimum on the box product. -/
theorem boxProd_gap_sharp [Nonempty A] [Nonempty B] {G : SimpleGraph A} {H : SimpleGraph B}
    {k l : ℝ} (hG : IsSharpGap (simpleWeight G) k) (hH : IsSharpGap (simpleWeight H) l) :
    IsSharpGap (simpleWeight (G □ H)) (min k l) := by
  rw [simpleWeight_boxProd]
  exact cartesian_gap_sharp (simpleWeight_nonneg G) hG hH

/-! ## Products indexed by a finite type -/

section FiniteProduct

open scoped Classical

variable {ι : Type*} {V : ι → Type*}

/-- Cartesian adjacency on tuples. An edge changes one coordinate along a factor edge
and fixes every other coordinate. -/
def boxPi (G : (i : ι) → SimpleGraph (V i)) : SimpleGraph ((i : ι) → V i) where
  Adj x y := ∃ i, (G i).Adj (x i) (y i) ∧ ∀ j, j ≠ i → x j = y j
  symm.symm _ _ := by
    rintro ⟨i, h, heq⟩
    exact ⟨i, h.symm, fun j hj => (heq j hj).symm⟩
  loopless.irrefl _ := by
    rintro ⟨i, h, _⟩
    exact h.ne rfl

variable [Fintype ι]

/-- The sum of the factor edge weights over coordinates whose other entries agree.
This also retains the diagonal weights and edge multiplicities of the factors. -/
noncomputable def piWeight (w : (i : ι) → V i → V i → ℝ) (x y : (i : ι) → V i) : ℝ :=
  ∑ i, if ∀ j, j ≠ i → x j = y j then w i (x i) (y i) else 0

theorem simpleWeight_boxPi (G : (i : ι) → SimpleGraph (V i)) :
    simpleWeight (boxPi G) = piWeight (fun i => simpleWeight (G i)) := by
  funext x y
  by_cases h : (boxPi G).Adj x y
  · rw [simpleWeight, ite_eq_left h, piWeight]
    obtain ⟨i, hadj, heq⟩ := h
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left heq, simpleWeight, ite_eq_left hadj]
    · intro j _ hji
      simp [simpleWeight, heq j hji]
    · simp
  · rw [simpleWeight, ite_eq_right h, piWeight]
    symm
    apply Finset.sum_eq_zero
    intro i _
    by_cases heq : ∀ j, j ≠ i → x j = y j
    · have hn : ¬ (G i).Adj (x i) (y i) := fun ha => h ⟨i, ha, heq⟩
      simp [simpleWeight, hn]
    · simp [heq]

variable [DecidableEq ι]

/-- Separating coordinate `i` identifies the tuple weight with the binary Cartesian weight
of that factor and the product over the remaining coordinates. -/
theorem piWeight_split (w : (j : ι) → V j → V j → ℝ) (i : ι) (x y : (j : ι) → V j) :
    piWeight w x y = cartesianWeight (w i) (piWeight (fun j : {j // j ≠ i} => w j))
      (Equiv.piSplitAt i V x) (Equiv.piSplitAt i V y) := by
  let tail (z : (j : ι) → V j) := fun j : {j // j ≠ i} => z j
  have hi : (∀ j, j ≠ i → x j = y j) ↔ tail x = tail y :=
    ⟨fun h => funext (fun j => h j j.property),
      fun h j hj => congrFun h (⟨j, hj⟩ : {j // j ≠ i})⟩
  have hj (j : {j // j ≠ i}) : (∀ t, t ≠ (j : ι) → x t = y t) ↔
      x i = y i ∧ ∀ t : {t // t ≠ i}, t ≠ j → tail x t = tail y t := by
    constructor
    · intro h
      exact ⟨h i j.property.symm, fun t ht => h t (fun e => ht (Subtype.ext e))⟩
    · rintro ⟨hhead, htail⟩ t hne
      by_cases ht : t = i
      · subst t
        exact hhead
      · exact htail ⟨t, ht⟩ (fun e => hne (congrArg Subtype.val e))
  rw [piWeight, cartesianWeight, Fintype.sum_eq_add_sum_subtype_ne _ i]
  -- The two sums can have different decision procedures for the same coordinate test.
  have term_eq {p q : Prop} {dp : Decidable p} {dq : Decidable q} {a : ℝ} (h : p ↔ q) :
      @ite ℝ p dp a 0 = @ite ℝ q dq a 0 := by
    cases dp <;> cases dq <;> first | rfl | tauto
  apply congrArg₂ (· + ·)
  · exact term_eq hi
  · split
    next hxy =>
      unfold piWeight
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact term_eq ((hj j).trans (and_iff_right hxy))
    next hxy =>
      apply Finset.sum_eq_zero
      intro j _
      split
      next h => exact (hxy ((hj j).mp h).1).elim
      next => rfl

private lemma gapBound_transport {u : A → A → ℝ} {v : B → B → ℝ} (e : A ≃ B)
    (hw : ∀ x y, u x y = v (e x) (e y)) {k : ℝ} (h : GapBound v k) : GapBound u k := by
  intro f hf
  have h0 : ∑ b, f (e.symm b) = 0 := (e.symm.sum_comp f).trans hf
  calc
    k * ∑ a, f a ^ 2 = k * ∑ b, f (e.symm b) ^ 2 := by
      rw [e.symm.sum_comp (fun a => f a ^ 2)]
    _ ≤ energy v (fun b => f (e.symm b)) := h _ h0
    _ = energy u f := by
      unfold energy
      refine Fintype.sum_equiv e.symm _ _ (fun b => ?_)
      refine Fintype.sum_equiv e.symm _ _ (fun c => ?_)
      simp [hw]

private lemma gapBound_congr {u : A → A → ℝ} {v : B → B → ℝ} (e : A ≃ B)
    (hw : ∀ x y, u x y = v (e x) (e y)) (k : ℝ) : GapBound u k ↔ GapBound v k :=
  ⟨gapBound_transport e.symm (fun x y => by simp [hw]), gapBound_transport e hw⟩

variable [∀ i, Fintype (V i)]

/-- The empty tuple is the unique vertex of the nullary product. -/
theorem pi_gap_of_isEmpty [IsEmpty ι] (w : (i : ι) → V i → V i → ℝ) (k : ℝ) :
    GapBound (piWeight w) k := by
  intro f hf
  have hz : f default = 0 := by simpa only [Fintype.sum_unique] using hf
  simp [energy, hz]

theorem pi_no_sharpGap_of_isEmpty [IsEmpty ι] (w : (i : ι) → V i → V i → ℝ) (k : ℝ) :
    ¬ IsSharpGap (piWeight w) k := by
  intro h
  exact (not_lt_of_ge (h.2 (pi_gap_of_isEmpty w (k + 1)))) (lt_add_one k)

/-- For nonempty vertex sets, the bounds on the product are exactly the bounds common to
all factors. The induction splits off any chosen coordinate and applies `cartesian_gap_iff`. -/
theorem pi_gap_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
    [∀ i, Nonempty (V i)] (w : (i : ι) → V i → V i → ℝ)
    (hw : ∀ i x y, 0 ≤ w i x y) (k : ℝ) :
    GapBound (piWeight w) k ↔ ∀ i, GapBound (w i) k := by
  rcases isEmpty_or_nonempty ι with hempty | hι
  · exact iff_of_true (pi_gap_of_isEmpty w k) (fun j => isEmptyElim j)
  · let i : ι := Classical.choice hι
    have htail := pi_gap_iff (ι := {j // j ≠ i}) (V := fun j => V j.val)
        (fun j => w j.val) (fun j => hw j.val) k
    rw [gapBound_congr (Equiv.piSplitAt i V) (piWeight_split w i),
      cartesian_gap_iff (hw i), htail]
    exact ⟨fun ⟨hhead, hrest⟩ j => by
      by_cases hj : j = i
      · subst j
        exact hhead
      · exact hrest ⟨j, hj⟩,
      fun h => ⟨h i, fun j => h j⟩⟩
termination_by Fintype.card ι
decreasing_by exact Fintype.card_subtype_lt (x := i) (not_not_intro rfl)

/-- The minimum of any given factor bounds is a bound on their Cartesian product. -/
theorem pi_gap [Nonempty ι] (w : (i : ι) → V i → V i → ℝ) (hw : ∀ i x y, 0 ≤ w i x y)
    (g : ι → ℝ) (hg : ∀ i, GapBound (w i) (g i)) :
    GapBound (piWeight w) (Finset.univ.inf' Finset.univ_nonempty g) := by
  rcases isEmpty_or_nonempty ((i : ι) → V i) with hempty | hprod
  · intro f _
    simp [energy]
  · let _ : ∀ i, Nonempty (V i) := fun i => hprod.map (fun x => x i)
    exact (pi_gap_iff w hw _).2 fun i => (hg i).mono (Finset.inf'_le g (Finset.mem_univ i))

/-- For a nonempty finite family, the largest product bound is the least sharp factor gap. -/
theorem pi_gap_sharp [Nonempty ι] [∀ i, Nonempty (V i)] (w : (i : ι) → V i → V i → ℝ)
    (hw : ∀ i x y, 0 ≤ w i x y) (g : ι → ℝ) (hg : ∀ i, IsSharpGap (w i) (g i)) :
    IsSharpGap (piWeight w) (Finset.univ.inf' Finset.univ_nonempty g) := by
  refine ⟨pi_gap w hw g (fun i => (hg i).1), ?_⟩
  intro t ht
  have h := (pi_gap_iff w hw t).1 ht
  exact Finset.le_inf' _ _ (fun i _ => (hg i).2 (h i))

/-- A real number bounds the simple graph product exactly when it bounds each factor. -/
theorem boxPi_gap_iff [∀ i, Nonempty (V i)] (G : (i : ι) → SimpleGraph (V i)) (k : ℝ) :
    GapBound (simpleWeight (boxPi G)) k ↔ ∀ i, GapBound (simpleWeight (G i)) k := by
  rw [simpleWeight_boxPi]
  exact pi_gap_iff _ (fun i => simpleWeight_nonneg (G i)) k

/-- Poincaré bounds tensorize on finite Cartesian products of simple graphs. -/
theorem boxPi_gap [Nonempty ι] (G : (i : ι) → SimpleGraph (V i)) (g : ι → ℝ)
    (hg : ∀ i, GapBound (simpleWeight (G i)) (g i)) :
    GapBound (simpleWeight (boxPi G)) (Finset.univ.inf' Finset.univ_nonempty g) := by
  rw [simpleWeight_boxPi]
  exact pi_gap _ (fun i => simpleWeight_nonneg (G i)) g hg

/-- With each undirected edge counted once, the sharp gap of the Cartesian product is
the minimum of all the sharp factor gaps. -/
theorem boxPi_gap_sharp [Nonempty ι] [∀ i, Nonempty (V i)] (G : (i : ι) → SimpleGraph (V i))
    (g : ι → ℝ) (hg : ∀ i, IsSharpGap (simpleWeight (G i)) (g i)) :
    IsSharpGap (simpleWeight (boxPi G)) (Finset.univ.inf' Finset.univ_nonempty g) := by
  rw [simpleWeight_boxPi]
  exact pi_gap_sharp _ (fun i => simpleWeight_nonneg (G i)) g hg

end FiniteProduct

end CartesianGraphProduct

namespace RingGrid

open RingDecay (gap)

variable {m n : ℕ} [NeZero m] [NeZero n]

/-- The energy of `f` on the grid of two rings: squared steps along both rings. -/
noncomputable def energy (f : ZMod m × ZMod n → ℝ) : ℝ :=
  ∑ p : ZMod m × ZMod n, ((f (p.1 + 1, p.2) - f p) ^ 2 + (f (p.1, p.2 + 1) - f p) ^ 2)

/-- The mean of row `i`. -/
noncomputable def rowMean (f : ZMod m × ZMod n → ℝ) (i : ZMod m) : ℝ := (∑ j, f (i, j)) / n

omit [NeZero m] in
/-- A constant plus a sum-zero row: `∑ⱼ (a + x j)² = n a² + ∑ⱼ x j²`. -/
lemma sum_sq_add_of_sum_zero (a : ℝ) (x : ZMod n → ℝ) (hx : ∑ j, x j = 0) :
    ∑ j, (a + x j) ^ 2 = n * a ^ 2 + ∑ j, x j ^ 2 := by
  have h : ∀ j, (a + x j) ^ 2 = a ^ 2 + 2 * a * x j + x j ^ 2 := fun j => by ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, hx, Finset.sum_const,
    Finset.card_univ, ZMod.card, nsmul_eq_mul]
  ring

omit [NeZero m] in
/-- Each row minus its mean has sum zero. -/
lemma row_sub_mean (f : ZMod m × ZMod n → ℝ) (i : ZMod m) :
    ∑ j, (f (i, j) - rowMean f i) = 0 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    rowMean]
  field_simp
  ring

/-- If `f` has sum zero, so do its row means. -/
lemma sum_rowMean (f : ZMod m × ZMod n → ℝ) (hf : ∑ p, f p = 0) : ∑ i, rowMean f i = 0 := by
  rw [Fintype.sum_prod_type] at hf
  simp only [rowMean, ← Finset.sum_div, hf, zero_div]

/-- `∑ f² = n ∑ c² + ∑ g²`, with `c` the row means and `g = f - c`. -/
lemma sum_sq_split (f : ZMod m × ZMod n → ℝ) :
    ∑ p, f p ^ 2 = n * ∑ i, rowMean f i ^ 2 + ∑ p, (f p - rowMean f p.1) ^ 2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h := sum_sq_add_of_sum_zero (rowMean f i) (fun j => f (i, j) - rowMean f i)
    (row_sub_mean f i)
  simp only [add_sub_cancel] at h
  exact h

/-- Steps along the first ring split the same way: `n ∑ (c (i+1) - c i)²` plus the steps of `g`. -/
lemma first_steps_split (f : ZMod m × ZMod n → ℝ) :
    ∑ p : ZMod m × ZMod n, (f (p.1 + 1, p.2) - f p) ^ 2
      = n * ∑ i, (rowMean f (i + 1) - rowMean f i) ^ 2
        + ∑ p : ZMod m × ZMod n,
          ((f (p.1 + 1, p.2) - rowMean f (p.1 + 1)) - (f p - rowMean f p.1)) ^ 2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hx : ∑ j, ((f (i + 1, j) - rowMean f (i + 1)) - (f (i, j) - rowMean f i)) = 0 := by
    rw [Finset.sum_sub_distrib, row_sub_mean, row_sub_mean, sub_zero]
  have h := sum_sq_add_of_sum_zero (rowMean f (i + 1) - rowMean f i) _ hx
  rw [← h]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- Steps along the second ring, row by row, by the cycle Wirtinger inequality. -/
lemma second_steps_ge (f : ZMod m × ZMod n → ℝ) :
    gap n * ∑ p, (f p - rowMean f p.1) ^ 2
      ≤ ∑ p : ZMod m × ZMod n, (f (p.1, p.2 + 1) - f p) ^ 2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h := CycleWirtinger.wirtinger (fun j => f (i, j) - rowMean f i) (row_sub_mean f i)
  simp only [sub_sub_sub_cancel_right] at h
  exact h

/-- For the ordered-pair energy, each of the two orientations has half weight.
At modulus two the two ring steps have the same endpoints and both count. -/
noncomputable def ringWeight {n : ℕ} [NeZero n] (x y : ZMod n) : ℝ := Unify.ringW x y / 2

omit [NeZero m] in
private lemma ringWeight_nonneg (x y : ZMod n) : 0 ≤ ringWeight x y := by
  unfold ringWeight Unify.ringW
  split_ifs <;> norm_num

omit [NeZero m] in
lemma ringWeight_energy (f : ZMod n → ℝ) :
    Unify.energy ringWeight f = ∑ j, (f (j + 1) - f j) ^ 2 := by
  calc
    Unify.energy ringWeight f = Unify.energy Unify.ringW f / 2 := by
      simp only [Unify.energy, ringWeight, Finset.sum_div, div_mul_eq_mul_div]
    _ = _ := by rw [Unify.ring_energy]; ring

omit [NeZero m] in
private lemma ring_gapBound : CartesianGraphProduct.GapBound (ringWeight (n := n)) (gap n) := by
  intro f hf
  rw [ringWeight_energy]
  exact CycleWirtinger.wirtinger f hf

/-- The torus energy agrees with the weighted Cartesian product energy for every positive
modulus, including one and two. -/
theorem energy_eq_cartesian (f : ZMod m × ZMod n → ℝ) :
    energy f = Unify.energy (CartesianGraphProduct.cartesianWeight
      (ringWeight (n := m)) (ringWeight (n := n))) f := by
  rw [CartesianGraphProduct.energy_cartesian]
  simp only [energy, Fintype.sum_prod_type, Finset.sum_add_distrib, ringWeight_energy]
  rw [Finset.sum_comm (f := fun i j => (f (i + 1, j) - f (i, j)) ^ 2)]

/-- **The grid of two rings has gap at least the smaller ring gap.** For `f` with sum zero,
`min (gap m) (gap n) * ∑ f² ≤ energy f`. -/
theorem grid_gap (f : ZMod m × ZMod n → ℝ) (hf : ∑ p, f p = 0) :
    min (gap m) (gap n) * ∑ p, f p ^ 2 ≤ energy f := by
  rw [energy_eq_cartesian]
  exact CartesianGraphProduct.cartesian_gap ringWeight_nonneg
    (ring_gapBound (n := m)) (ring_gapBound (n := n)) f hf

/-! ## The constant is attained -/

omit [NeZero m] in
/-- For `n ≥ 2`, the wave `w j = cos (2π j/n)` on one ring has mean zero and meets the ring gap
with equality: `∑ (w (j+1) - w j)² = gap n * ∑ w²`. -/
lemma ring_wave (hn : 2 ≤ n) :
    ∑ j : ZMod n, Real.cos (2 * π * j.val / n) = 0 ∧
    ∑ j : ZMod n, (Real.cos (2 * π * (j + 1).val / n) - Real.cos (2 * π * j.val / n)) ^ 2
      = gap n * ∑ j : ZMod n, Real.cos (2 * π * j.val / n) ^ 2 := by
  have : Fact (1 < n) := ⟨by omega⟩
  set w : ZMod n → ℝ := fun j => Real.cos (2 * π * j.val / n) with hw
  have hre : ∀ j : ZMod n, w j = (ZMod.stdAddChar j).re := by
    intro j
    rw [hw]
    simp only
    rw [CycleWirtinger.e_eq_exp, Complex.exp_ofReal_mul_I_re]
  constructor
  · change ∑ j, w j = 0
    simp only [hre]
    rw [← Complex.re_sum]
    have h1 := CycleWirtinger.ortho (n := n) 1
    simp only [one_ne_zero, ↓reduceIte, mul_one] at h1
    rw [h1, Complex.zero_re]
  · change ∑ j, (w (j + 1) - w j) ^ 2 = gap n * ∑ j, w j ^ 2
    have hstep := congrFun (RingDecay.heatStep_wave hn 1)
    have hnb : ∀ j, w (j + 1) + w (j - 1) = (2 - gap n) * w j := by
      intro j
      have := hstep j
      simp only [RingDecay.heatStep, one_mul] at this
      change w j + (w (j + 1) - 2 * w j + w (j - 1)) = (1 - gap n) * w j at this
      linarith
    have hshift1 : ∑ j, w (j + 1) ^ 2 = ∑ j, w j ^ 2 :=
      RingDecay.sum_shift_add (fun j => w j ^ 2) 1
    have hshift2 : ∑ j, w j * w (j - 1) = ∑ j, w (j + 1) * w j := by
      have := RingDecay.sum_shift_add (fun j => w j * w (j - 1)) 1
      simp only [add_sub_cancel_right] at this
      exact this.symm
    have hsum : ∑ j, w j * (w (j + 1) + w (j - 1)) = (2 - gap n) * ∑ j, w j ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [hnb j]; ring)
    have hsplit : ∑ j, w j * (w (j + 1) + w (j - 1))
        = ∑ j, w (j + 1) * w j + ∑ j, w j * w (j - 1) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hexp : ∑ j, (w (j + 1) - w j) ^ 2
        = ∑ j, w (j + 1) ^ 2 + ∑ j, w j ^ 2 - 2 * ∑ j, w (j + 1) * w j := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hexp, hshift1]
    rw [hsplit, hshift2] at hsum
    linarith

/-- The wave along the first ring: `cos (2π i/m)`, the same on every row. -/
noncomputable def rowWave (p : ZMod m × ZMod n) : ℝ := Real.cos (2 * π * p.1.val / m)

/-- The wave along the second ring: `cos (2π j/n)`, the same on every column. -/
noncomputable def colWave (p : ZMod m × ZMod n) : ℝ := Real.cos (2 * π * p.2.val / n)

/-- **The wave along the first ring is sharp.** For `m ≥ 2` it has sum zero and
`energy = gap m * ∑ rowWave²`. -/
theorem rowWave_sharp (hm : 2 ≤ m) :
    ∑ p, (rowWave : ZMod m × ZMod n → ℝ) p = 0 ∧
    energy (rowWave : ZMod m × ZMod n → ℝ) = gap m * ∑ p, (rowWave : ZMod m × ZMod n → ℝ) p ^ 2 := by
  obtain ⟨h0, h1⟩ := ring_wave (n := m) hm
  constructor
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [rowWave, h0, Finset.sum_const_zero]
  · rw [energy, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm,
      Finset.sum_comm (f := fun x y => (rowWave (x, y) : ℝ) ^ 2), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [rowWave, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero]
    exact h1

/-- **The wave along the second ring is sharp.** For `n ≥ 2` it has sum zero and
`energy = gap n * ∑ colWave²`. -/
theorem colWave_sharp (hn : 2 ≤ n) :
    ∑ p, (colWave : ZMod m × ZMod n → ℝ) p = 0 ∧
    energy (colWave : ZMod m × ZMod n → ℝ) = gap n * ∑ p, (colWave : ZMod m × ZMod n → ℝ) p ^ 2 := by
  obtain ⟨h0, h1⟩ := ring_wave (n := n) hn
  constructor
  · rw [Fintype.sum_prod_type]
    simp only [colWave, h0, Finset.sum_const_zero]
  · rw [energy, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [colWave, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_add]
    exact h1

/-- **The constant `min (gap m) (gap n)` cannot be improved.** For `m, n ≥ 2` there is a
nonzero `f` with sum zero and `energy f = min (gap m) (gap n) * ∑ f²`: the wave along the slower
ring. -/
theorem grid_gap_sharp (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ f : ZMod m × ZMod n → ℝ, ∑ p, f p = 0 ∧ f (0, 0) = 1 ∧
      energy f = min (gap m) (gap n) * ∑ p, f p ^ 2 := by
  rcases le_total (gap m) (gap n) with h | h
  · refine ⟨rowWave, (rowWave_sharp hm).1, by simp [rowWave], ?_⟩
    rw [min_eq_left h]
    exact (rowWave_sharp hm).2
  · refine ⟨colWave, (colWave_sharp hn).1, by simp [colWave], ?_⟩
    rw [min_eq_right h]
    exact (colWave_sharp hn).2

omit [NeZero m] in
/-- The cosine wave attains the optimal bound for the weighted ring with its original
step multiplicities. -/
theorem ring_isSharpGap (hn : 2 ≤ n) :
    CartesianGraphProduct.IsSharpGap (ringWeight (n := n)) (gap n) := by
  refine ⟨ring_gapBound, ?_⟩
  intro k hk
  let w (j : ZMod n) := Real.cos (2 * π * j.val / n)
  obtain ⟨hzero, heq⟩ := ring_wave hn
  have htest := hk w hzero
  have hmass : 0 < ∑ j, w j ^ 2 := by
    calc
      0 < w 0 ^ 2 := by simp [w]
      _ ≤ ∑ j, w j ^ 2 := Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ 0)
  rw [ringWeight_energy, heq] at htest
  exact le_of_mul_le_mul_right htest hmass

open scoped Classical in
/-- On a finite-dimensional periodic grid, the sharp gap is the smallest ring gap.
Each period is at least two, so every factor has a nonzero mean-zero cosine wave. -/
theorem torus_gap_sharp {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (period : ι → ℕ)
    [∀ i, NeZero (period i)] (hperiod : ∀ i, 2 ≤ period i) :
    CartesianGraphProduct.IsSharpGap
      (CartesianGraphProduct.piWeight (fun i => ringWeight (n := period i)))
      (Finset.univ.inf' Finset.univ_nonempty (fun i => gap (period i))) :=
  CartesianGraphProduct.pi_gap_sharp _ (fun i => ringWeight_nonneg (n := period i)) _
    (fun i => ring_isSharpGap (hperiod i))

/-! ## The heat flow on the grid

`lap f` is `4 f` minus the four neighbors (with wrap), and one heat step with step size `τ` is
`f ↦ f - τ * lap f`. The route needs no two-direction Fourier transform: the step keeps the sum,
`∑ next² = ∑ f² - 2τ · energy f + τ² ∑ (lap f)²` (`sum_sq_heatStep`), one Cauchy–Schwarz line
gives `∑ (lap f)² ≤ 8 · energy f` (`sum_lap_sq_le`), and `grid_gap` finishes. -/

/-- `4 f` minus the four neighbors on the grid of two rings. -/
noncomputable def lap (f : ZMod m × ZMod n → ℝ) (p : ZMod m × ZMod n) : ℝ :=
  4 * f p - f (p.1 + 1, p.2) - f (p.1 - 1, p.2) - f (p.1, p.2 + 1) - f (p.1, p.2 - 1)

/-- One heat step on the grid with step size `τ`. -/
noncomputable def heatStep (τ : ℝ) (f : ZMod m × ZMod n → ℝ) (p : ZMod m × ZMod n) : ℝ :=
  f p - τ * lap f p

/-- The mean of `f` over the grid. -/
noncomputable def mean (f : ZMod m × ZMod n → ℝ) : ℝ := (∑ p, f p) / (m * n)

/-- Shifting along the first ring does not change a sum. -/
lemma sum_shift_fst (F : ZMod m × ZMod n → ℝ) (a : ZMod m) :
    ∑ p : ZMod m × ZMod n, F (p.1 + a, p.2) = ∑ p, F p :=
  Fintype.sum_equiv ((Equiv.addRight a).prodCongr (Equiv.refl _)) _ _ (fun _ => rfl)

/-- Shifting along the second ring does not change a sum. -/
lemma sum_shift_snd (F : ZMod m × ZMod n → ℝ) (b : ZMod n) :
    ∑ p : ZMod m × ZMod n, F (p.1, p.2 + b) = ∑ p, F p :=
  Fintype.sum_equiv ((Equiv.refl _).prodCongr (Equiv.addRight b)) _ _ (fun _ => rfl)

lemma sum_lap (f : ZMod m × ZMod n → ℝ) : ∑ p, lap f p = 0 := by
  have h1 := sum_shift_fst f 1
  have h2 := sum_shift_fst f (-1)
  have h3 := sum_shift_snd f 1
  have h4 := sum_shift_snd f (-1)
  simp only [← sub_eq_add_neg] at h2 h4
  simp only [lap, Finset.sum_sub_distrib, ← Finset.mul_sum, h1, h2, h3, h4]
  ring

/-- **One heat step keeps the sum**, and so the mean. -/
theorem sum_heatStep (τ : ℝ) (f : ZMod m × ZMod n → ℝ) : ∑ p, heatStep τ f p = ∑ p, f p := by
  simp only [heatStep, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_lap, mul_zero, sub_zero]

theorem mean_heatStep (τ : ℝ) (f : ZMod m × ZMod n → ℝ) : mean (heatStep τ f) = mean f := by
  rw [mean, mean, sum_heatStep]

/-- `∑ f · lap f = energy f`. -/
lemma sum_mul_lap (f : ZMod m × ZMod n → ℝ) : ∑ p, f p * lap f p = energy f := by
  have hA := sum_shift_fst (fun p => f p ^ 2) 1
  have hB := sum_shift_snd (fun p => f p ^ 2) 1
  have hC := sum_shift_fst (fun p => f p * f (p.1 - 1, p.2)) 1
  have hD := sum_shift_snd (fun p => f p * f (p.1, p.2 - 1)) 1
  simp only [add_sub_cancel_right, Prod.mk.eta] at hA hB hC hD
  have hL : ∑ p, f p * lap f p = 4 * ∑ p, f p ^ 2 - ∑ p, f p * f (p.1 + 1, p.2)
      - ∑ p, f p * f (p.1 - 1, p.2) - ∑ p, f p * f (p.1, p.2 + 1)
      - ∑ p, f p * f (p.1, p.2 - 1) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun p _ => by simp only [lap]; ring)
  have hE : energy f = ∑ p : ZMod m × ZMod n, f (p.1 + 1, p.2) ^ 2
      + ∑ p : ZMod m × ZMod n, f (p.1, p.2 + 1) ^ 2
      + 2 * ∑ p, f p ^ 2 - 2 * ∑ p : ZMod m × ZMod n, f (p.1 + 1, p.2) * f p
      - 2 * ∑ p : ZMod m × ZMod n, f (p.1, p.2 + 1) * f p := by
    simp only [energy, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have hX : ∑ p : ZMod m × ZMod n, f p * f (p.1 + 1, p.2)
      = ∑ p : ZMod m × ZMod n, f (p.1 + 1, p.2) * f p :=
    Finset.sum_congr rfl (fun p _ => mul_comm _ _)
  have hY : ∑ p : ZMod m × ZMod n, f p * f (p.1, p.2 + 1)
      = ∑ p : ZMod m × ZMod n, f (p.1, p.2 + 1) * f p :=
    Finset.sum_congr rfl (fun p _ => mul_comm _ _)
  rw [hL, hE, hA, hB, ← hC, ← hD, hX, hY]
  ring

/-- **Cauchy–Schwarz: each point has 4 neighbors**, so `∑ (lap f)² ≤ 8 · energy f`. -/
lemma sum_lap_sq_le (f : ZMod m × ZMod n → ℝ) : ∑ p, lap f p ^ 2 ≤ 8 * energy f := by
  have hpt : ∀ p : ZMod m × ZMod n, lap f p ^ 2
      ≤ 4 * ((f (p.1 + 1, p.2) - f p) ^ 2 + (f p - f (p.1 - 1, p.2)) ^ 2
        + (f (p.1, p.2 + 1) - f p) ^ 2 + (f p - f (p.1, p.2 - 1)) ^ 2) := by
    intro p
    have e : lap f p = (f p - f (p.1 + 1, p.2)) + (f p - f (p.1 - 1, p.2))
        + (f p - f (p.1, p.2 + 1)) + (f p - f (p.1, p.2 - 1)) := by simp only [lap]; ring
    rw [e]
    set a := f p - f (p.1 + 1, p.2)
    set b := f p - f (p.1 - 1, p.2)
    set c := f p - f (p.1, p.2 + 1)
    set d := f p - f (p.1, p.2 - 1)
    have ha : (f (p.1 + 1, p.2) - f p) ^ 2 = a ^ 2 := by ring
    have hc : (f (p.1, p.2 + 1) - f p) ^ 2 = c ^ 2 := by ring
    rw [ha, hc]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
      sq_nonneg (b - d), sq_nonneg (c - d)]
  have hb := sum_shift_fst (fun p => (f p - f (p.1 - 1, p.2)) ^ 2) 1
  have hd := sum_shift_snd (fun p => (f p - f (p.1, p.2 - 1)) ^ 2) 1
  simp only [add_sub_cancel_right, Prod.mk.eta] at hb hd
  calc ∑ p, lap f p ^ 2
      ≤ ∑ p : ZMod m × ZMod n, 4 * ((f (p.1 + 1, p.2) - f p) ^ 2 + (f p - f (p.1 - 1, p.2)) ^ 2
        + (f (p.1, p.2 + 1) - f p) ^ 2 + (f p - f (p.1, p.2 - 1)) ^ 2) :=
        Finset.sum_le_sum (fun p _ => hpt p)
    _ = 8 * energy f := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib, energy]
        rw [← hb, ← hd]
        ring

/-- **The size after one step:** `∑ next² = ∑ f² - 2τ · energy f + τ² ∑ (lap f)²`. -/
theorem sum_sq_heatStep (τ : ℝ) (f : ZMod m × ZMod n → ℝ) :
    ∑ p, heatStep τ f p ^ 2 = ∑ p, f p ^ 2 - 2 * τ * energy f + τ ^ 2 * ∑ p, lap f p ^ 2 := by
  rw [← sum_mul_lap, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun p _ => by simp only [heatStep]; ring)

/-- After one step, `∑ next² ≤ ∑ f² - 2τ(1 - 4τ) · energy f`. -/
theorem sum_sq_heatStep_le (τ : ℝ) (f : ZMod m × ZMod n → ℝ) :
    ∑ p, heatStep τ f p ^ 2 ≤ ∑ p, f p ^ 2 - 2 * τ * (1 - 4 * τ) * energy f := by
  rw [sum_sq_heatStep]
  nlinarith [sum_lap_sq_le f, sq_nonneg τ]

/-- **One step, mean zero.** For `0 ≤ τ ≤ 1/4`,
`∑ next² ≤ (1 - 2τ(1 - 4τ) · min (gap m) (gap n)) · ∑ f²`. -/
theorem heatStep_decay (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 4) (f : ZMod m × ZMod n → ℝ)
    (hf : ∑ p, f p = 0) :
    ∑ p, heatStep τ f p ^ 2 ≤ (1 - 2 * τ * (1 - 4 * τ) * min (gap m) (gap n)) * ∑ p, f p ^ 2 := by
  have h1 := sum_sq_heatStep_le τ f
  have h2 := grid_gap f hf
  have hk : 0 ≤ 2 * τ * (1 - 4 * τ) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 hk]

/-- **At `τ = 1/8`** each step shrinks the squared size by a factor of at least
`1 - min (gap m) (gap n) / 8`. -/
theorem heatStep_decay_eighth (f : ZMod m × ZMod n → ℝ) (hf : ∑ p, f p = 0) :
    ∑ p, heatStep (1 / 8) f p ^ 2 ≤ (1 - min (gap m) (gap n) / 8) * ∑ p, f p ^ 2 := by
  have h := heatStep_decay (1 / 8) (by norm_num) (by norm_num) f hf
  have e : (1 : ℝ) - 2 * (1 / 8) * (1 - 4 * (1 / 8)) * min (gap m) (gap n)
      = 1 - min (gap m) (gap n) / 8 := by ring
  rwa [e] at h

omit [NeZero m] [NeZero n] in
lemma heatStep_sub_const (τ c : ℝ) (f : ZMod m × ZMod n → ℝ) (p : ZMod m × ZMod n) :
    heatStep τ (fun q => f q - c) p = heatStep τ f p - c := by
  simp only [heatStep, lap]
  ring

lemma sum_sub_mean (f : ZMod m × ZMod n → ℝ) : ∑ p, (f p - mean f) = 0 := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card,
    ZMod.card, nsmul_eq_mul, mean]
  push_cast
  field_simp
  ring

/-- **One step, any data.** The uneven part `f - mean f` shrinks by the same factor. -/
theorem heatStep_decay_mean (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 4) (f : ZMod m × ZMod n → ℝ) :
    ∑ p, (heatStep τ f p - mean (heatStep τ f)) ^ 2
      ≤ (1 - 2 * τ * (1 - 4 * τ) * min (gap m) (gap n)) * ∑ p, (f p - mean f) ^ 2 := by
  have h := heatStep_decay τ hτ0 hτ (fun q => f q - mean f) (sum_sub_mean f)
  simp only [heatStep_sub_const] at h
  rw [mean_heatStep]
  exact h

theorem mean_iterate (τ : ℝ) (f : ZMod m × ZMod n → ℝ) (k : ℕ) :
    mean ((heatStep τ)^[k] f) = mean f := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', mean_heatStep, ih]

omit [NeZero m] [NeZero n] in
/-- The factor `1 - 2τ(1 - 4τ) · min (gap m) (gap n)` is at least `1/2`. -/
lemma factor_nonneg (τ : ℝ) :
    0 ≤ 1 - 2 * τ * (1 - 4 * τ) * min (gap m) (gap n) := by
  have hg4 : min (gap m) (gap n) ≤ 4 := (min_le_left _ _).trans (RingDecay.gap_le_four m)
  have hg0 : 0 ≤ min (gap m) (gap n) := by
    refine le_min ?_ ?_ <;> rw [RingDecay.gap_eq_four_sin_sq] <;> positivity
  have hk : 2 * τ * (1 - 4 * τ) ≤ 1 / 8 := by nlinarith [sq_nonneg (4 * τ - 1 / 2)]
  have := mul_le_mul_of_nonneg_right hk hg0
  linarith

/-- **After `k` steps** the uneven part is at most the factor to the power `k` times its start. -/
theorem iterate_decay (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 4) (f : ZMod m × ZMod n → ℝ)
    (k : ℕ) :
    ∑ p, ((heatStep τ)^[k] f p - mean f) ^ 2
      ≤ (1 - 2 * τ * (1 - 4 * τ) * min (gap m) (gap n)) ^ k * ∑ p, (f p - mean f) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := heatStep_decay_mean τ hτ0 hτ ((heatStep τ)^[k] f)
    rw [mean_heatStep, mean_iterate] at h
    calc ∑ p, (heatStep τ ((heatStep τ)^[k] f) p - mean f) ^ 2
        ≤ (1 - 2 * τ * (1 - 4 * τ) * min (gap m) (gap n))
            * ∑ p, ((heatStep τ)^[k] f p - mean f) ^ 2 := h
      _ ≤ (1 - 2 * τ * (1 - 4 * τ) * min (gap m) (gap n))
            * ((1 - 2 * τ * (1 - 4 * τ) * min (gap m) (gap n)) ^ k
              * ∑ p, (f p - mean f) ^ 2) :=
          mul_le_mul_of_nonneg_left ih (factor_nonneg τ)
      _ = (1 - 2 * τ * (1 - 4 * τ) * min (gap m) (gap n)) ^ (k + 1)
            * ∑ p, (f p - mean f) ^ 2 := by ring

omit [NeZero m] [NeZero n] in
/-- For `m, n ≥ 2` and `0 < τ < 1/4` the factor is strictly below one. -/
lemma factor_lt_one (hm : 2 ≤ m) (hn : 2 ≤ n) (τ : ℝ) (hτ0 : 0 < τ) (hτ : τ < 1 / 4) :
    1 - 2 * τ * (1 - 4 * τ) * min (gap m) (gap n) < 1 := by
  have hg : 0 < min (gap m) (gap n) := lt_min (RingDecay.gap_pos hm) (RingDecay.gap_pos hn)
  have hk : 0 < 2 * τ * (1 - 4 * τ) := by nlinarith
  nlinarith [mul_pos hk hg]

/-- **The uneven part goes to zero** for `m, n ≥ 2` and `0 < τ < 1/4`. -/
theorem energy_tendsto_zero (hm : 2 ≤ m) (hn : 2 ≤ n) (τ : ℝ) (hτ0 : 0 < τ) (hτ : τ < 1 / 4)
    (f : ZMod m × ZMod n → ℝ) :
    Filter.Tendsto (fun k => ∑ p, ((heatStep τ)^[k] f p - mean f) ^ 2)
      Filter.atTop (nhds 0) := by
  have h0 := factor_nonneg (m := m) (n := n) τ
  have h1 := factor_lt_one hm hn τ hτ0 hτ
  have hlim : Filter.Tendsto (fun k : ℕ => (1 - 2 * τ * (1 - 4 * τ) * min (gap m) (gap n)) ^ k
      * ∑ p, (f p - mean f) ^ 2) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const
      (∑ p, (f p - mean f) ^ 2)
  refine squeeze_zero (fun k => ?_) (fun k => iterate_decay τ hτ0.le hτ.le f k) hlim
  exact Finset.sum_nonneg (fun p _ => sq_nonneg _)

/-- **Every value settles to the mean** for `m, n ≥ 2` and `0 < τ < 1/4`. -/
theorem iterate_tendsto_mean (hm : 2 ≤ m) (hn : 2 ≤ n) (τ : ℝ) (hτ0 : 0 < τ) (hτ : τ < 1 / 4)
    (f : ZMod m × ZMod n → ℝ) (p : ZMod m × ZMod n) :
    Filter.Tendsto (fun k => (heatStep τ)^[k] f p) Filter.atTop (nhds (mean f)) := by
  have hE := energy_tendsto_zero hm hn τ hτ0 hτ f
  have hsq : Filter.Tendsto (fun k => ((heatStep τ)^[k] f p - mean f) ^ 2)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun k => sq_nonneg _) (fun k => ?_) hE
    exact Finset.single_le_sum (f := fun q => ((heatStep τ)^[k] f q - mean f) ^ 2)
      (fun q _ => sq_nonneg _) (Finset.mem_univ p)
  have habs : Filter.Tendsto (fun k => |(heatStep τ)^[k] f p - mean f|)
      Filter.atTop (nhds 0) := by
    have := hsq.sqrt
    simpa [Real.sqrt_sq_eq_abs] using this
  have hd : Filter.Tendsto (fun k => (heatStep τ)^[k] f p - mean f) Filter.atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  simpa using hd.add_const (mean f)

end RingGrid
