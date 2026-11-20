import Mathlib

/-!
# Light bounce and capture

This file models the super-black grain (catalog entry `1`) on playground tab 34 and the
capture rule on tabs 16, 27 and 28.

* **Almost no light comes back.** For nonnegative incoming light and a reflected share
  `0 ≤ ε ≤ 0.00035`, at most `0.00035` of the input comes back (`reflected_le_cap`).
  This cap is a parameter of the light model.
* **Nothing goes missing.** The absorbed and reflected light add up to the input at one
  hit. At every later bounce, the light absorbed so far plus the remainder still adds up
  to the input (`absorbed_sum_add_remainder`). For a fixed share the remainder is
  `ε ^ n · I` after `n` bounces (`remainder_eq`). For an allowed share it tends to zero.
* **Once in, never out.** If a step keeps a set inside itself, a state starting in the
  set stays there at every later step (`once_in_never_out`). Both rules keep a state
  inside once it enters. A grain keeps its material and stays at or below its starting
  row. A ray captured at a fixed horizon stays captured.

## How the rules match the playground

* **Grain motion.** In `updateGrid`, a super-black grain stays put, falls one row, or
  slides one column while falling. Rows are processed from the bottom up. A moving grain
  takes its material label into an empty cell. Only this material needs to satisfy
  `GrainMove` in the row theorems.
* **Drawing.** Each starting color channel is capped at `12`. Red and green add an
  integer jitter from `0` to `5`. Blue adds half that jitter, rounded down. On a grain of
  another material, each super-black neighbor reduces the color multiplier by `0.18`
  before integer rounding. The light split `ε · I` and `(1 - ε) · I` is modeled separately.
* **Capture.** With a fixed radius `r_s`, tabs 16 and 28 check after moving. Tab 16
  includes the edge (`≤ r_s`). Tab 28 excludes it (`< r_s`) and uses center `(0,0)`.
  Tab 27 checks `≤ 0.96 r_s` before moving. The ray model leaves inactive states in place.
-/

namespace LightBounceAndCapture

open Filter Topology

/-! ## Reflected and absorbed light -/

/-- The light model caps the reflected share at `0.00035`. -/
noncomputable def capShare : ℝ := 0.00035

/-- A reflect share is allowed when `0 ≤ ε ≤ 0.00035`. -/
def AllowedShare (ε : ℝ) : Prop := 0 ≤ ε ∧ ε ≤ capShare

/-- Light sent back by one hit: the share `ε` of the incoming light `I`. -/
def reflected (ε I : ℝ) : ℝ := ε * I

/-- Light taken in by one hit: the rest, `(1 - ε) · I`. -/
def absorbed (ε I : ℝ) : ℝ := (1 - ε) * I

/-- An allowed share is strictly below `1`. -/
theorem AllowedShare.lt_one {ε : ℝ} (h : AllowedShare ε) : ε < 1 := by
  have := h.2; unfold capShare at this; linarith

/-- The defining equality also gives an upper bound on reflected light. -/
theorem reflected_le {ε I : ℝ} (_hε : AllowedShare ε) : reflected ε I ≤ ε * I :=
  le_of_eq rfl

/-- **Almost no light comes back.** With an allowed share and nonnegative input, the reflected
light is between `0` and `0.00035` times the incoming light. -/
theorem reflected_le_cap {ε I : ℝ} (hε : AllowedShare ε) (hI : 0 ≤ I) :
    0 ≤ reflected ε I ∧ reflected ε I ≤ capShare * I :=
  ⟨mul_nonneg hε.1 hI, mul_le_mul_of_nonneg_right hε.2 hI⟩

/-- With an allowed share and nonnegative incoming light, at least `1 - 0.00035` of the
light is taken in. -/
theorem absorbed_ge {ε I : ℝ} (hε : AllowedShare ε) (hI : 0 ≤ I) :
    (1 - capShare) * I ≤ absorbed ε I := by
  unfold absorbed
  exact mul_le_mul_of_nonneg_right (by linarith [hε.2]) hI

/-- **Nothing goes missing.** The incoming light equals the absorbed light plus the
reflected light. -/
theorem incoming_eq_absorbed_add_reflected (ε I : ℝ) :
    I = absorbed ε I + reflected ε I := by
  unfold absorbed reflected; ring

/-- Light still bouncing after `n` bounces: each bounce keeps only the reflected part. -/
def remainder (ε I : ℝ) : ℕ → ℝ
  | 0 => I
  | n + 1 => reflected ε (remainder ε I n)

/-- The light still bouncing after `n` bounces is exactly `ε ^ n · I`. -/
theorem remainder_eq (ε I : ℝ) (n : ℕ) : remainder ε I n = ε ^ n * I := by
  induction n with
  | zero => simp [remainder]
  | succ n ih => simp only [remainder, reflected, ih]; ring

/-- The remainder formula also gives an upper bound after `n` bounces. -/
theorem remainder_le (ε I : ℝ) (n : ℕ) : remainder ε I n ≤ ε ^ n * I :=
  le_of_eq (remainder_eq ε I n)

/-- **Bouncing dies out (limit).** With an allowed share, the light still bouncing tends
to `0`. -/
theorem remainder_tendsto_zero {ε : ℝ} (hε : AllowedShare ε) (I : ℝ) :
    Tendsto (remainder ε I) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hε.1 hε.lt_one).mul_const I
  rw [zero_mul] at h
  simpa only [funext (remainder_eq ε I)] using h

/-- **Nothing goes missing, over many bounces.** The light absorbed in the first `n`
bounces plus the light still bouncing equals the incoming light. -/
theorem absorbed_sum_add_remainder (ε I : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, absorbed ε (remainder ε I k)) + remainder ε I n = I := by
  induction n with
  | zero => simp [remainder]
  | succ n ih =>
    have h1 : remainder ε I (n + 1) = ε * remainder ε I n := rfl
    rw [Finset.sum_range_succ, h1]
    unfold absorbed at ih ⊢
    linear_combination ih

/-- Over all bounces, the light absorbed tends to the whole incoming light. -/
theorem absorbed_sum_tendsto {ε : ℝ} (hε : AllowedShare ε) (I : ℝ) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, absorbed ε (remainder ε I k)) atTop (𝓝 I) := by
  have h := (tendsto_const_nhds (x := I)).sub (remainder_tendsto_zero hε I)
  rw [sub_zero] at h
  refine h.congr (fun n => ?_)
  have := absorbed_sum_add_remainder ε I n
  linarith

/-- **Bouncing dies out, for any bounce sequence.** If the light left after each bounce is
nonnegative and at most `ε` times the light before it, then after `n` bounces it is at most
`ε ^ n` times the start. -/
theorem bounce_le {ε : ℝ} (hε : 0 ≤ ε) {R : ℕ → ℝ}
    (hstep : ∀ n, R (n + 1) ≤ ε * R n) (n : ℕ) : R n ≤ ε ^ n * R 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc R (n + 1) ≤ ε * R n := hstep n
      _ ≤ ε * (ε ^ n * R 0) := mul_le_mul_of_nonneg_left ih hε
      _ = ε ^ (n + 1) * R 0 := by ring

/-- With an allowed share, any such nonnegative bounce sequence tends to `0`. -/
theorem bounce_tendsto_zero {ε : ℝ} (hε : AllowedShare ε) {R : ℕ → ℝ}
    (hnonneg : ∀ n, 0 ≤ R n) (hstep : ∀ n, R (n + 1) ≤ ε * R n) :
    Tendsto R atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hε.1 hε.lt_one).mul_const (R 0)
  rw [zero_mul] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h hnonneg
    (bounce_le hε.1 hstep)

/-! ### Drawing the super-black grain -/

/-- A channel starts at `c` and receives the applied jitter `j` after the cap at `12`. -/
def superBlackChannel (c j : ℕ) : ℕ := min c 12 + j

/-- With applied jitter below `6`, the channel is at most `17` out of `255`. -/
theorem superBlackChannel_le (c : ℕ) {j : ℕ} (hj : j < 6) : superBlackChannel c j ≤ 17 := by
  unfold superBlackChannel; omega

/-- With at most four super-black neighbors, the color multiplier on a grain of another
material lies between `0.28` and `1`, before integer rounding. -/
theorem neighbor_share_bounds {near : ℕ} (h : near ≤ 4) :
    (0.28 : ℝ) ≤ 1 - 0.18 * near ∧ 1 - 0.18 * (near : ℝ) ≤ 1 := by
  have h' : (near : ℝ) ≤ 4 := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ near := Nat.cast_nonneg _
  constructor <;> linarith

/-! ## Once in, never out -/

/-- **Once in, never out.** For any step map `f` and any set `S` that `f` sends into
itself, a state that starts in `S` is in `S` after every number of steps. -/
theorem once_in_never_out {α : Type*} (f : α → α) (S : Set α) (hS : Set.MapsTo f S S)
    {x : α} (hx : x ∈ S) (n : ℕ) : f^[n] x ∈ S :=
  hS.iterate n hx

/-- The same rule when the step may change from frame to frame: if every frame's step sends
`S` into itself, a state that starts in `S` is in `S` after every number of frames. -/
theorem once_in_never_out_frames {α : Type*} (f : ℕ → α → α) (S : Set α)
    (hS : ∀ k, Set.MapsTo (f k) S S) {x : α} (hx : x ∈ S) (n : ℕ) :
    (Nat.rec x (fun k y => f k y) n : α) ∈ S := by
  induction n with
  | zero => exact hx
  | succ n ih => exact hS n ih

/-! ### Grain motion on tab 34 -/

/-- A grain on the tab 34 grid: column `x`, row `y` (rows count downward) and material
index `kind` in the catalog. -/
structure Grain where
  x : ℤ
  y : ℤ
  kind : ℕ
deriving DecidableEq

/-- Catalog index of the super-black grain on tab 34. -/
def superBlackGrainKind : ℕ := 1

/-- Catalog index of Ferrofluids on tab 34. -/
def ferroKind : ℕ := 4

/-- A single modeled move keeps the label. A grain may stay, fall, or slide while falling.
The extra pull move is available to ferrofluid. -/
inductive GrainMove : Grain → Grain → Prop
  | stay (g : Grain) : GrainMove g g
  | fall (x y : ℤ) (k : ℕ) : GrainMove ⟨x, y, k⟩ ⟨x, y + 1, k⟩
  | slide (x y d : ℤ) (k : ℕ) (hd : d = 1 ∨ d = -1) : GrainMove ⟨x, y, k⟩ ⟨x + d, y + 1, k⟩
  | pull (x y dx dy : ℤ) (k : ℕ) (hk : k = ferroKind) (hdx : |dx| ≤ 1) (hdy : |dy| ≤ 1) :
      GrainMove ⟨x, y, k⟩ ⟨x + dx, y + dy, k⟩

/-- Every grain move keeps the material label. -/
theorem GrainMove.kind_eq {g h : Grain} (m : GrainMove g h) : h.kind = g.kind := by
  cases m <;> rfl

/-- In this move relation, a non-ferrofluid grain keeps or increases its row. -/
theorem GrainMove.y_le {g h : Grain} (m : GrainMove g h) (hk : g.kind ≠ ferroKind) :
    g.y ≤ h.y := by
  cases m with
  | stay => exact le_rfl
  | fall => simp
  | slide => simp
  | pull _ _ _ _ _ hk' => exact absurd hk' hk

/-- The set of super-black grains at row `r` or below. -/
def superBlackRegion (r : ℤ) : Set Grain := {g | g.kind = superBlackGrainKind ∧ r ≤ g.y}

/-- If a step follows the move rule for super-black grains, it preserves this set. -/
theorem superBlackRegion_mapsTo (step : Grain → Grain)
    (hstep : ∀ g, g.kind = superBlackGrainKind → GrainMove g (step g))
    (r : ℤ) : Set.MapsTo step (superBlackRegion r) (superBlackRegion r) := by
  intro g ⟨hk, hy⟩
  have hk' : g.kind ≠ ferroKind := by rw [hk]; decide
  have m := hstep g hk
  exact ⟨m.kind_eq.trans hk, hy.trans (m.y_le hk')⟩

/-- A super-black grain starting at row `r` or below keeps its material and stays at or
below that row after any number of steps. -/
theorem super_black_grain_stays_at_or_below (step : Grain → Grain)
    (hstep : ∀ g, g.kind = superBlackGrainKind → GrainMove g (step g))
    (r : ℤ) {g : Grain} (hg : g ∈ superBlackRegion r) (n : ℕ) : step^[n] g ∈ superBlackRegion r :=
  once_in_never_out step (superBlackRegion r) (superBlackRegion_mapsTo step hstep r) hg n

/-- The same holds when each frame uses its own step map, as the page's random slides do. -/
theorem super_black_grain_stays_at_or_below_frames (step : ℕ → Grain → Grain)
    (hstep : ∀ k g, g.kind = superBlackGrainKind → GrainMove g (step k g))
    (r : ℤ) {g : Grain} (hg : g ∈ superBlackRegion r) (n : ℕ) :
    (Nat.rec g (fun k h => step k h) n : Grain) ∈ superBlackRegion r :=
  once_in_never_out_frames step (superBlackRegion r)
    (fun k => superBlackRegion_mapsTo (step k) (hstep k) r) hg n

/-! ### Captured rays and stars at a fixed horizon -/

/-- A ray or star on a Black Hole tab: its position and whether it is still live. -/
structure Ray (P : Type*) where
  pos : P
  alive : Bool

open Classical in
/-- One step on tabs 16 and 28: a live ray moves; if it lands inside the horizon it is
captured, if it lands in the far-away set it is dropped, otherwise it stays live. A ray
that is no longer live is skipped and does not change. -/
noncomputable def rayStep {P : Type*} (move : P → P) (inside gone : Set P) (s : Ray P) :
    Ray P :=
  if s.alive then
    if move s.pos ∈ inside then ⟨move s.pos, false⟩
    else if move s.pos ∈ gone then ⟨move s.pos, false⟩
    else ⟨move s.pos, true⟩
  else s

open Classical in
/-- One step on tab 27: a live ray inside the horizon is captured where it is; otherwise
it moves and stays live. A ray that is no longer live does not change. -/
noncomputable def rayStepCheckFirst {P : Type*} (move : P → P) (inside : Set P) (s : Ray P) :
    Ray P :=
  if s.alive then
    if s.pos ∈ inside then ⟨s.pos, false⟩ else ⟨move s.pos, true⟩
  else s

/-- The captured set: rays that are no longer live and sit inside the horizon. -/
def captured {P : Type*} (inside : Set P) : Set (Ray P) :=
  {s | s.alive = false ∧ s.pos ∈ inside}

/-- A ray that is no longer live is left unchanged by a step. -/
theorem rayStep_of_not_alive {P : Type*} (move : P → P) (inside gone : Set P) {s : Ray P}
    (h : s.alive = false) : rayStep move inside gone s = s := by
  simp [rayStep, h]

/-- The tab 16 and 28 step sends the captured set into itself. -/
theorem captured_mapsTo {P : Type*} (move : P → P) (inside gone : Set P) :
    Set.MapsTo (rayStep move inside gone) (captured inside) (captured inside) := by
  intro s hs
  rw [rayStep_of_not_alive move inside gone hs.1]
  exact hs

/-- **Captured stays captured.** On tabs 16 and 28, a captured ray is captured after every
number of steps. -/
theorem captured_stays_captured {P : Type*} (move : P → P) (inside gone : Set P)
    {s : Ray P} (hs : s ∈ captured inside) (n : ℕ) :
    (rayStep move inside gone)^[n] s ∈ captured inside :=
  once_in_never_out _ _ (captured_mapsTo move inside gone) hs n

/-- A captured ray never moves again: after every number of steps it is the same ray. -/
theorem captured_frozen {P : Type*} (move : P → P) (inside gone : Set P)
    {s : Ray P} (hs : s.alive = false) (n : ℕ) : (rayStep move inside gone)^[n] s = s :=
  Function.iterate_fixed (rayStep_of_not_alive move inside gone hs) n

/-- A live ray whose move lands inside the horizon is captured after the next step and at
every step after that. -/
theorem lands_inside_captured_forever {P : Type*} (move : P → P) (inside gone : Set P)
    {s : Ray P} (ha : s.alive = true) (hin : move s.pos ∈ inside) (n : ℕ) :
    (rayStep move inside gone)^[n + 1] s ∈ captured inside := by
  rw [Function.iterate_succ_apply]
  apply captured_stays_captured
  simp [rayStep, ha, hin, captured]

/-- The tab 27 step sends the captured set into itself. -/
theorem captured_mapsTo_checkFirst {P : Type*} (move : P → P) (inside : Set P) :
    Set.MapsTo (rayStepCheckFirst move inside) (captured inside) (captured inside) := by
  intro s hs
  simpa [rayStepCheckFirst, hs.1] using hs

/-- **Captured stays captured on tab 27.** -/
theorem captured_stays_captured_checkFirst {P : Type*} (move : P → P) (inside : Set P)
    {s : Ray P} (hs : s ∈ captured inside) (n : ℕ) :
    (rayStepCheckFirst move inside)^[n] s ∈ captured inside :=
  once_in_never_out _ _ (captured_mapsTo_checkFirst move inside) hs n

/-! ### Horizon disks with a fixed center and radius -/

/-- Distance in the plane from the hole's center `c`. -/
noncomputable def distFrom (c p : ℝ × ℝ) : ℝ := Real.sqrt ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2)

/-- Inside the horizon, edge included (tab 16 uses `≤ r_s`; tab 27 uses `≤ 0.96 r_s`). -/
def closedHorizon (c : ℝ × ℝ) (R : ℝ) : Set (ℝ × ℝ) := {p | distFrom c p ≤ R}

/-- Inside the horizon, edge excluded (tab 28 uses `< r_s`). -/
def openHorizon (c : ℝ × ℝ) (R : ℝ) : Set (ℝ × ℝ) := {p | distFrom c p < R}

/-- **Tab 16.** A ray captured inside the disk of radius `r_s` stays captured there. -/
theorem tab16_captured_stays (move : ℝ × ℝ → ℝ × ℝ) (gone : Set (ℝ × ℝ)) (c : ℝ × ℝ)
    (rs : ℝ) {s : Ray (ℝ × ℝ)} (hs : s ∈ captured (closedHorizon c rs)) (n : ℕ) :
    distFrom c ((rayStep move (closedHorizon c rs) gone)^[n] s).pos ≤ rs ∧
      ((rayStep move (closedHorizon c rs) gone)^[n] s).alive = false :=
  have h := captured_stays_captured move (closedHorizon c rs) gone hs n
  ⟨h.2, h.1⟩

/-- **Tab 27.** A ray captured inside the disk of radius `0.96 r_s` stays captured there. -/
theorem tab27_captured_stays (move : ℝ × ℝ → ℝ × ℝ) (c : ℝ × ℝ) (rs : ℝ)
    {s : Ray (ℝ × ℝ)} (hs : s ∈ captured (closedHorizon c (0.96 * rs))) (n : ℕ) :
    distFrom c ((rayStepCheckFirst move (closedHorizon c (0.96 * rs)))^[n] s).pos
        ≤ 0.96 * rs ∧
      ((rayStepCheckFirst move (closedHorizon c (0.96 * rs)))^[n] s).alive = false :=
  have h := captured_stays_captured_checkFirst move (closedHorizon c (0.96 * rs)) hs n
  ⟨h.2, h.1⟩

/-- **Tab 28.** A ray that fell inside the open disk of radius `r_s` stays there. -/
theorem tab28_captured_stays (move : ℝ × ℝ → ℝ × ℝ) (gone : Set (ℝ × ℝ)) (rs : ℝ)
    {s : Ray (ℝ × ℝ)} (hs : s ∈ captured (openHorizon (0, 0) rs)) (n : ℕ) :
    distFrom (0, 0) ((rayStep move (openHorizon (0, 0) rs) gone)^[n] s).pos < rs ∧
      ((rayStep move (openHorizon (0, 0) rs) gone)^[n] s).alive = false :=
  have h := captured_stays_captured move (openHorizon (0, 0) rs) gone hs n
  ⟨h.2, h.1⟩

end LightBounceAndCapture
