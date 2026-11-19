import PlaygroundGolay
import LeechKissing

/-! # Existing Leech results in the playground's coordinates

The lattice condition is unchanged except for using the playground's code.
The coordinate permutation transfers the already proved lattice results.
This file does not formalize browser execution or floating-point projections.
-/
namespace PlaygroundLeech

open PlaygroundGolay LeechLattice LeechMinimal Finset

def InPlayLeech (x : Vec) : Prop :=
  ∃ m : ℤ, (m = 0 ∨ m = 1) ∧ (∀ i, x i % 2 = m) ∧ (∑ i, x i) % 8 = 4 * m ∧
    ∀ k : ℤ, IsPlayWord (residueSet x k)

def vectorEquiv : Vec ≃ Vec where
  toFun := toLean
  invFun := toPlay
  left_inv := toPlay_toLean
  right_inv := toLean_toPlay

theorem sum_toLean (x : Vec) : ∑ i, toLean x i = ∑ i, x i := by
  apply Fintype.sum_equiv coordinateEquiv.symm
  intro i; rfl

theorem norm_toLean (x : Vec) : normSq (toLean x) = normSq x := by
  apply Fintype.sum_equiv coordinateEquiv.symm
  intro i; rfl

theorem residue_toLean (x : Vec) (k : ℤ) :
    residueSet (toLean x) k = toLean (residueSet x k) := rfl

theorem lattice_correspondence (x : Vec) : InPlayLeech x ↔ InLeech (toLean x) := by
  constructor
  · rintro ⟨m, hm, hp, hs, hc⟩
    refine ⟨m, hm, fun i => hp _, ?_, ?_⟩
    · rwa [sum_toLean]
    · intro k; exact (code_correspondence _).1 (hc k)
  · rintro ⟨m, hm, hp, hs, hc⟩
    refine ⟨m, hm, ?_, ?_, ?_⟩
    · intro i; simpa [toLean] using hp (coordinateEquiv i)
    · rwa [sum_toLean] at hs
    · intro k; exact (code_correspondence _).2 (hc k)

theorem toLean_ne_zero {x : Vec} : toLean x ≠ 0 ↔ x ≠ 0 := by
  have h : toLean x = 0 ↔ x = 0 := by
    constructor
    · intro he
      funext i
      simpa [toLean] using congrFun he (coordinateEquiv i)
    · rintro rfl; rfl
  exact not_congr h

/-- Transfers the existing lower bound; no new minimum-length argument is needed. -/
theorem play_norm_ge_32 (x : Vec) (hx : InPlayLeech x) (h0 : x ≠ 0) :
    32 ≤ normSq x := by
  rw [← norm_toLean]
  exact leech_norm_ge_32 (toLean x) ((lattice_correspondence x).1 hx)
    (toLean_ne_zero.2 h0)

def IsPlayShortest (x : Vec) : Prop :=
  InPlayLeech x ∧ x ≠ 0 ∧ ∀ y : Vec, InPlayLeech y → y ≠ 0 → normSq x ≤ normSq y

theorem shortest_correspondence (x : Vec) :
    IsPlayShortest x ↔ IsShortest (toLean x) := by
  constructor
  · rintro ⟨hx, h0, hmin⟩
    refine ⟨(lattice_correspondence x).1 hx, toLean_ne_zero.2 h0, ?_⟩
    intro y hy hy0
    have hp : InPlayLeech (toPlay y) := (lattice_correspondence _).2 (by
      simpa only [toLean_toPlay] using hy)
    have hp0 : toPlay y ≠ 0 := toLean_ne_zero.1 (by
      simpa only [toLean_toPlay] using hy0)
    have hn := hmin (toPlay y) hp hp0
    have hny : normSq (toPlay y) = normSq y := by
      simpa only [toLean_toPlay] using (norm_toLean (toPlay y)).symm
    simpa only [norm_toLean, hny] using hn
  · rintro ⟨hx, h0, hmin⟩
    refine ⟨(lattice_correspondence x).2 hx, toLean_ne_zero.1 h0, ?_⟩
    intro y hy hy0
    simpa only [norm_toLean] using
      hmin (toLean y) ((lattice_correspondence y).1 hy) (toLean_ne_zero.2 hy0)

theorem play_shortest_iff_norm32 (x : Vec) :
    IsPlayShortest x ↔ InPlayLeech x ∧ normSq x = 32 := by
  rw [shortest_correspondence, shortest_iff_norm32, norm_toLean, ← lattice_correspondence]

/-- Classification is transferred through the explicit coordinate permutation. -/
theorem play_minimal_iff (x : Vec) : InPlayLeech x ∧ normSq x = 32 ↔
    FourShape (toLean x) ∨ OctadShape (toLean x) ∨ OddShape (toLean x) := by
  rw [lattice_correspondence, ← norm_toLean x, minimal_iff]

abbrev PlayShortestVectors := {x : Vec // IsPlayShortest x}

noncomputable def shortestEquiv : PlayShortestVectors ≃ ShortestVectors :=
  Equiv.subtypeEquiv vectorEquiv shortest_correspondence

noncomputable instance : Fintype PlayShortestVectors :=
  Fintype.ofEquiv ShortestVectors shortestEquiv.symm

/-- The playground-code lattice has the same 196,560 shortest vectors, relabeled. -/
theorem card_play_shortest_vectors : Fintype.card PlayShortestVectors = 196560 := by
  rw [Fintype.card_congr shortestEquiv, card_shortest_vectors]

end PlaygroundLeech
