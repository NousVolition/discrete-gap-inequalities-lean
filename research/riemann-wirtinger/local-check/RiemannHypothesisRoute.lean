import RiemannZeroGaps

/-!
# What a complete zero count would need to supply

This module keeps the Riemann hypothesis as the research goal. It proves a
conditional counting criterion, without assuming that the needed counts or
complete lists of zeta zeros have been obtained. Multiplicity is unnecessary
for this set-based criterion: every distinct nontrivial zero must be covered.
-/

open Complex

namespace RiemannZeroGaps

/-- A complete family of finite zero lists with full critical-line counts
would establish RH. Completeness is an explicit hypothesis. -/
theorem rh_of_complete_critical_counts (census : ℕ → Finset ℂ)
    (complete : ∀ s : ℂ, NontrivialZero s → ∃ N, s ∈ census N)
    (counts : ∀ N, (census N).card ≤
      ((census N).filter fun s => s.re = 1/2).card) : RiemannHypothesis := by
  classical
  intro s hz htr hpole
  obtain ⟨N, hN⟩ := complete s ⟨hz, htr, hpole⟩
  have heq : (census N).filter (fun z => z.re = 1/2) = census N :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (counts N)
  have hmem : s ∈ (census N).filter (fun z => z.re = 1/2) := by rwa [heq]
  exact (Finset.mem_filter.mp hmem).2

/-- For sound and complete finite lists, matching the critical-line counts
at every stage is equivalent to RH. No such list construction is assumed
to have been carried out by the spacing theorems. -/
theorem rh_iff_complete_critical_counts (census : ℕ → Finset ℂ)
    (sound : ∀ N s, s ∈ census N → NontrivialZero s)
    (complete : ∀ s : ℂ, NontrivialZero s → ∃ N, s ∈ census N) :
    RiemannHypothesis ↔ ∀ N, ((census N).filter fun s => s.re = 1/2).card = (census N).card := by
  classical
  constructor
  · intro hRH N
    have heq : (census N).filter (fun s => s.re = 1/2) = census N := by
      apply Finset.filter_eq_self.mpr
      intro s hs
      have hz := sound N s hs
      exact hRH s hz.1 hz.2.1 hz.2.2
    rw [heq]
  · intro h
    exact rh_of_complete_critical_counts census complete (fun N => (h N).ge)

end RiemannZeroGaps
