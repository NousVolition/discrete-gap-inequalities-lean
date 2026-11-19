import LeechMinimal
import LeechCodeCounts

namespace LeechMinimal

open LeechLattice LeechCodeCounts

abbrev OddParams := Codeword × Fin 24
abbrev OddVectors := {x : Vec // OddShape x}

def oddMap (p : OddParams) : OddVectors :=
  ⟨oddVector p.1.val p.2, p.1.val, p.1.property, p.2, rfl⟩

theorem oddVector_injective {w v : Fin 24 → Bool} {j k : Fin 24}
    (h : oddVector w j = oddVector v k) : w = v ∧ j = k := by
  have hw : w = v := by
    simpa only [oddVector_residue] using congrArg (fun x => residueSet x 3) h
  refine ⟨hw, ?_⟩
  subst v
  by_contra hjk
  have hj := congrFun h j
  cases hb : w j <;> simp [oddVector, hjk, hb] at hj

theorem oddMap_bijective : Function.Bijective oddMap := by
  constructor
  · intro p q h
    have hp := oddVector_injective (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext hp.1) hp.2
  · rintro ⟨x, w, hw, j, rfl⟩
    exact ⟨(⟨w, hw⟩, j), rfl⟩

noncomputable def oddEquiv : OddParams ≃ OddVectors :=
  Equiv.ofBijective oddMap oddMap_bijective

noncomputable instance : Fintype OddVectors := Fintype.ofEquiv OddParams oddEquiv

theorem card_odd : Fintype.card OddVectors = 98304 := by
  rw [← Fintype.card_congr oddEquiv, Fintype.card_prod, card_codeword, Fintype.card_fin]

end LeechMinimal
