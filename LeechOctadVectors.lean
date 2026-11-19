import LeechSignVectors
import LeechOctadCount

namespace LeechMinimal

open LeechLattice LeechCodeCounts LeechSignVectors Finset

def codeSupport (w : Fin 24 → Bool) : Finset (Fin 24) := univ.filter (fun i => w i = true)

theorem signed_two_residue (w : Fin 24 → Bool) (b : codeSupport w → Bool) :
    residueSet (signedVector 2 (codeSupport w) b) 2 = w := by
  funext i
  cases hw : w i
  · have hi : i ∉ codeSupport w := by simp [codeSupport, hw]
    simp [residueSet, signedVector, hi]
  · have hi : i ∈ codeSupport w := by simp [codeSupport, hw]
    cases hb : b ⟨i, hi⟩ <;> simp [residueSet, signedVector, hi, hb]

theorem octad_support {x : Vec} (hx : OctadShape x) :
    codeSupport (residueSet x 2) = support x := by
  ext i
  rcases hx.1 i with h | h | h <;> simp [codeSupport, residueSet, support, h]

abbrev OctadParams := (w : Octad) × {b : codeSupport w.val.val → Bool // evenSigns b}
abbrev OctadVectors := {x : Vec // OctadShape x}

def octadMap (p : OctadParams) : OctadVectors :=
  ⟨signedVector 2 (codeSupport p.1.val.val) p.2.val,
    signedVector_values _ _ _,
    by rw [signed_two_residue]; exact p.1.val.property,
    by rw [signedVector_support (by norm_num)]; exact p.1.property,
    by rw [signedVector_negative_card (by norm_num)]; exact p.2.property⟩

theorem octadMap_bijective : Function.Bijective octadMap := by
  constructor
  · rintro ⟨w, a⟩ ⟨v, b⟩ h
    have hv := congrArg Subtype.val h
    change signedVector 2 (codeSupport w.val.val) a.val =
      signedVector 2 (codeSupport v.val.val) b.val at hv
    have hwv : w = v := by
      apply Subtype.ext
      apply Subtype.ext
      simpa only [signed_two_residue] using congrArg (fun x => residueSet x 2) hv
    subst v
    have hab : a = b := Subtype.ext (signedVector_injective (by norm_num) _ hv)
    subst b
    rfl
  · rintro ⟨x, hx⟩
    let w : Octad := ⟨⟨residueSet x 2, hx.2.1⟩, by
      change (codeSupport (residueSet x 2)).card = 8
      rw [octad_support hx, hx.2.2.1]⟩
    let b : codeSupport w.val.val → Bool := fun i => decide (x i < 0)
    have hs : codeSupport w.val.val = support x := octad_support hx
    have hb : signedVector 2 (codeSupport w.val.val) b = x := by
      change signedVector 2 (codeSupport w.val.val) (fun i => decide (x i < 0)) = x
      rw [hs]
      exact signedVector_recover (by norm_num) x hx.1
    have he : evenSigns b := by
      unfold evenSigns
      rw [← signedVector_negative_card (by norm_num : (0 : ℤ) < 2), hb]
      exact hx.2.2.2
    exact ⟨⟨w, ⟨b, he⟩⟩, Subtype.ext hb⟩

noncomputable def octadEquiv : OctadParams ≃ OctadVectors :=
  Equiv.ofBijective octadMap octadMap_bijective

noncomputable instance : Fintype OctadVectors := Fintype.ofEquiv OctadParams octadEquiv

theorem card_octad_params : Fintype.card OctadParams = Fintype.card Octad * 128 := by
  rw [Fintype.card_sigma]
  have hc : ∀ w : Octad, Fintype.card {b : codeSupport w.val.val → Bool // evenSigns b} = 128 := by
    intro w
    apply card_evenSigns_eight
    rw [Fintype.card_coe]
    exact w.property
  simp_rw [hc]
  simp

theorem card_octad_vectors : Fintype.card OctadVectors = 97152 := by
  rw [← Fintype.card_congr octadEquiv, card_octad_params, card_octad]

end LeechMinimal
