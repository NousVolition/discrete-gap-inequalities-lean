import LeechSignVectors

namespace LeechMinimal

open LeechSignVectors Finset

abbrev FourParams := (s : {s : Finset (Fin 24) // s.card = 2}) × (s.val → Bool)
abbrev FourVectors := {x : Vec // FourShape x}

def fourMap (p : FourParams) : FourVectors :=
  ⟨signedVector 4 p.1.val p.2, signedVector_values _ _ _,
    by rw [signedVector_support (by norm_num), p.1.property]⟩

theorem fourMap_bijective : Function.Bijective fourMap := by
  constructor
  · rintro ⟨⟨s, hs⟩, a⟩ ⟨⟨t, ht⟩, b⟩ h
    have hv := congrArg Subtype.val h
    change signedVector 4 s a = signedVector 4 t b at hv
    have hst := congrArg support hv
    rw [signedVector_support (by norm_num), signedVector_support (by norm_num)] at hst
    subst t
    have hab := signedVector_injective (by norm_num : (0 : ℤ) < 4) s hv
    subst b
    rfl
  · rintro ⟨x, hx⟩
    refine ⟨⟨⟨support x, hx.2⟩, signsOf x⟩, ?_⟩
    apply Subtype.ext
    exact signedVector_recover (by norm_num) x hx.1

noncomputable def fourEquiv : FourParams ≃ FourVectors :=
  Equiv.ofBijective fourMap fourMap_bijective

noncomputable instance : Fintype FourVectors := Fintype.ofEquiv FourParams fourEquiv

theorem card_four_params : Fintype.card FourParams = Nat.choose 24 2 * 2 ^ 2 := by
  rw [Fintype.card_sigma]
  have hc : ∀ s : {s : Finset (Fin 24) // s.card = 2},
      Fintype.card (s.val → Bool) = 2 ^ 2 := by
    intro s
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, s.property]
  simp_rw [hc]
  rw [sum_const, card_univ, Fintype.card_finset_len]
  simp

theorem card_four : Fintype.card FourVectors = 1104 := by
  rw [← Fintype.card_congr fourEquiv, card_four_params]
  decide

end LeechMinimal
