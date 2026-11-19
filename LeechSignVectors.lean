import LeechMinimal
import E8PlumbingBridge

/-! Sign assignments on a prescribed support, including the even-sign count. -/
namespace LeechSignVectors

open LeechMinimal Finset

def signedVector (q : ℤ) (s : Finset (Fin 24)) (b : s → Bool) : Vec :=
  fun i => if hi : i ∈ s then (if b ⟨i, hi⟩ then -q else q) else 0

theorem signedVector_values (q : ℤ) (s : Finset (Fin 24)) (b : s → Bool) :
    ∀ i, signedVector q s b i = 0 ∨ signedVector q s b i = q ∨
      signedVector q s b i = -q := by
  intro i
  by_cases hi : i ∈ s
  · cases hb : b ⟨i, hi⟩ <;> simp [signedVector, hi, hb]
  · simp [signedVector, hi]

theorem signedVector_support {q : ℤ} (hq : q ≠ 0)
    (s : Finset (Fin 24)) (b : s → Bool) : support (signedVector q s b) = s := by
  ext i
  by_cases hi : i ∈ s
  · cases hb : b ⟨i, hi⟩ <;> simp [support, signedVector, hi, hb, hq]
  · simp [support, signedVector, hi]

def signsOf (x : Vec) : support x → Bool := fun i => decide (x i < 0)

theorem signedVector_recover {q : ℤ} (hq : 0 < q) (x : Vec)
    (hx : ∀ i, x i = 0 ∨ x i = q ∨ x i = -q) :
    signedVector q (support x) (signsOf x) = x := by
  funext i
  rcases hx i with h | h | h <;>
    simp [signedVector, support, signsOf, h, hq.ne', hq, not_lt_of_ge hq.le]

theorem signedVector_injective {q : ℤ} (hq : 0 < q) (s : Finset (Fin 24)) :
    Function.Injective (signedVector q s) := by
  intro a b h
  funext i
  have hi := congrFun h i.val
  cases ha : a i <;> cases hb : b i <;>
    simp [signedVector, i.property, ha, hb] at hi ⊢ <;> omega

theorem signedVector_negative_card {q : ℤ} (hq : 0 < q)
    (s : Finset (Fin 24)) (b : s → Bool) :
    (negatives (signedVector q s b)).card = (univ.filter (fun i : s => b i = true)).card := by
  have hi : ∀ i, signedVector q s b i < 0 ↔ ∃ h : i ∈ s, b ⟨i, h⟩ = true := by
    intro i
    by_cases h : i ∈ s
    · cases hb : b ⟨i, h⟩ <;> simp [signedVector, h, hb, hq, not_lt_of_ge hq.le]
    · simp [signedVector, h]
  change (univ.filter (fun i => signedVector q s b i < 0)).card = _
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  apply Fintype.card_congr
  refine {
    toFun := fun i => ⟨⟨i.val, ((hi i.val).1 i.property).choose⟩,
      ((hi i.val).1 i.property).choose_spec⟩
    invFun := fun i => ⟨i.val.val, (hi _).2 ⟨i.val.property, i.property⟩⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro i; rfl
  · intro i; rfl

def evenSigns {α : Type*} [Fintype α] (b : α → Bool) : Prop :=
  (univ.filter (fun i => b i = true)).card % 2 = 0

noncomputable instance {α : Type*} [Fintype α] : Fintype {b : α → Bool // evenSigns b} :=
  Fintype.ofFinite _

theorem evenSigns_precomp {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (b : β → Bool) : evenSigns (b ∘ e) ↔ evenSigns b := by
  classical
  unfold evenSigns
  have h : (univ.filter (fun i : α => b (e i) = true)).card =
      (univ.filter (fun i : β => b i = true)).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl))
  simp only [Function.comp_apply]
  rw [h]

noncomputable def evenSignsEquiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) : {b : α → Bool // evenSigns b} ≃ {b : β → Bool // evenSigns b} where
  toFun b := ⟨b.val ∘ e.symm, (evenSigns_precomp e.symm b.val).2 b.property⟩
  invFun b := ⟨b.val ∘ e, (evenSigns_precomp e b.val).2 b.property⟩
  left_inv b := by ext i; simp
  right_inv b := by ext i; simp

set_option maxRecDepth 4096 in
theorem card_evenSigns_eight {α : Type*} [Fintype α] (h : Fintype.card α = 8) :
    Fintype.card {b : α → Bool // evenSigns b} = 128 := by
  classical
  let e : α ≃ Fin 8 := Fintype.equivFinOfCardEq h
  rw [Fintype.card_congr (evenSignsEquiv e), Fintype.card_subtype]
  have hs : (univ.filter (fun b : Fin 8 → Bool => evenSigns b)) =
      univ.filter (fun b : Fin 8 → Bool => E8PlumbingBridge.isEvenParity b = true) := by
    apply Finset.filter_congr
    intro b _
    simp only [evenSigns, E8PlumbingBridge.isEvenParity, beq_iff_eq]
  rw [hs]
  exact E8PlumbingBridge.card_spinor_roots

end LeechSignVectors
