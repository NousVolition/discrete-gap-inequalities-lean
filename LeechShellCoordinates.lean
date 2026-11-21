import LeechCoordinateAlphabet
import LeechSymmetry

/-! # Counting Leech lattice vectors by their Golay residue words

The labels record each coordinate's value, its contribution to squared length,
and its contribution to the sum modulo eight. -/
namespace LeechShellCoordinates

open LeechCoordinateAlphabet (Width Labels charge labelFlag)
open LeechLattice LeechMinimal LeechCodeCounts LeechSymmetry LeechNorm48Count Finset

private def value (width : Width) (odd bit : Bool) : Labels width → ℤ :=
  match width with
  | .four => if odd then (if bit then ![7,3,-1,-5] else ![-7,-3,1,5])
             else (if bit then ![-6,-2,2,6] else ![-8,-4,0,4])
  | .five => if odd then (if bit then ![7,3,-1,-5,-9] else ![-7,-3,1,5,9])
            else (if bit then ![-6,-2,2,6,10] else ![-8,-4,0,4,8])
  | .six => if odd then (if bit then ![7,3,-1,-5,-9,11] else ![-7,-3,1,5,9,-11])
            else (if bit then ![-6,-2,2,6,10,-10] else ![-8,-4,0,4,8,12])

private def lower : Width → ℤ
  | .four => -8
  | .five => -9
  | .six => -11

private def upper : Width → ℤ
  | .four => 7
  | .five => 9
  | .six => 12

private def parity (p : Bool) : ℤ := if p then 1 else 0
private def special (p : Bool) : ℤ := if p then 3 else 2
private def total (p : Bool) : ℤ := if p then 4 else 0
private def budget (u : ℤ) (p : Bool) (k : ℕ) : ℤ := if p then u - 3 else u - (k : ℤ) / 2
private def baseEnergy (p b : Bool) : ℤ := if p then 1 else if b then 4 else 0
private def anchor (p b : Bool) : ℤ := if p then (if b then -1 else 1) else (if b then 2 else 0)
private def carry (width : Width) (p b : Bool) (a : (Labels width)) : ℤ := (value width p b a - anchor p b - 4 * labelFlag width a) / 8

private theorem square_rule (width : Width) (p b : Bool) (a : (Labels width)) :
    value width p b a ^ 2 = baseEnergy p b + 8 * charge width p b a := by
  cases width <;> cases p <;> cases b <;> fin_cases a <;> decide

private theorem sum_rule (width : Width) (p b : Bool) (a : (Labels width)) :
    value width p b a = anchor p b + 4 * labelFlag width a + 8 * carry width p b a := by
  cases width <;> cases p <;> cases b <;> fin_cases a <;> decide

private theorem point_parity (width : Width) (p b : Bool) (a : (Labels width)) : value width p b a % 2 = parity p := by
  cases width <;> cases p <;> cases b <;> fin_cases a <;> decide

private theorem point_bit (width : Width) (p b : Bool) (a : (Labels width)) :
    decide (value width p b a % 4 = special p % 4) = b := by
  cases width <;> cases p <;> cases b <;> fin_cases a <;> decide

private theorem value_inj (width : Width) (p b : Bool) : Function.Injective (value width p b) := by
  intro a c h
  cases width <;> cases p <;> cases b <;> fin_cases a <;> fin_cases c <;> (first | rfl | contradiction)

private theorem value_covers (width : Width) (p : Bool) (x : ℤ) (hp : x % 2 = parity p) (hlo : lower width ≤ x) (hhi : x ≤ upper width) :
    ∃ a : (Labels width), value width p (decide (x % 4 = special p % 4)) a = x := by
  cases width <;> cases p <;> simp only [lower, upper] at hlo hhi <;> interval_cases x <;> norm_num [parity] at hp <;> decide

private def coords (width : Width) (p : Bool) (w : Fin 24 → Bool) (a : Fin 24 → (Labels width)) : Vec :=
  fun i => value width p (w i) (a i)

private theorem coords_residue (width : Width) (p w a) : residueSet (coords width p w a) (special p) = w := by
  funext i; exact point_bit width _ _ _

private theorem bits_weight (w : Fin 24 → Bool) : LeechCoordinateTally.bits w true = weight w := by
  simp [LeechCoordinateTally.bits, weight, sum_boole]

private theorem zeros_ones (w : Fin 24 → Bool) : LeechCoordinateTally.bits w false + LeechCoordinateTally.bits w true = 24 := by
  rw [LeechCoordinateTally.bits, LeechCoordinateTally.bits, ← sum_add_distrib]
  have hi (i : Fin 24) : (if w i = false then 1 else 0) + (if w i = true then 1 else 0) = (1 : ℕ) := by
    cases w i <;> decide
  simp [hi]

private theorem count_ones (w : Fin 24 → Bool) :
    (∑ i, if w i = true then (1 : ℤ) else 0) = (weight w : ℤ) := by
  simp [sum_boole, weight]

private theorem energy_sum (p : Bool) (w : Fin 24 → Bool) :
    ∑ i, baseEnergy p (w i) = (if p then 24 else 4 * (weight w : ℤ)) := by
  cases p with
  | true => simp [baseEnergy]
  | false =>
    have hi (i : Fin 24) : baseEnergy false (w i) = 4 * (if w i = true then 1 else 0) := by
      cases w i <;> decide
    simp only [hi, ← mul_sum, count_ones, Bool.false_eq_true, ite_false]

private theorem anchor_sum (p : Bool) (w : Fin 24 → Bool) :
    ∑ i, anchor p (w i) = (if p then 24 - 2 * (weight w : ℤ) else 2 * (weight w : ℤ)) := by
  cases p with
  | false =>
    have hi (i : Fin 24) : anchor false (w i) = 2 * (if w i = true then 1 else 0) := by
      cases w i <;> decide
    simp only [hi, ← mul_sum, count_ones, Bool.false_eq_true, ite_false]
  | true =>
    have hi (i : Fin 24) : anchor true (w i) = 1 - 2 * (if w i = true then 1 else 0) := by
      cases w i <;> decide
    simp only [hi, sum_sub_distrib, ← mul_sum, count_ones, ite_true]
    simp

private theorem constraints (width : Width) (u : ℤ) (p : Bool) (w : Codeword) (a : Fin 24 → (Labels width)) :
    (normSq (coords width p w.val a) = 8 * u ∧ (∑ i, coords width p w.val a i) % 8 = total p) ↔
    ((∑ i, charge width p (w.val i) (a i)) = budget u p (weight w.val) ∧
     (∑ i, labelFlag width (a i)) % 2 = parity p % 2) := by
  have h4 : weight w.val % 4 = 0 := golay_weight_mod_four w.property
  have he : normSq (coords width p w.val a) =
      (if p then 24 else 4 * (weight w.val : ℤ)) + 8 * ∑ i, charge width p (w.val i) (a i) := by
    simp only [normSq, coords, square_rule, sum_add_distrib, ← mul_sum, energy_sum]
  have hs : (∑ i, coords width p w.val a i) =
      (if p then 24 - 2 * (weight w.val : ℤ) else 2 * (weight w.val : ℤ)) +
        4 * (∑ i, labelFlag width (a i)) + 8 * ∑ i, carry width p (w.val i) (a i) := by
    unfold coords
    rw [sum_congr rfl (fun i _ => sum_rule width p (w.val i) (a i))]
    simp only [sum_add_distrib, ← mul_sum, anchor_sum]
  rw [he, hs]
  cases p <;> simp only [budget, parity, total, Bool.false_eq_true, ite_false, ite_true] <;> omega

private abbrev Shell (u : ℤ) := {x : Lattice // normSq x.val = 8 * u}
private abbrev Params (width : Width) (u : ℤ) := Σ p : Bool, Σ w : Codeword, LeechCoordinateTally.Picks (charge width p) (labelFlag width) w.val (budget u p (weight w.val)) (parity p)

private def pack (width : Width) (u : ℤ) : Params width u → Shell u := fun ⟨p,w,a⟩ =>
  ⟨⟨coords width p w.val a.val, by
    apply (inLeech_iff _).2
    have hs := ((constraints width u p w a.val).2 a.property).2
    have hp (i : Fin 24) : coords width p w.val a.val i % 2 = parity p := point_parity width _ _ _
    have hw : IsGolayWord (residueSet (coords width p w.val a.val) (special p)) :=
      (coords_residue width p w.val a.val).symm ▸ w.property
    cases p with
    | false => exact Or.inl ⟨hp,hs,hw⟩
    | true => exact Or.inr ⟨hp,hs,hw⟩⟩, ((constraints width u p w a.val).2 a.property).1⟩

private theorem pack_injective (width : Width) (u : ℤ) : Function.Injective (pack width u) := by
  rintro ⟨p,w,a⟩ ⟨q,v,b⟩ h
  have hx : coords width p w.val a.val = coords width q v.val b.val :=
    congrArg (fun x : Shell u => x.val.val) h
  have hp : parity p = parity q := (point_parity width p (w.val 0) (a.val 0)).symm.trans
    ((congrArg (fun x : Vec => x 0 % 2) hx).trans (point_parity width q (v.val 0) (b.val 0)))
  have he : p = q := by cases p <;> cases q <;> first | rfl | contradiction
  subst q
  have hw : w = v := Subtype.ext ((coords_residue width p w.val a.val).symm.trans
    ((congrArg (fun x => residueSet x (special p)) hx).trans (coords_residue width p v.val b.val)))
  subst v
  have ha : a = b := Subtype.ext (funext (fun i => value_inj width p (w.val i) (congrFun hx i)))
  subst b; rfl

private theorem pack_covers (width : Width) (u : ℤ) (x : Shell u)
    (bound : ∀ i, lower width ≤ x.val.val i ∧ x.val.val i ≤ upper width) : ∃ a, pack width u a = x := by
  obtain ⟨p, hp, hs, hw⟩ : ∃ p : Bool, (∀ i, x.val.val i % 2 = parity p) ∧
      (∑ i, x.val.val i) % 8 = total p ∧ IsGolayWord (residueSet x.val.val (special p)) := by
    rcases (inLeech_iff x.val.val).1 x.val.property with he | ho
    · exact ⟨false, he⟩
    · exact ⟨true, ho⟩
  let w : Codeword := ⟨residueSet x.val.val (special p), hw⟩
  have hh (i : Fin 24) : ∃ a : (Labels width), value width p (w.val i) a = x.val.val i := by
    exact value_covers width p _ (hp i) (bound i).1 (bound i).2
  choose a ha using hh
  have he : coords width p w.val a = x.val.val := funext ha
  have hcond := (constraints width u p w a).1 (by rw [he]; exact ⟨x.property,hs⟩)
  exact ⟨⟨p,w,a,hcond⟩, Subtype.ext (Subtype.ext he)⟩

private theorem card_params (width : Width) (u : ℤ) : Nat.card (Params width u) =
      ∑ p : Bool, ∑ w : Codeword, LeechCoordinateAlphabet.tally width p (24 - weight w.val) (weight w.val)
        (if p then u - 3 else u - (weight w.val : ℤ) / 2) (if p then 1 else 0) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp_rw [Fintype.card_sigma, LeechCoordinateTally.card_picks]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro w _
  have h := zeros_ones w.val
  rw [bits_weight] at h ⊢
  rw [show LeechCoordinateTally.bits w.val false = 24 - weight w.val by omega]
  rfl

/-- Count a shell by its Golay words when all coordinates in the shell lie between −7 and 7. -/
theorem card_vectors_from_choices (u : ℤ)
    (bound : ∀ x : Lattice, normSq x.val = 8 * u → ∀ i, -7 ≤ x.val i ∧ x.val i ≤ 7) :
    Nat.card {x : Lattice // normSq x.val = 8 * u} =
      ∑ p : Bool, ∑ w : Codeword, tally p (24 - weight w.val) (weight w.val)
        (if p then u - 3 else u - (weight w.val : ℤ) / 2) (if p then 1 else 0) := by
  have onto : Function.Surjective (pack .four u) := fun x => pack_covers .four u x fun i => by
    have h := bound x.val x.property i
    change -8 ≤ x.val.val i ∧ x.val.val i ≤ 7
    omega
  exact (Nat.card_congr (Equiv.ofBijective (pack .four u) ⟨pack_injective .four u, onto⟩)).symm.trans (card_params .four u)

/-- Count the part of a shell whose coordinates all lie from −8 to 7. -/
theorem card_box_from_choices (u : ℤ) :
    Nat.card {x : {v : Lattice // normSq v.val = 8 * u} //
      ∀ i, -8 ≤ x.val.val i ∧ x.val.val i ≤ 7} =
      ∑ p : Bool, ∑ w : Codeword, tally p (24 - weight w.val) (weight w.val)
        (if p then u - 3 else u - (weight w.val : ℤ) / 2) (if p then 1 else 0) := by
  let box := {x : Shell u // ∀ i, -8 ≤ x.val.val i ∧ x.val.val i ≤ 7}
  let f : Params .four u → box := fun a => ⟨pack .four u a, fun i => by
    obtain ⟨p,w,v⟩ := a
    change -8 ≤ value .four p (w.val i) (v.val i) ∧ value .four p (w.val i) (v.val i) ≤ 7
    generalize w.val i = b
    generalize v.val i = j
    cases p <;> cases b <;> fin_cases j <;> decide⟩
  have bij : Function.Bijective f := by
    constructor
    · intro a b h
      exact pack_injective .four u (congrArg Subtype.val h)
    · intro x
      obtain ⟨a,ha⟩ := pack_covers .four u x.val x.property
      exact ⟨a, Subtype.ext ha⟩
  exact (Nat.card_congr (Equiv.ofBijective f bij)).symm.trans (card_params .four u)

/-- Count a shell with five choices per residue when every coordinate lies from −9 to 9. -/
theorem card_vectors_five_choices (u : ℤ)
    (bound : ∀ x : Lattice, normSq x.val = 8 * u → ∀ i, -9 ≤ x.val i ∧ x.val i ≤ 9) :
    Nat.card {x : Lattice // normSq x.val = 8 * u} =
      ∑ p : Bool, ∑ w : Codeword, LeechCoordinateChoices.tally true p (24 - weight w.val) (weight w.val)
        (if p then u - 3 else u - (weight w.val : ℤ) / 2) (if p then 1 else 0) := by
  have onto : Function.Surjective (pack .five u) := fun x =>
    pack_covers .five u x (bound x.val x.property)
  exact (Nat.card_congr (Equiv.ofBijective (pack .five u) ⟨pack_injective .five u, onto⟩)).symm.trans
    (card_params .five u)

/-- Count a shell with six choices per residue over the full coordinate range from −11 to 12. -/
theorem card_vectors_in_six_choice_range (u : ℤ)
    (bound : ∀ x : Lattice, normSq x.val = 8 * u → ∀ i, -11 ≤ x.val i ∧ x.val i ≤ 12) :
    Nat.card {x : Lattice // normSq x.val = 8 * u} =
      ∑ p : Bool, ∑ w : Codeword, LeechCoordinateAlphabet.tally .six p (24 - weight w.val) (weight w.val)
        (if p then u - 3 else u - (weight w.val : ℤ) / 2) (if p then 1 else 0) := by
  have onto : Function.Surjective (pack .six u) := fun x =>
    pack_covers .six u x (bound x.val x.property)
  exact (Nat.card_congr (Equiv.ofBijective (pack .six u) ⟨pack_injective .six u, onto⟩)).symm.trans
    (card_params .six u)

/-- Count a shell with six choices per residue when each coordinate lies from −10 to 10. -/
theorem card_vectors_six_choices (u : ℤ)
    (bound : ∀ x : Lattice, normSq x.val = 8 * u → ∀ i, -10 ≤ x.val i ∧ x.val i ≤ 10) :
    Nat.card {x : Lattice // normSq x.val = 8 * u} =
      ∑ p : Bool, ∑ w : Codeword, LeechCoordinateAlphabet.tally .six p (24 - weight w.val) (weight w.val)
        (if p then u - 3 else u - (weight w.val : ℤ) / 2) (if p then 1 else 0) := by
  apply card_vectors_in_six_choice_range
  intro x hx i
  have := bound x hx i
  omega

end LeechShellCoordinates
