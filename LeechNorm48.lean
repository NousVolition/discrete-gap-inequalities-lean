import LeechNorm48Count
import LeechDodecadCount
import LeechSymmetry

/-! # The squared-length-48 shell of the Leech lattice

The residue word and coordinate parity determine four possible labels per
coordinate. The squared-length and sum conditions select the admissible label
assignments. Squared length 48 here is 6 in the usual normalization. -/
namespace LeechNorm48

open LeechLattice LeechMinimal LeechCodeCounts LeechSymmetry LeechNorm48Count Finset

private def value (odd bit : Bool) : Label → ℤ :=
  if odd then (if bit then ![7,3,-1,-5] else ![-7,-3,1,5])
  else (if bit then ![-6,-2,2,6] else ![-8,-4,0,4])

private def parity (p : Bool) : ℤ := if p then 1 else 0
private def special (p : Bool) : ℤ := if p then 3 else 2
private def total (p : Bool) : ℤ := if p then 4 else 0
private def budget (p : Bool) (k : ℕ) : ℤ := if p then 3 else 6 - (k : ℤ) / 2
private def baseEnergy (p b : Bool) : ℤ := if p then 1 else if b then 4 else 0
private def anchor (p b : Bool) : ℤ := if p then (if b then -1 else 1) else (if b then 2 else 0)
private def carry (p b : Bool) (a : Label) : ℤ := (value p b a - anchor p b - 4 * flag a) / 8

private theorem square_rule (p b : Bool) (a : Label) :
    value p b a ^ 2 = baseEnergy p b + 8 * cost p b a := by
  cases p <;> cases b <;> fin_cases a <;> decide

private theorem sum_rule (p b : Bool) (a : Label) :
    value p b a = anchor p b + 4 * flag a + 8 * carry p b a := by
  cases p <;> cases b <;> fin_cases a <;> decide

private theorem point_parity (p b : Bool) (a : Label) : value p b a % 2 = parity p := by
  cases p <;> cases b <;> fin_cases a <;> decide

private theorem point_bit (p b : Bool) (a : Label) :
    decide (value p b a % 4 = special p % 4) = b := by
  cases p <;> cases b <;> fin_cases a <;> decide

private theorem value_inj (p b : Bool) : Function.Injective (value p b) := by
  intro a c h
  cases p <;> cases b <;> fin_cases a <;> fin_cases c <;> (first | rfl | contradiction)

private theorem value_covers (p : Bool) (x : ℤ) (hp : x % 2 = parity p) (hn : x^2 ≤ 48) :
    ∃ a : Label, value p (decide (x % 4 = special p % 4)) a = x := by
  have hlo : -6 ≤ x := by by_contra! h; nlinarith
  have hhi : x ≤ 6 := by by_contra! h; nlinarith
  cases p <;> interval_cases x <;> norm_num [parity] at hp <;> decide

private def coords (p : Bool) (w : Fin 24 → Bool) (a : Fin 24 → Label) : Vec :=
  fun i => value p (w i) (a i)

private theorem coords_residue (p w a) : residueSet (coords p w a) (special p) = w := by
  funext i; exact point_bit _ _ _

private theorem bits_weight (w : Fin 24 → Bool) : bits w true = weight w := by
  simp [bits, weight, sum_boole]

private theorem zeros_ones (w : Fin 24 → Bool) : bits w false + bits w true = 24 := by
  rw [bits, bits, ← sum_add_distrib]
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

private theorem constraints (p : Bool) (w : Codeword) (a : Fin 24 → Label) :
    (normSq (coords p w.val a) = 48 ∧ (∑ i, coords p w.val a i) % 8 = total p) ↔
    ((∑ i, cost p (w.val i) (a i)) = budget p (weight w.val) ∧
     (∑ i, flag (a i)) % 2 = parity p % 2) := by
  have h4 : weight w.val % 4 = 0 := golay_weight_mod_four w.property
  have he : normSq (coords p w.val a) =
      (if p then 24 else 4 * (weight w.val : ℤ)) + 8 * ∑ i, cost p (w.val i) (a i) := by
    simp only [normSq, coords, square_rule, sum_add_distrib, ← mul_sum, energy_sum]
  have hs : (∑ i, coords p w.val a i) =
      (if p then 24 - 2 * (weight w.val : ℤ) else 2 * (weight w.val : ℤ)) +
        4 * (∑ i, flag (a i)) + 8 * ∑ i, carry p (w.val i) (a i) := by
    unfold coords
    rw [sum_congr rfl (fun i _ => sum_rule p (w.val i) (a i))]
    simp only [sum_add_distrib, ← mul_sum, anchor_sum]
  rw [he, hs]
  cases p <;> simp only [budget, parity, total, Bool.false_eq_true, ite_false, ite_true] <;> omega

private abbrev Shell := {x : Lattice // normSq x.val = 48}
private abbrev Params := Σ p : Bool, Σ w : Codeword, Picks p w.val (budget p (weight w.val)) (parity p)

private def pack : Params → Shell := fun ⟨p,w,a⟩ =>
  ⟨⟨coords p w.val a.val, by
    apply (inLeech_iff _).2
    have hs := ((constraints p w a.val).2 a.property).2
    have hp (i : Fin 24) : coords p w.val a.val i % 2 = parity p := point_parity _ _ _
    have hw : IsGolayWord (residueSet (coords p w.val a.val) (special p)) :=
      (coords_residue p w.val a.val).symm ▸ w.property
    cases p with
    | false => exact Or.inl ⟨hp,hs,hw⟩
    | true => exact Or.inr ⟨hp,hs,hw⟩⟩, ((constraints p w a.val).2 a.property).1⟩

private theorem pack_injective : Function.Injective pack := by
  rintro ⟨p,w,a⟩ ⟨q,v,b⟩ h
  have hx : coords p w.val a.val = coords q v.val b.val :=
    congrArg (fun x : Shell => x.val.val) h
  have hp : parity p = parity q := (point_parity p (w.val 0) (a.val 0)).symm.trans
    ((congrArg (fun x : Vec => x 0 % 2) hx).trans (point_parity q (v.val 0) (b.val 0)))
  have he : p = q := by cases p <;> cases q <;> first | rfl | contradiction
  subst q
  have hw : w = v := Subtype.ext ((coords_residue p w.val a.val).symm.trans
    ((congrArg (fun x => residueSet x (special p)) hx).trans (coords_residue p v.val b.val)))
  subst v
  have ha : a = b := Subtype.ext (funext (fun i => value_inj p (w.val i) (congrFun hx i)))
  subst b; rfl

private theorem pack_surjective : Function.Surjective pack := by
  intro x
  obtain ⟨p, hp, hs, hw⟩ : ∃ p : Bool, (∀ i, x.val.val i % 2 = parity p) ∧
      (∑ i, x.val.val i) % 8 = total p ∧ IsGolayWord (residueSet x.val.val (special p)) := by
    rcases (inLeech_iff x.val.val).1 x.val.property with he | ho
    · exact ⟨false, he⟩
    · exact ⟨true, ho⟩
  let w : Codeword := ⟨residueSet x.val.val (special p), hw⟩
  have hh (i : Fin 24) : ∃ a : Label, value p (w.val i) a = x.val.val i := by
    apply value_covers p _ (hp i)
    calc
      _ ≤ normSq x.val.val := single_le_sum (fun j _ => sq_nonneg (x.val.val j)) (mem_univ i)
      _ = 48 := x.property
  choose a ha using hh
  have he : coords p w.val a = x.val.val := funext ha
  have hcond := (constraints p w a).1 (by rw [he]; exact ⟨x.property,hs⟩)
  exact ⟨⟨p,w,a,hcond⟩, Subtype.ext (Subtype.ext he)⟩

private theorem per_word (p : Bool) (w : Codeword) :
    Fintype.card (Picks p w.val (budget p (weight w.val)) (parity p)) =
      if p then 2048 else if weight w.val = 8 then 4096 else if weight w.val = 12 then 2048 else 0 := by
  rw [card_picks]
  have hz := zeros_ones w.val
  have hm : weight w.val = 0 ∨ 8 ≤ weight w.val := by
    by_cases h : ∃ i, w.val i = true
    · exact Or.inr (golay_weight_ge_eight w.property h)
    · left; simp [weight, show ∀ i, w.val i ≠ true by simpa using h]
  cases p with
  | true => exact odd_choices _ _ hz
  | false =>
    rw [bits_weight] at hz ⊢
    exact even_choices _ _ hz (golay_weight_mod_four w.property) hm

/-- All vectors of squared length 48 in the integer-coordinate Leech lattice. -/
theorem card_norm48_vectors : Nat.card {x : Lattice // normSq x.val = 48} = 16773120 := by
  classical
  let equiv := Equiv.ofBijective pack ⟨pack_injective,pack_surjective⟩
  rw [← Nat.card_congr equiv, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp_rw [Fintype.card_sigma, per_word]
  rw [Fintype.sum_bool]
  have hterm (w : Codeword) :
      (if weight w.val = 8 then 4096 else if weight w.val = 12 then 2048 else 0) =
        (if weight w.val = 8 then 1 else 0) * 4096 + (if weight w.val = 12 then 1 else 0) * 2048 := by
    split_ifs <;> omega
  simp only [Bool.false_eq_true, ite_false, ite_true, hterm, sum_add_distrib, ← sum_mul,
    sum_boole, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id]
  have h8 := Fintype.card_subtype (fun w : Codeword => weight w.val = 8)
  have h12 := Fintype.card_subtype (fun w : Codeword => weight w.val = 12)
  rw [← h8, ← h12, card_octad, card_dodecad, card_codeword]
  decide

end LeechNorm48
