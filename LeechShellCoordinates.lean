import LeechNorm48Count
import LeechSymmetry

/-! # Counting Leech lattice vectors by their Golay residue words

The labels record each coordinate's value, its contribution to squared length,
and its contribution to the sum modulo eight. -/
namespace LeechShellCoordinates

open LeechLattice LeechMinimal LeechCodeCounts LeechSymmetry LeechNorm48Count Finset

private def value (odd bit : Bool) : Label → ℤ :=
  if odd then (if bit then ![7,3,-1,-5] else ![-7,-3,1,5])
  else (if bit then ![-6,-2,2,6] else ![-8,-4,0,4])

private def parity (p : Bool) : ℤ := if p then 1 else 0
private def special (p : Bool) : ℤ := if p then 3 else 2
private def total (p : Bool) : ℤ := if p then 4 else 0
private def budget (u : ℤ) (p : Bool) (k : ℕ) : ℤ := if p then u - 3 else u - (k : ℤ) / 2
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

private theorem value_covers (p : Bool) (x : ℤ) (hp : x % 2 = parity p) (hlo : -8 ≤ x) (hhi : x ≤ 7) :
    ∃ a : Label, value p (decide (x % 4 = special p % 4)) a = x := by
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

private theorem constraints (u : ℤ) (p : Bool) (w : Codeword) (a : Fin 24 → Label) :
    (normSq (coords p w.val a) = 8 * u ∧ (∑ i, coords p w.val a i) % 8 = total p) ↔
    ((∑ i, cost p (w.val i) (a i)) = budget u p (weight w.val) ∧
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

private abbrev Shell (u : ℤ) := {x : Lattice // normSq x.val = 8 * u}
private abbrev Params (u : ℤ) := Σ p : Bool, Σ w : Codeword, Picks p w.val (budget u p (weight w.val)) (parity p)

private def pack (u : ℤ) : Params u → Shell u := fun ⟨p,w,a⟩ =>
  ⟨⟨coords p w.val a.val, by
    apply (inLeech_iff _).2
    have hs := ((constraints u p w a.val).2 a.property).2
    have hp (i : Fin 24) : coords p w.val a.val i % 2 = parity p := point_parity _ _ _
    have hw : IsGolayWord (residueSet (coords p w.val a.val) (special p)) :=
      (coords_residue p w.val a.val).symm ▸ w.property
    cases p with
    | false => exact Or.inl ⟨hp,hs,hw⟩
    | true => exact Or.inr ⟨hp,hs,hw⟩⟩, ((constraints u p w a.val).2 a.property).1⟩

private theorem pack_injective (u : ℤ) : Function.Injective (pack u) := by
  rintro ⟨p,w,a⟩ ⟨q,v,b⟩ h
  have hx : coords p w.val a.val = coords q v.val b.val :=
    congrArg (fun x : Shell u => x.val.val) h
  have hp : parity p = parity q := (point_parity p (w.val 0) (a.val 0)).symm.trans
    ((congrArg (fun x : Vec => x 0 % 2) hx).trans (point_parity q (v.val 0) (b.val 0)))
  have he : p = q := by cases p <;> cases q <;> first | rfl | contradiction
  subst q
  have hw : w = v := Subtype.ext ((coords_residue p w.val a.val).symm.trans
    ((congrArg (fun x => residueSet x (special p)) hx).trans (coords_residue p v.val b.val)))
  subst v
  have ha : a = b := Subtype.ext (funext (fun i => value_inj p (w.val i) (congrFun hx i)))
  subst b; rfl

private theorem pack_covers (u : ℤ) (x : Shell u)
    (bound : ∀ i, -8 ≤ x.val.val i ∧ x.val.val i ≤ 7) : ∃ a, pack u a = x := by
  obtain ⟨p, hp, hs, hw⟩ : ∃ p : Bool, (∀ i, x.val.val i % 2 = parity p) ∧
      (∑ i, x.val.val i) % 8 = total p ∧ IsGolayWord (residueSet x.val.val (special p)) := by
    rcases (inLeech_iff x.val.val).1 x.val.property with he | ho
    · exact ⟨false, he⟩
    · exact ⟨true, ho⟩
  let w : Codeword := ⟨residueSet x.val.val (special p), hw⟩
  have hh (i : Fin 24) : ∃ a : Label, value p (w.val i) a = x.val.val i := by
    exact value_covers p _ (hp i) (bound i).1 (bound i).2
  choose a ha using hh
  have he : coords p w.val a = x.val.val := funext ha
  have hcond := (constraints u p w a).1 (by rw [he]; exact ⟨x.property,hs⟩)
  exact ⟨⟨p,w,a,hcond⟩, Subtype.ext (Subtype.ext he)⟩

private theorem card_params (u : ℤ) : Nat.card (Params u) =
      ∑ p : Bool, ∑ w : Codeword, tally p (24 - weight w.val) (weight w.val)
        (if p then u - 3 else u - (weight w.val : ℤ) / 2) (if p then 1 else 0) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp_rw [Fintype.card_sigma, card_picks]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro w _
  have h := zeros_ones w.val
  rw [bits_weight] at h ⊢
  rw [show bits w.val false = 24 - weight w.val by omega]
  rfl

/-- Count a shell by its Golay words when all coordinates in the shell lie between −7 and 7. -/
theorem card_vectors_from_choices (u : ℤ)
    (bound : ∀ x : Lattice, normSq x.val = 8 * u → ∀ i, -7 ≤ x.val i ∧ x.val i ≤ 7) :
    Nat.card {x : Lattice // normSq x.val = 8 * u} =
      ∑ p : Bool, ∑ w : Codeword, tally p (24 - weight w.val) (weight w.val)
        (if p then u - 3 else u - (weight w.val : ℤ) / 2) (if p then 1 else 0) := by
  have onto : Function.Surjective (pack u) := fun x => pack_covers u x fun i => by
    have h := bound x.val x.property i
    omega
  exact (Nat.card_congr (Equiv.ofBijective (pack u) ⟨pack_injective u, onto⟩)).symm.trans (card_params u)

/-- Count the part of a shell whose coordinates all lie from −8 to 7. -/
theorem card_box_from_choices (u : ℤ) :
    Nat.card {x : {v : Lattice // normSq v.val = 8 * u} //
      ∀ i, -8 ≤ x.val.val i ∧ x.val.val i ≤ 7} =
      ∑ p : Bool, ∑ w : Codeword, tally p (24 - weight w.val) (weight w.val)
        (if p then u - 3 else u - (weight w.val : ℤ) / 2) (if p then 1 else 0) := by
  let box := {x : Shell u // ∀ i, -8 ≤ x.val.val i ∧ x.val.val i ≤ 7}
  let f : Params u → box := fun a => ⟨pack u a, fun i => by
    obtain ⟨p,w,v⟩ := a
    change -8 ≤ value p (w.val i) (v.val i) ∧ value p (w.val i) (v.val i) ≤ 7
    generalize w.val i = b
    generalize v.val i = j
    cases p <;> cases b <;> fin_cases j <;> decide⟩
  have bij : Function.Bijective f := by
    constructor
    · intro a b h
      exact pack_injective u (congrArg Subtype.val h)
    · intro x
      obtain ⟨a,ha⟩ := pack_covers u x.val x.property
      exact ⟨a, Subtype.ext ha⟩
  exact (Nat.card_congr (Equiv.ofBijective f bij)).symm.trans (card_params u)

end LeechShellCoordinates
