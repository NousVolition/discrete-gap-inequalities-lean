import ConwayMoves

/-! # The orbit of a standard axis contains every vector of squared length 64 -/

namespace ConwayMoves

open GolayMathieu LeechSextet LeechSymmetry LeechLattice LeechMinimal

private theorem bounded_four (a b c d : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hab : b ≤ a) (hbc : c ≤ b) (hcd : d ≤ c) (ha8 : a ≤ 8)
    (hp : b%2=a%2 ∧ c%2=a%2 ∧ d%2=a%2) (hs : a+b+c+d ≤ 2*a)
    (hl : a^2+b^2+c^2+d^2+20*(a%2) ≤ 64)
    (hh : 64 ≤ a^2+b^2+c^2+21*d^2) : a = 8 ∨ (a=6 ∧ b=2 ∧ c=2 ∧ d=2) := by
  have finiteCheck : ∀ i j k l : Fin 9,
      let a := (i.val : ℤ); let b := (j.val : ℤ); let c := (k.val : ℤ); let d := (l.val : ℤ)
      b ≤ a → c ≤ b → d ≤ c → b%2=a%2 ∧ c%2=a%2 ∧ d%2=a%2 →
      a+b+c+d ≤ 2*a → a^2+b^2+c^2+d^2+20*(a%2) ≤ 64 →
      64 ≤ a^2+b^2+c^2+21*d^2 → a=8 ∨ (a=6 ∧ b=2 ∧ c=2 ∧ d=2) := by decide +kernel
  have h := finiteCheck ⟨a.toNat, by omega⟩ ⟨b.toNat, by omega⟩
    ⟨c.toNat, by omega⟩ ⟨d.toNat, by omega⟩
  simp only [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb,
    Int.toNat_of_nonneg hc, Int.toNat_of_nonneg hd] at h
  exact h hab hbc hcd hp hs hl hh

private theorem head_cases (v : Point → ℤ) (vpos : ∀ i, 0 ≤ v i)
    (ord : Antitone v) (par : ∀ i, v i % 2 = v 0 % 2)
    (hn : (∑ i, v i ^ 2) = 64) (hfour : v 0 + v 1 + v 2 + v 3 ≤ 2*v 0) :
    v 0 = 8 ∨ (v 0 = 6 ∧ v 1 = 2 ∧ v 2 = 2 ∧ v 3 = 2) := by
  have split : (∑ i, v i^2) = (v 0^2 + v 1^2 + v 2^2 + v 3^2) +
      ∑ i : Fin 20, v (Fin.natAdd 4 i)^2 := by
    rw [Fin.sum_univ_add (a := 4) (b := 20), Fin.sum_univ_four]; rfl
  rw [split] at hn
  have lo : ∀ i : Fin 20, v 0 % 2 ≤ v (Fin.natAdd 4 i)^2 := by
    intro i
    have h := par (Fin.natAdd 4 i)
    by_cases hz : v (Fin.natAdd 4 i) = 0
    · rw [hz] at h ⊢; omega
    · have hv := vpos (Fin.natAdd 4 i); have : 1 ≤ v (Fin.natAdd 4 i) := by omega
      have : 1 ≤ v (Fin.natAdd 4 i)^2 := by nlinarith
      omega
  have hi : ∀ i : Fin 20, v (Fin.natAdd 4 i)^2 ≤ v 3^2 := by
    intro i
    have h := ord (show (3 : Fin 24) ≤ Fin.natAdd 4 i from by change 3 ≤ 4+i.val; omega)
    exact pow_le_pow_left₀ (vpos _) h 2
  have hlow := Finset.sum_le_sum (s := Finset.univ) (fun i _ => lo i)
  have hhigh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hlow hhigh
  have htail : 0 ≤ ∑ i : Fin 20, v (Fin.natAdd 4 i)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h8 : v 0 ≤ 8 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
  apply bounded_four _ _ _ _ (vpos _) (vpos _) (vpos _) (vpos _)
    (ord (by decide : (0 : Point) ≤ 1)) (ord (by decide : (1 : Point) ≤ 2))
    (ord (by decide : (2 : Point) ≤ 3)) h8 ⟨par 1, par 2, par 3⟩ hfour <;> linarith

private theorem first_eight {y : Lattice} (h : y.val 0 = 8) (hn : normSq y.val = 64) :
    y = latticeAxis 0 := by
  have leq : ∀ i : Point, axis 0 i ^ 2 ≤ y.val i ^ 2 := by
    intro i; by_cases hi : i = 0
    · subst i; simp [axis,h]
    · simpa [axis,hi] using sq_nonneg (y.val i)
  have eqs : (∑ i, axis 0 i ^ 2) = ∑ i, y.val i ^ 2 := (axis_norm 0).trans hn.symm
  apply Subtype.ext; funext i
  have hi := (Finset.sum_eq_sum_iff_of_le (fun j _ => leq j)).1 eqs i (Finset.mem_univ i)
  change y.val i = axis 0 i
  by_cases h0 : i = 0
  · subst i; simpa [axis] using h
  · simp [axis,h0] at hi ⊢; nlinarith

private theorem six_contradiction (x : Lattice) (hn : normSq x.val = 64)
    (hM : ∀ y, Reaches x y → ∀ j, |y.val j| ≤ 6) (f : Fin 4 ↪ Point)
    (h6 : |x.val (f 0)| = 6) (h1 : |x.val (f 1)| = 2)
    (h2 : |x.val (f 2)| = 2) (h3 : |x.val (f 3)| = 2) : False := by
  obtain ⟨y, hy, hv⟩ := arrange_four x f (fun _ => false)
  let z := symmetry y
  have hz : Reaches x z := reaches_trans hy ⟨symmetry,sextet_mem,rfl⟩
  have hsum : (∑ j : Fin 4, y.val (first j)) = 12 := by rw [Fin.sum_univ_four]; simp [hv,h6,h1,h2,h3]
  have hi (j : Fin 4) : 2 * z.val (first j) = 2 * |x.val (f j)| - 12 := by
    have h := first_norm_move y j
    rw [hsum, hv] at h
    exact h
  have h0z : z.val 0 = 0 := by have := hi 0; rw [h6] at this; change 2*z.val 0 = _ at this; omega
  have h1z : z.val 1 = -4 := by have := hi 1; rw [h1] at this; change 2*z.val 1 = _ at this; omega
  have h2z : z.val 2 = -4 := by have := hi 2; rw [h2] at this; change 2*z.val 2 = _ at this; omega
  have h3z : z.val 3 = -4 := by have := hi 3; rw [h3] at this; change 2*z.val 3 = _ at this; omega
  have tail (i : Fin 20) : z.val (Fin.natAdd 4 i) = 0 := by
    let j : Point := Fin.natAdd 4 i
    let e := Equiv.swap (0 : Point) j
    let t := (Fin.castLEEmb (by decide : 4 ≤ 24)).trans e.toEmbedding
    have b := four_sum_bound z 6 (fun v h => hM v (reaches_trans hz h)) t
    have hj : 4 ≤ j.val := by change 4 ≤ 4+i.val; omega
    have ht0 : t 0 = j := Equiv.swap_apply_left (0 : Point) j
    have ht1 : t 1 = 1 := Equiv.swap_apply_of_ne_of_ne (show (1 : Point) ≠ 0 by decide)
      (show (1 : Point) ≠ j by intro h; have h' : 1 = j.val := congrArg Fin.val h; omega)
    have ht2 : t 2 = 2 := Equiv.swap_apply_of_ne_of_ne (show (2 : Point) ≠ 0 by decide)
      (show (2 : Point) ≠ j by intro h; have h' : 2 = j.val := congrArg Fin.val h; omega)
    have ht3 : t 3 = 3 := Equiv.swap_apply_of_ne_of_ne (show (3 : Point) ≠ 0 by decide)
      (show (3 : Point) ≠ j by intro h; have h' : 3 = j.val := congrArg Fin.val h; omega)
    rw [Fin.sum_univ_four,ht0,ht1,ht2,ht3,h1z,h2z,h3z] at b
    norm_num at b
    change z.val j = 0
    exact abs_nonpos_iff.mp (by linarith)
  have n := (reaches_norm hz).trans hn
  change (∑ i : Fin (4+20), z.val i ^ 2) = 64 at n
  rw [Fin.sum_univ_add, Fin.sum_univ_four] at n
  change z.val 0^2 + z.val 1^2 + z.val 2^2 + z.val 3^2 + _ = 64 at n
  simp [h0z,h1z,h2z,h3z,tail] at n

/-- The listed moves send the standard axis to every lattice vector of squared length 64. -/
theorem norm64_transitive (x : Lattice) (hn : normSq x.val = 64) : Reaches (latticeAxis 0) x := by
  classical
  let : Fintype G := Fintype.ofFinite _
  let size := fun p : G × Point => |(p.1.val x).val p.2|
  obtain ⟨⟨g, j⟩, _, hmax⟩ := Finset.exists_max_image Finset.univ size Finset.univ_nonempty
  let y := g.val x
  have hy : Reaches x y := ⟨_,g.property,rfl⟩
  let q := Tuple.sort (fun i => -|y.val i|)
  let v := fun i => |y.val (q i)|
  have ord : Antitone v := by
    intro i k hik
    have h := Tuple.monotone_sort (fun i => -|y.val i|) hik
    exact neg_le_neg_iff.mp h
  have hM : ∀ z, Reaches y z → ∀ i, |z.val i| ≤ v 0 := by
    rintro _ ⟨h,hh,rfl⟩ i
    have hm := hmax (⟨h*g.val,G.mul_mem hh g.property⟩,i) (Finset.mem_univ _)
    have ho := ord (Fin.zero_le (q.symm j))
    change |y.val (q (q.symm j))| ≤ v 0 at ho
    rw [q.apply_symm_apply] at ho
    exact hm.trans ho
  let f := (Fin.castLEEmb (by decide : 4 ≤ 24)).trans q.toEmbedding
  have hvsum : (∑ i, v i ^ 2) = 64 := by
    change (∑ i, |y.val (q i)|^2) = 64
    simp_rw [sq_abs]
    rw [Equiv.sum_comp q (fun i => y.val i^2)]
    exact (reaches_norm hy).trans hn
  obtain ⟨m, _, hp, _, _⟩ := y.property
  have par (i : Point) : v i % 2 = m := by
    have h := hp (q i)
    change |y.val (q i)| % 2 = m
    rcases abs_choice (y.val (q i)) with ha | ha <;> rw [ha] <;> omega
  have hfour := four_sum_bound y (v 0) hM f
  rw [Fin.sum_univ_four] at hfour
  rcases head_cases v (fun _ => abs_nonneg _) ord (fun i => (par i).trans (par 0).symm)
    hvsum hfour with h8 | ⟨h6,h1,h2,h3⟩
  · obtain ⟨z,hz,he⟩ := arrange_four y f (fun _ => false)
    have h0 : z.val 0 = 8 := (he 0).trans h8
    have hxz := reaches_trans hy hz
    rw [first_eight h0 ((reaches_norm hxz).trans hn)] at hxz
    exact reaches_symm hxz
  · exact False.elim (six_contradiction y ((reaches_norm hy).trans hn)
      (h6 ▸ hM) f h6 h1 h2 h3)

theorem generators_span_aut : G = ⊤ :=
  eq_top_of_norm64_transitive G sign_mem perm_mem norm64_transitive

end ConwayMoves
