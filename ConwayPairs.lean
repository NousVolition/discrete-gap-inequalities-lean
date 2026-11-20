import ConwayCoordinates
import ConwayTransitivity

/-! # Ordered orthogonal pairs of shortest vectors -/

namespace ConwayPairs

open GolayMathieu ConwayIncidence ConwayMoves LeechSymmetry LeechLattice LeechMinimal

def asL (x : MinimalVectors) : Lattice := ⟨x.val,x.property.1⟩

def rootVec (b : Bool) : Vec := fun i =>
  (if i = 0 then 4 else 0) + (if i = 1 then twoSign b 4 else 0)

def root (b : Bool) : MinimalVectors :=
  ⟨rootVec b, four_mem_norm ((by unfold FourShape; decide +kernel : ∀ a, FourShape (rootVec a)) b)⟩

theorem root_dot (x : Vec) : dot (root true).val x = 4 * (x 0 - x 1) := by
  simp [root,rootVec,dot,add_mul,ite_mul,Finset.sum_add_distrib,twoSign]; ring

theorem roots_sum : asL (root true) + asL (root false) = latticeAxis 0 := by
  apply Subtype.ext; decide +kernel

theorem roots_sub : asL (root false) - asL (root true) = latticeAxis 1 := by
  apply Subtype.ext; decide +kernel

abbrev Pair := {p : MinimalVectors × MinimalVectors // dot p.1.val p.2.val = 0}

def basePair : Pair := ⟨(root true,root false), by decide +kernel⟩

instance : MulAction Aut Pair where
  smul g p := ⟨(onShortest g p.val.1, onShortest g p.val.2),
    (map_dot g (asL p.val.1) (asL p.val.2)).trans p.property⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem coord_bound (x : MinimalVectors) (i : Point) : |x.val i| ≤ 4 := by
  rcases (minimal_iff x.val).1 x.property with h|h|⟨w, _, j, h⟩
  · rcases h.1 i with hi|hi|hi <;> rw [hi] <;> decide
  · rcases h.1 i with hi|hi|hi <;> rw [hi] <;> decide
  · rw [h]; unfold oddVector; split_ifs <;> decide

theorem four_of_first (x : MinimalVectors) (h0 : x.val 0 = 4) : FourShape x.val := by
  rcases (minimal_iff x.val).1 x.property with h|h|h
  · exact h
  · rcases h.1 0 with hi|hi|hi <;> omega
  · have := oddShape_parity h 0; omega

theorem root_unique (x : MinimalVectors) (b : Bool) (h0 : x.val 0 = 4)
    (h1 : x.val 1 = twoSign b 4) : x = root b := by
  have low (i : Point) : (root b).val i ^ 2 ≤ x.val i ^ 2 := by
    by_cases hi : i = 0
    · subst i; simp [root,rootVec,h0]
    · by_cases hj : i = 1
      · subst i; simp [root,rootVec,h1]
      · simpa [root,rootVec,hi,hj] using sq_nonneg (x.val i)
  have eqs := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun i _ => low i)).1
    ((root b).property.2.trans x.property.2.symm)
  apply Subtype.ext; funext i
  by_cases hi : i = 0
  · subst i; simpa [root,rootVec] using h0
  · by_cases hj : i = 1
    · subst i; simpa [root,rootVec] using h1
    · have h := eqs i (Finset.mem_univ i)
      simp [root,rootVec,hi,hj] at h ⊢
      nlinarith

theorem pair_transitive (p : Pair) : ∃ g : Aut, g • basePair = p := by
  let u := asL p.val.1
  let v := asL p.val.2
  have hn : normSq (u+v).val = 64 := by
    change normSq (p.val.1.val+p.val.2.val) = 64
    rw [normSq_add, p.val.1.property.2, p.val.2.property.2,p.property]; decide
  obtain ⟨a, _, ha⟩ := reaches_symm (norm64_transitive _ hn)
  let x := onShortest a p.val.1
  let y := onShortest a p.val.2
  have added : x.val + y.val = axis 0 := congrArg Subtype.val ((a.property.1 u v).symm.trans ha)
  have hs (i : Point) : x.val i + y.val i = axis 0 i := congrFun added i
  have h0 := hs 0
  have hx := coord_bound x 0
  have hy := coord_bound y 0
  rw [abs_le] at hx hy
  change x.val 0 + y.val 0 = 8 at h0
  have hx0 : x.val 0 = 4 := by omega
  have hy0 : y.val 0 = 4 := by omega
  have h4 := four_of_first x hx0
  have mem0 : (0 : Point) ∈ support x.val := by simp [support,hx0]
  have card := Finset.card_erase_of_mem mem0
  rw [h4.2] at card
  obtain ⟨j,hj⟩ := Finset.card_eq_one.mp card
  have hmem : j ∈ (support x.val).erase 0 := by rw [hj]; simp
  obtain ⟨hnj,hm⟩ := Finset.mem_erase.mp hmem
  have hj0 : x.val j ≠ 0 := (Finset.mem_filter.mp hm).2
  have hjxy := hs j
  simp [axis,hnj] at hjxy
  let b := decide (x.val j = 4)
  obtain ⟨g,hg⟩ := move_indices 0 j hnj b
  have neg : twoSign b (x.val j) = -4 ∧ twoSign b (y.val j) = 4 := by
    rcases h4.1 j with hj|hj|hj
    · contradiction
    all_goals simp [b,twoSign,hj]; omega
  have h1 : onShortest g x = root true := root_unique _ true ((hg (asL x)).1.trans hx0)
    ((hg (asL x)).2.trans neg.1)
  have h2 : onShortest g y = root false := root_unique _ false ((hg (asL y)).1.trans hy0)
    ((hg (asL y)).2.trans neg.2)
  have he : (g*a) • p = basePair := Subtype.ext (Prod.ext h1 h2)
  exact ⟨(g*a)⁻¹, by rw [← he, inv_smul_smul]⟩

abbrev Partner (v : MinimalVectors) := {w : MinimalVectors // dot v.val w.val = 0}

noncomputable def partnerTransport (g : Aut) (v : MinimalVectors) :
    Partner v ≃ Partner (onShortest g v) :=
  Equiv.subtypeEquiv (onShortest g) (fun w => by
    change _ ↔ dot (g (asL v)).val (g (asL w)).val = 0
    rw [map_dot]; rfl)

theorem shortest_has_partner (v : MinimalVectors) : Nonempty (Partner v) := by
  let f (i : Point) : Fin 5 := ⟨(|v.val i|).toNat, by have := coord_bound v i; omega⟩
  have hi : ¬ Function.Injective f := by
    intro h; have hl := Fintype.card_le_of_injective f h
    norm_num at hl
  obtain ⟨i,j,he,hn⟩ := Function.not_injective_iff.mp hi
  have he' := congrArg (fun n : Fin 5 => (n.val : ℤ)) he
  change ((|v.val i|).toNat : ℤ) = ((|v.val j|).toNat : ℤ) at he'
  simp only [Int.toNat_of_nonneg (abs_nonneg _)] at he'
  have hb : ∃ b, v.val i = twoSign b (v.val j) := by
    rcases abs_eq_abs.mp he' with h|h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  obtain ⟨b,hb⟩ := hb
  obtain ⟨g,hg⟩ := move_indices i j hn.symm b
  have h0 := (hg (asL v)).1
  have h1 := (hg (asL v)).2
  have hdot : dot (root true).val (onShortest g v).val = 0 := by
    rw [root_dot]; change 4*((g (asL v)).val 0 - (g (asL v)).val 1)=0
    rw [h0,h1]; change 4*(v.val i-twoSign b (v.val j))=0; rw [hb]; ring
  have hcomm (x y : Vec) : dot x y = dot y x := by simp [dot,mul_comm]
  exact ⟨(partnerTransport g v).symm ⟨root true,(hcomm _ _).trans hdot⟩⟩

theorem shortest_transitive (v : MinimalVectors) : ∃ g : Aut, onShortest g (root true) = v := by
  obtain ⟨w⟩ := shortest_has_partner v
  obtain ⟨g,h⟩ := pair_transitive ⟨(v,w.val),w.property⟩
  exact ⟨g,congrArg (fun p : Pair => p.val.1) h⟩

def pairEquiv : Pair ≃ (Σ v : MinimalVectors, Partner v) where
  toFun p := ⟨p.val.1,p.val.2,p.property⟩
  invFun p := ⟨(p.1,p.2.val),p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fixes_pair_iff (g : Aut) : g • basePair = basePair ↔
    g (latticeAxis 0) = latticeAxis 0 ∧ g (latticeAxis 1) = latticeAxis 1 := by
  constructor
  · intro h
    have hu := congrArg (fun p : Pair => asL p.val.1) h
    have hv := congrArg (fun p : Pair => asL p.val.2) h
    change g (asL (root true)) = asL (root true) at hu
    change g (asL (root false)) = asL (root false) at hv
    constructor
    · rw [← roots_sum,g.property.1,hu,hv]
    · rw [← roots_sub]; change toAddEquiv g _ = _
      rw [map_sub]; change g _ - g _ = _; rw [hu,hv]
  · rintro ⟨h0,h1⟩
    have same (i : Point) (hi : g (latticeAxis i) = latticeAxis i) (x : MinimalVectors) :
        (onShortest g x).val i = x.val i := by
      have h := map_dot g (asL x) (latticeAxis i)
      rw [hi] at h
      change dot (g (asL x)).val (axis i) = dot x.val (axis i) at h
      rw [dot_axis,dot_axis] at h
      change (g (asL x)).val i = x.val i; omega
    have hr (b : Bool) : onShortest g (root b) = root b :=
      root_unique _ b ((same 0 h0 _).trans (by rfl)) ((same 1 h1 _).trans (by simp [root,rootVec]))
    exact Subtype.ext (Prod.ext (hr true) (hr false))

end ConwayPairs
