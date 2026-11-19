import LeechOctadCount

/-! # The playground's Golay generator in the proved code's coordinates

The recipe below models the Leech page's residue loop, shifted generators and
descending XOR basis reduction. Finite witnesses are checked by Lean's kernel;
closure arguments then cover every message, not only the generator rows.
-/
namespace PlaygroundGolay

open LeechLattice GolayMatrixDistance Finset

def quadraticResidues : List Nat :=
  (List.range' 1 22).foldl (fun qs i =>
    let r := i * i % 23
    if qs.contains r then qs else qs ++ [r]) []

def rawGenerator (s : Nat) : UInt32 :=
  quadraticResidues.foldl (fun w x => w ||| (1 <<< ((x + s) % 23).toUInt32)) 0 |||
    ((1 : UInt32) <<< (23 : UInt32))

def rawGenerators : List UInt32 := (List.range 23).map rawGenerator ++ [0xFFFFFF]

/-- Insert into the descending basis, modeling the page's numeric descending sort. -/
def insertDescending (v : UInt32) : List UInt32 → List UInt32
  | [] => [v]
  | b :: bs => if b ≤ v then v :: b :: bs else b :: insertDescending v bs

def reduceBasis (basis : List UInt32) (g : UInt32) : List UInt32 :=
  let v := basis.foldl (fun v b => min v (v ^^^ b)) g
  if v == 0 then basis else insertDescending v basis

def computedBasis : List UInt32 := rawGenerators.foldl reduceBasis []

def basisMasks : Array UInt32 :=
  #[8729438, 4716696, 2358348, 1179174, 1005026, 290622,
    145311, 84390, 42195, 17118, 15946, 7973]

theorem quadraticResidues_eq : quadraticResidues = [1,4,9,16,2,13,3,18,12,8,6] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem computedBasis_eq : computedBasis = basisMasks.toList := by
  decide +kernel

def coordinateMap (i : Fin 24) : Fin 24 :=
  (#[0,1,2,3,4,5,6,17,8,12,9,16,7,18,14,13,19,20,22,23,15,10,11,21] : Array (Fin 24)).getD i.val 0

def inverseMap (i : Fin 24) : Fin 24 :=
  (#[0,1,2,3,4,5,6,12,8,10,21,22,9,15,14,20,11,7,13,16,17,23,18,19] : Array (Fin 24)).getD i.val 0

/-- Maps a playground coordinate index to its Lean coordinate index. -/
def coordinateEquiv : Fin 24 ≃ Fin 24 where
  toFun := coordinateMap
  invFun := inverseMap
  left_inv := by decide
  right_inv := by decide

def toLean {α : Type*} (x : Fin 24 → α) : Fin 24 → α := fun i => x (coordinateEquiv.symm i)
def toPlay {α : Type*} (x : Fin 24 → α) : Fin 24 → α := fun i => x (coordinateEquiv i)

theorem toPlay_toLean {α : Type*} (x : Fin 24 → α) : toPlay (toLean x) = x := by
  funext i; simp [toPlay, toLean]

theorem toLean_toPlay {α : Type*} (x : Fin 24 → α) : toLean (toPlay x) = x := by
  funext i; simp [toPlay, toLean]

def encodeStep (rows : Array UInt32) (m : Nat) (acc : UInt32) (i : Nat) : UInt32 :=
  if (m >>> i) &&& 1 == 1 then acc ^^^ rows.getD i 0 else acc

def encodeWith (rows : Array UInt32) (m : Nat) : UInt32 :=
  (List.range 12).foldl (encodeStep rows m) 0

/-- Code membership uses the basis computed from the playground's recipe. -/
def IsPlayWord (w : Fin 24 → Bool) : Prop :=
  ∃ m < 4096, word (encodeWith computedBasis.toArray m) = w

theorem isPlayWord_iff (w : Fin 24 → Bool) : IsPlayWord w ↔
    ∃ m < 4096, word (encodeWith basisMasks m) = w := by
  simp only [IsPlayWord, computedBasis_eq, Array.toArray_toList]

theorem word_xor (u v : UInt32) : word (u ^^^ v) = fun k => word u k ^^ word v k := by
  funext k
  exact bitAt_xor u v k.val (by omega)

private theorem fold_encode_xor (rows : Array UInt32) (m n : Nat) (l : List Nat)
    (a b : UInt32) : l.foldl (encodeStep rows (m ^^^ n)) (a ^^^ b) =
      l.foldl (encodeStep rows m) a ^^^ l.foldl (encodeStep rows n) b := by
  induction l generalizing a b with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    simp only [encodeStep, natBit_eq, Nat.testBit_xor]
    cases m.testBit i <;> cases n.testBit i <;>
      simp [UInt32.xor_assoc, UInt32.xor_comm, u32_xor_left_comm]

theorem encodeWith_xor (rows : Array UInt32) (m n : Nat) :
    encodeWith rows (m ^^^ n) = encodeWith rows m ^^^ encodeWith rows n := by
  simp only [encodeWith, ← fold_encode_xor]
  rfl

theorem encodeWith_zero (rows : Array UInt32) : encodeWith rows 0 = 0 := by
  have h : ∀ l : List Nat, l.foldl (encodeStep rows 0) 0 = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih => simpa [encodeStep] using ih
  exact h _

theorem isPlayWord_false : IsPlayWord (fun _ => false) := by
  rw [isPlayWord_iff]
  exact ⟨0, by norm_num, by rw [encodeWith_zero, word_zero]⟩

theorem isPlayWord_xor {u v : Fin 24 → Bool} (hu : IsPlayWord u) (hv : IsPlayWord v) :
    IsPlayWord (fun k => u k ^^ v k) := by
  obtain ⟨m, hm, rfl⟩ := (isPlayWord_iff u).1 hu
  obtain ⟨n, hn, rfl⟩ := (isPlayWord_iff v).1 hv
  rw [isPlayWord_iff]
  refine ⟨m ^^^ n, Nat.xor_lt_two_pow (n := 12) hm hn, ?_⟩
  rw [encodeWith_xor, word_xor]

def forwardMessage (i : Fin 12) : Fin 4096 :=
  (#[478,2200,1740,678,994,830,927,294,595,94,714,933] : Array (Fin 4096)).getD i.val 0

def reverseMessage (i : Fin 12) : Fin 4096 :=
  (#[2105,3360,2040,3656,3169,1865,2801,3856,3345,649,3804,3387] : Array (Fin 4096)).getD i.val 0

theorem forward_row (i : Fin 12) : toLean (word (basisMasks.getD i.val 0)) =
    word (encodeNat (forwardMessage i).val) := by
  have h : ∀ (j : Fin 12) (k : Fin 24), toLean (word (basisMasks.getD j.val 0)) k =
      word (encodeNat (forwardMessage j).val) k := by decide +kernel
  funext k; exact h i k

theorem reverse_row (i : Fin 12) : toPlay (word (genMasks.getD i.val 0)) =
    word (encodeWith basisMasks (reverseMessage i).val) := by
  have h : ∀ (j : Fin 12) (k : Fin 24), toPlay (word (genMasks.getD j.val 0)) k =
      word (encodeWith basisMasks (reverseMessage j).val) k := by decide +kernel
  funext k; exact h i k

theorem encodeWith_property (rows : Array UInt32) (m : Nat) (P : (Fin 24 → Bool) → Prop)
    (hzero : P (fun _ => false))
    (hxor : ∀ u v, P u → P v → P (fun k => u k ^^ v k))
    (hrows : ∀ i < 12, P (word (rows.getD i 0))) : P (word (encodeWith rows m)) := by
  have hfold : ∀ l : List Nat, (∀ i ∈ l, i < 12) →
      ∀ a, P (word a) → P (word (l.foldl (encodeStep rows m) a)) := by
    intro l
    induction l with
    | nil => intro _ a ha; exact ha
    | cons i l ih =>
      intro hl a ha
      rw [List.foldl_cons]
      apply ih (fun j hj => hl j (by simp [hj]))
      simp only [encodeStep]
      split_ifs
      · rw [word_xor]; exact hxor _ _ ha (hrows i (hl i (by simp)))
      · exact ha
  apply hfold _ (by simpa using fun (i : Nat) (hi : i < 12) => hi)
  simpa only [word_zero] using hzero

theorem play_toLean {w : Fin 24 → Bool} (hw : IsPlayWord w) : IsGolayWord (toLean w) := by
  obtain ⟨m, _, rfl⟩ := (isPlayWord_iff w).1 hw
  apply encodeWith_property basisMasks m (fun v => IsGolayWord (toLean v))
  · exact isGolayWord_false
  · intro u v hu hv; exact isGolayWord_xor hu hv
  · intro i hi
    rw [forward_row ⟨i, hi⟩]
    exact ⟨(forwardMessage ⟨i, hi⟩).val, (forwardMessage ⟨i, hi⟩).isLt, rfl⟩

theorem lean_toPlay {w : Fin 24 → Bool} (hw : IsGolayWord w) : IsPlayWord (toPlay w) := by
  obtain ⟨m, _, rfl⟩ := hw
  change IsPlayWord (toPlay (word (encodeWith genMasks m)))
  apply encodeWith_property genMasks m (fun v => IsPlayWord (toPlay v))
  · exact isPlayWord_false
  · intro u v hu hv; exact isPlayWord_xor hu hv
  · intro i hi
    rw [reverse_row ⟨i, hi⟩, isPlayWord_iff]
    exact ⟨(reverseMessage ⟨i, hi⟩).val, (reverseMessage ⟨i, hi⟩).isLt, rfl⟩

/-- The computed modulo-23 code is the proved modulo-11 code after relabeling coordinates. -/
theorem code_correspondence (w : Fin 24 → Bool) : IsPlayWord w ↔ IsGolayWord (toLean w) := by
  constructor
  · exact play_toLean
  · intro h
    simpa only [toPlay_toLean] using lean_toPlay h

theorem weight_toLean (w : Fin 24 → Bool) :
    LeechCodeCounts.weight (toLean w) = LeechCodeCounts.weight w := by
  unfold LeechCodeCounts.weight
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquiv coordinateEquiv.symm (fun _ => Iff.rfl))

noncomputable def codeEquiv : {w : Fin 24 → Bool // IsPlayWord w} ≃ LeechCodeCounts.Codeword where
  toFun w := ⟨toLean w.val, play_toLean w.property⟩
  invFun w := ⟨toPlay w.val, lean_toPlay w.property⟩
  left_inv w := Subtype.ext (toPlay_toLean w.val)
  right_inv w := Subtype.ext (toLean_toPlay w.val)

noncomputable instance : Fintype {w : Fin 24 → Bool // IsPlayWord w} := Fintype.ofFinite _

theorem card_play_code : Fintype.card {w : Fin 24 → Bool // IsPlayWord w} = 4096 := by
  rw [Fintype.card_congr codeEquiv, LeechCodeCounts.card_codeword]

end PlaygroundGolay
