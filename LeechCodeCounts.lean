import LeechLattice
import GolayLeechBridge

namespace LeechCodeCounts

open LeechLattice GolayMatrixDistance Finset

theorem word_encode_injective {m n : ℕ} (hm : m < 4096) (hn : n < 4096)
    (h : word (encodeNat m) = word (encodeNat n)) : m = n := by
  have hw : word (encodeNat (m ^^^ n)) = fun _ => false := by
    funext i
    change bitAt (encodeNat (m ^^^ n)) i.val = false
    rw [encodeNat_xor, bitAt_xor _ _ _ (by omega)]
    have hi := congrFun h i
    change bitAt (encodeNat m) i.val = bitAt (encodeNat n) i.val at hi
    rw [hi]; simp
  have hp : popcount24 (encodeNat (m ^^^ n)) = 0 := by
    rw [popcount24_eq_card, hw]; simp
  have hlt := Nat.xor_lt_two_pow (n := 12) hm hn
  have hz : m ^^^ n = 0 := by
    by_contra hne
    have := golay_min_distance_bound (m ^^^ n) (by omega) hlt
    omega
  have := congrArg (fun k => k ^^^ n) hz
  simpa [Nat.xor_assoc] using this

abbrev Codeword := {w : Fin 24 → Bool // IsGolayWord w}
noncomputable instance : Fintype Codeword := Fintype.ofFinite _

def encodeWord (m : Fin 4096) : Codeword := ⟨word (encodeNat m.val), m.val, m.isLt, rfl⟩

theorem encodeWord_bijective : Function.Bijective encodeWord := by
  constructor
  · intro m n h
    apply Fin.ext
    exact word_encode_injective m.isLt n.isLt (congrArg Subtype.val h)
  · rintro ⟨w, m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, rfl⟩

noncomputable def codeEquiv : Fin 4096 ≃ Codeword := Equiv.ofBijective encodeWord encodeWord_bijective

theorem card_codeword : Fintype.card Codeword = 4096 := by
  rw [← Fintype.card_congr codeEquiv]
  simp

def weight (w : Fin 24 → Bool) : ℕ := (univ.filter (fun i => w i = true)).card
abbrev Octad := {w : Codeword // weight w.val = 8}
noncomputable instance : Fintype Octad := Fintype.ofFinite _

/- The block folds in the existing code file count messages of weight eight. -/
private theorem block_fold_eight (start : ℕ) (l : List ℕ) (a b c d e : ℕ) :
    (l.foldl (fun (a,b,c,d,e) k =>
      let w := popcount24 (encodeNat (start+k))
      if w == 0 then (a+1,b,c,d,e)
      else if w == 8 then (a,b+1,c,d,e)
      else if w == 12 then (a,b,c+1,d,e)
      else if w == 16 then (a,b,c,d+1,e)
      else if w == 24 then (a,b,c,d,e+1)
      else (a,b,c,d,e)) (a,b,c,d,e)).2.1 =
      b + l.countP (fun k => popcount24 (encodeNat (start+k)) == 8) := by
  induction l generalizing a b c d e with
  | nil => simp
  | cons k l ih =>
    simp only [List.foldl_cons, List.countP_cons]
    split_ifs <;> simp_all <;> omega

theorem blockCounts_eight (start : ℕ) : (blockCounts start).2.1 =
    (List.range 256).countP (fun k => popcount24 (encodeNat (start+k)) == 8) := by
  simpa only [blockCounts, Nat.zero_add] using
    block_fold_eight start (List.range 256) 0 0 0 0 0

private theorem total_fold_eight (l : List ℕ) (a b c d e : ℕ) :
    (l.foldl (fun (a,b,c,d,e) blk =>
      let (a',b',c',d',e') := blockCounts (blk*256)
      (a+a',b+b',c+c',d+d',e+e')) (a,b,c,d,e)).2.1 =
      b + (l.map (fun blk => (blockCounts (blk*256)).2.1)).sum := by
  induction l generalizing a b c d e with
  | nil => simp
  | cons k l ih => simp [List.foldl_cons, ih, Nat.add_assoc]

theorem weightCounts_eight : weightCounts.2.1 =
    ((List.range 16).map (fun blk =>
      (List.range 256).countP (fun k => popcount24 (encodeNat (blk*256+k)) == 8))).sum := by
  simpa only [weightCounts, Nat.zero_add, blockCounts_eight] using
    total_fold_eight (List.range 16) 0 0 0 0 0

end LeechCodeCounts
