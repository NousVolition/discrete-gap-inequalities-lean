import ConwayMoves

namespace ConwayIncidence

open GolayMathieu ConwayMoves LeechSymmetry LeechLattice

def twoSign (b : Bool) (a : ℤ) := if b then -a else a

def rawPair (i j : Point) : Perm := Equiv.swap 0 i * Equiv.swap 1 ((Equiv.swap 0 i) j)

theorem move_indices (i j : Point) (hn : j ≠ i) (b : Bool) :
    ∃ g : Aut, ∀ x : Lattice, (g x).val 0 = x.val i ∧ (g x).val 1 = twoSign b (x.val j) := by
  have ok : ∀ a c : Point, c ≠ a → rawPair a c 0 = a ∧ rawPair a c 1 = c := by decide +kernel
  let f := (Fin.castLEEmb (by decide : 4 ≤ 24)).trans (rawPair i j).toEmbedding
  obtain ⟨p, hp, h⟩ := four_transitive f
  have h0 : p 0 = i := (h 0).trans (ok i j hn).1
  have h1 : p 1 = j := (h 1).trans (ok i j hn).2
  obtain ⟨w, hw⟩ := four_signs (fun a => if a = 1 then b else false)
  have hw0 : w.val 0 = false := hw 0
  have hw1 : w.val 1 = b := by exact (hw 1).trans (by rfl)
  refine ⟨signAut w * permutationAut p hp, fun x => ?_⟩
  change (if w.val 0 then -x.val (p 0) else x.val (p 0)) = _ ∧
    (if w.val 1 then -x.val (p 1) else x.val (p 1)) = _
  simp [hw0,hw1,h0,h1,twoSign]

end ConwayIncidence
