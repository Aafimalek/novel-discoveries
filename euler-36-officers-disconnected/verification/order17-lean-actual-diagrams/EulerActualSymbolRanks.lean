import EulerActualCoordinatePerm

namespace LatinGap
open EulerAllUsedDiagrams

private def rankOf (k : Nat) (L : List Nat) : Nat := L.eraseDups.idxOf k + 1

private theorem threeRanks : ∀ a b c : Fin 6,
    rankOf a.val [a.val,b.val,c.val] = 1 ∧
    rankOf b.val [a.val,b.val,c.val] = (if b = a then 1 else 2) ∧
    rankOf c.val [a.val,b.val,c.val] = (if c = a then 1 else
      if c = b then (if b = a then 1 else 2) else if b = a then 2 else 3) := by decide +kernel

def nonzeroColumn (V : Coord → Word 6) (j : Coord) : List Nat :=
  (List.ofFn fun i : Coord => (V i j).val).filter (· != 0)

def archivedRank (V : Coord → Word 6) (i j : Coord) : Nat :=
  if V i j = 0 then 0 else rankOf (V i j).val (nonzeroColumn V j)

private theorem nonzeroColumn_eq (V : Coord → Word 6)
    (hz : ∀ j, V j j = 0) (hn : ∀ i j, j ≠ i → V i j ≠ 0) (j : Coord) :
    nonzeroColumn V j = [(V (outerRows j 0) j).val,
        (V (outerRows j 1) j).val,(V (outerRows j 2) j).val] := by
  have hNE (i j : Coord) (h : j ≠ i) : (V i j).val ≠ 0 :=
    fun e => hn i j h (Fin.ext e)
  fin_cases j <;>
    simp [nonzeroColumn,List.ofFn_succ,outerRows,hz,hNE]

/-- For each column, actual relabeling implements the rank numbers used
by archive canonicalization (zero fixed, then first occurrences). -/
theorem geometric_rank_renaming (V : Coord → Word 6)
    (hz : ∀ j, V j j = 0) (hn : ∀ i j, j ≠ i → V i j ≠ 0) :
    ∃ lab : Coord → Equiv.Perm (Fin 6),
      (∀ j, lab j 0 = 0) ∧ ∀ i j, (lab j (V i j)).val = archivedRank V i j := by
  have single (j : Coord) :
      ∃ lab : Equiv.Perm (Fin 6),
        lab 0 = 0 ∧ ∀ i, (lab (V i j)).val = archivedRank V i j := by
    let a := V (outerRows j 0) j
    let b := V (outerRows j 1) j
    let c := V (outerRows j 2) j
    have na : a ≠ 0 := hn _ j (outerRows_ne j 0).symm
    have nb : b ≠ 0 := hn _ j (outerRows_ne j 1).symm
    have nc : c ≠ 0 := hn _ j (outerRows_ne j 2).symm
    obtain ⟨p,h0,ha,hb,hc⟩ := first_occurrence_pattern (0 : Fin 6) a b c na nb nc
    obtain ⟨ra,rb,rc⟩ := threeRanks a b c
    refine ⟨p,h0,?_⟩
    intro i
    by_cases he : i = j
    · subst i
      simp [archivedRank,hz,h0]
    · obtain ⟨r,hr⟩ := outerRows_cover i j he
      rw [← hr]
      fin_cases r
      · change (p a).val = (if a = 0 then 0 else rankOf a.val (nonzeroColumn V j))
        rw [ite_eq_right na,nonzeroColumn_eq V hz hn,ha,ra]
        rfl
      · change (p b).val = (if b = 0 then 0 else rankOf b.val (nonzeroColumn V j))
        rw [ite_eq_right nb,nonzeroColumn_eq V hz hn,hb,rb]
        split <;> rfl
      · change (p c).val = (if c = 0 then 0 else rankOf c.val (nonzeroColumn V j))
        rw [ite_eq_right nc,nonzeroColumn_eq V hz hn,hc,rc]
        by_cases ca : c = a <;> by_cases cb : c = b <;> by_cases ba : b = a <;> simp [ca,cb,ba]
  choose lab h0 h using single
  exact ⟨lab,h0,fun i j => h j i⟩

#print axioms geometric_rank_renaming
end LatinGap
