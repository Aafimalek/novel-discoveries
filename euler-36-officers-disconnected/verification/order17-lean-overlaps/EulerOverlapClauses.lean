import EulerCommonCounterAssembly
import EulerGeometryValuation

namespace LatinGap.PairEncoding

def orientPair (i j : Coord) (h : i ≠ j) (a b : Fin 6) : PairKey 6 :=
  if l : i < j then ⟨i,j,l,a,b⟩ else ⟨j,i,lt_of_le_of_ne (le_of_not_gt l) h.symm,b,a⟩

theorem orientPair_used (D : Design 6) (i j : Coord) (h : i ≠ j) (a b : Fin 6) :
    (encode D).pair (orientPair i j h a b) = true ↔ Used D (i,a) (j,b) := by
  unfold orientPair
  split
  · exact pair_encode D _
  · exact (pair_encode D _).trans ⟨used_symm,used_symm⟩

def overlapAllow (p : PairKey 6) : List ℤ :=
  [literal (pairNumber p) true,
   literal (degreeThresholdNumber p.i p.a 3) true,
   literal (degreeThresholdNumber p.j p.b 3) true]

def overlapNeg (p : PairKey 6) (k : Coord) (hi : p.i ≠ k) (hj : p.j ≠ k)
    (a : Fin 6) : List ℤ :=
  [literal (pairNumber (orientPair p.i k hi p.a a)) false,
   literal (pairNumber (orientPair p.j k hj p.b a)) false]

def overlapClause (p : PairKey 6) (xs :
    List ((k : Coord) ×' (_ : p.i ≠ k) ×' (_ : p.j ≠ k) ×' Fin 6)) : List ℤ :=
  overlapAllow p ++ xs.flatMap (fun ⟨k,hi,hj,a⟩ => overlapNeg p k hi hj a)

def Overlap (D : Design 6) (p : PairKey 6) (k : Coord) (a : Fin 6) : Prop :=
  Used D (p.i,p.a) (k,a) ∧ Used D (p.j,p.b) (k,a)

def UnusedLow (D : Design 6) (p : PairKey 6) : Prop :=
  ¬ Used D (p.i,p.a) (p.j,p.b) ∧ freq D (p.i,p.a) = 2 ∧ freq D (p.j,p.b) = 2

theorem overlapClause_holds (D : Design 6) (v : ℕ → Bool)
    (hP : ∀ p : PairKey 6, v (pairNumber p) = (encode D).pair p)
    (hT : ∀ (g : Coord) (a : Fin 6) (d : Fin 7),
      v (degreeThresholdNumber g a d) = decide (d.val ≤ freq D (g,a)))
    (hm : ∀ x : Label 6, 2 ≤ freq D x) (p : PairKey 6)
    (xs : List ((k : Coord) ×' (_ : p.i ≠ k) ×' (_ : p.j ≠ k) ×' Fin 6))
    (rule : UnusedLow D p → ¬ ∀ x ∈ xs, Overlap D p x.1 x.2.2.2) :
    NumberedHolds v (overlapClause p xs) := by
  classical
  by_cases hp : Used D (p.i,p.a) (p.j,p.b)
  · exact holds_literal_of_mem (b := true) (by simp [overlapClause, overlapAllow])
      (by have := (pairNumber_bounds p).1; omega) ((hP p).trans ((pair_encode D p).2 hp))
  by_cases hA : 3 ≤ freq D (p.i,p.a)
  · exact holds_literal_of_mem (b := true) (by simp [overlapClause, overlapAllow])
      (by have := (degreeThresholdNumber_bounds p.i p.a 3).1; omega)
      ((hT p.i p.a 3).trans (by simpa using hA))
  by_cases hB : 3 ≤ freq D (p.j,p.b)
  · exact holds_literal_of_mem (b := true) (by simp [overlapClause, overlapAllow])
      (by have := (degreeThresholdNumber_bounds p.j p.b 3).1; omega)
      ((hT p.j p.b 3).trans (by simpa using hB))
  have hlow : UnusedLow D p := ⟨hp,by have := hm (p.i,p.a); omega,
    by have := hm (p.j,p.b); omega⟩
  obtain ⟨⟨k,hi,hj,a⟩,hn⟩ := not_forall.mp (rule hlow)
  have mem : ⟨k,hi,hj,a⟩ ∈ xs := by by_contra no; exact hn (fun h => (no h).elim)
  have hmiss : ¬ Overlap D p k a := fun ho => hn (fun _ => ho)
  have appendHit (q : PairKey 6)
      (showMem : literal (pairNumber q) false ∈ overlapNeg p k hi hj a)
      (showBit : (encode D).pair q = false) : NumberedHolds v (overlapClause p xs) := by
    apply holds_literal_of_mem (b := false) _ _ ((hP q).trans showBit)
    · apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨_,mem,showMem⟩
    · have := (pairNumber_bounds q).1
      omega
  rcases not_and_or.mp hmiss with ha | hb
  · refine appendHit (orientPair p.i k hi p.a a) (by simp [overlapNeg]) ?_
    cases e : (encode D).pair (orientPair p.i k hi p.a a)
    · rfl
    · exact (ha ((orientPair_used D _ _ hi _ _).1 e)).elim
  · refine appendHit (orientPair p.j k hj p.b a) (by simp [overlapNeg]) ?_
    cases e : (encode D).pair (orientPair p.j k hj p.b a)
    · rfl
    · exact (hb ((orientPair_used D _ _ hj _ _).1 e)).elim

#print axioms overlapClause_holds
end LatinGap.PairEncoding
