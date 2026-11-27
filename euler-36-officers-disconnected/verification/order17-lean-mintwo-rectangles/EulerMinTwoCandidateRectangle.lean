import EulerArchivedOverlaps

namespace LatinGap.PairEncoding

/-- Exact Python minimum-two shared-neighbor rectangle clause.
In the original (dx,dy) loop, d=6-dx-dy never exceeds 2, and
d+1>2 holds precisely at dx=dy=2. -/
def minTwoCandidateRectangleClause (p : PairKey 6) (s : Opposite p.i p.j)
    (c t : Fin 6) : List ℤ :=
  [literal (pairNumber p) true,
   literal (pairNumber (orientPair p.i s.left s.il p.a c)) true,
   literal (pairNumber (orientPair p.j s.left s.jl p.b c)) true,
   literal (degreeThresholdNumber p.i p.a 3) true,
   literal (degreeThresholdNumber p.j p.b 3) true,
   literal (pairNumber (orientPair p.i s.right s.ir p.a t)) false,
   literal (pairNumber (orientPair p.j s.right s.jr p.b t)) false,
   literal (degreeThresholdNumber s.left c 3) true]

def archiveMinTwoCandidateRectangleBlock : List (List ℤ) :=
  archivedCoordPairs.flatMap fun ⟨(i,j),h⟩ =>
    (opposites i j).flatMap fun s =>
      singleLabels.flatMap fun a => singleLabels.flatMap fun b =>
        singleLabels.flatMap fun c =>
          singleLabels.map fun t => minTwoCandidateRectangleClause ⟨i,j,h,a,b⟩ s c t

/-- With an unused pair of endpoints of degree at most two, an unblocked
label on one side and a common used neighbor on the other imply that
the unblocked label has at least three used neighbors. -/
theorem minTwo_candidateRectangle_degree {D : Design 6} (lin : Linear D)
    (sat : Saturated D) (p : PairKey 6) (s : Opposite p.i p.j)
    (c t : Fin 6) (hpair : ¬ Used D (p.i,p.a) (p.j,p.b))
    (hx : freq D (p.i,p.a) ≤ 2) (hy : freq D (p.j,p.b) ≤ 2)
    (hc1 : ¬ Used D (p.i,p.a) (s.left,c)) (hc2 : ¬ Used D (p.j,p.b) (s.left,c))
    (ht1 : Used D (p.i,p.a) (s.right,t)) (ht2 : Used D (p.j,p.b) (s.right,t)) :
    3 ≤ freq D (s.left,c) := by
  have hc := (mem_candidates s.il s.jl).2 ⟨hc1,hc2⟩
  have hshared := card_candidates_shared lin s.ir s.jr ht1 ht2
  have hall := card_candidates_le_freq lin s.different (fun b hb =>
    candidate_rectangle sat (ne_of_lt p.increasing) s.il s.ir s.jl s.jr s.different hpair hc hb)
  omega

theorem minTwoCandidateRectangleClause_holds {D : Design 6} (lin : Linear D)
    (sat : Saturated D) (v : ℕ → Bool)
    (hP : ∀ p : PairKey 6, v (pairNumber p) = (encode D).pair p)
    (hT : ∀ (g : Coord) (a : Fin 6) (d : Fin 7),
      v (degreeThresholdNumber g a d) = decide (d.val ≤ freq D (g,a)))
    (p : PairKey 6) (s : Opposite p.i p.j) (c t : Fin 6) :
    NumberedHolds v (minTwoCandidateRectangleClause p s c t) := by
  classical
  let C := minTwoCandidateRectangleClause p s c t
  by_contra no
  have ht (g : Coord) (a : Fin 6) (hm : literal (degreeThresholdNumber g a 3) true ∈ C) :
      ¬ 3 ≤ freq D (g,a) := by
    intro hz
    apply no
    refine holds_literal_of_mem hm (by have := (degreeThresholdNumber_bounds g a 3).1; omega) ?_
    rw [hT]
    exact decide_eq_true hz
  have hpos (q : PairKey 6) (hm : literal (pairNumber q) true ∈ C) : v (pairNumber q) ≠ true :=
    fun h => no (holds_literal_of_mem hm (by have := (pairNumber_bounds q).1; omega) h)
  have hneg (q : PairKey 6) (hm : literal (pairNumber q) false ∈ C) : v (pairNumber q) = true := by
    cases e : v (pairNumber q)
    · exact (no (holds_literal_of_mem hm (by have := (pairNumber_bounds q).1; omega) e)).elim
    · rfl
  have baseUnused : ¬ Used D (p.i,p.a) (p.j,p.b) := fun e =>
    hpos p (by simp [C,minTwoCandidateRectangleClause]) ((hP p).trans ((pair_encode D p).2 e))
  have lowLeft : freq D (p.i,p.a) ≤ 2 :=
    Nat.le_of_lt_succ (Nat.lt_of_not_ge (ht p.i p.a (by simp [C,minTwoCandidateRectangleClause])))
  have lowRight : freq D (p.j,p.b) ≤ 2 :=
    Nat.le_of_lt_succ (Nat.lt_of_not_ge (ht p.j p.b (by simp [C,minTwoCandidateRectangleClause])))
  have c1 : ¬ Used D (p.i,p.a) (s.left,c) := fun e => hpos (orientPair p.i s.left s.il p.a c)
    (by simp [C,minTwoCandidateRectangleClause])
    ((hP _).trans ((orientPair_used D _ _ _ _ _).2 e))
  have c2 : ¬ Used D (p.j,p.b) (s.left,c) := fun e => hpos (orientPair p.j s.left s.jl p.b c)
    (by simp [C,minTwoCandidateRectangleClause])
    ((hP _).trans ((orientPair_used D _ _ _ _ _).2 e))
  have t1 : Used D (p.i,p.a) (s.right,t) := (orientPair_used D p.i s.right s.ir p.a t).1
    ((hP _).symm.trans (hneg _ (by simp [C,minTwoCandidateRectangleClause])))
  have t2 : Used D (p.j,p.b) (s.right,t) := (orientPair_used D p.j s.right s.jr p.b t).1
    ((hP _).symm.trans (hneg _ (by simp [C,minTwoCandidateRectangleClause])))
  exact ht s.left c (by simp [C,minTwoCandidateRectangleClause])
    (minTwo_candidateRectangle_degree lin sat p s c t baseUnused lowLeft lowRight c1 c2 t1 t2)

/-- One correct numeric valuation satisfies every clause of the exact
standard min-two rectangle-propagation family. -/
theorem geometry_satisfies_archiveMinTwoCandidateRectangleBlock {D : Design 6}
    (lin : Linear D) (sat : Saturated D) (v : ℕ → Bool)
    (hP : ∀ p : PairKey 6, v (pairNumber p) = (encode D).pair p)
    (hT : ∀ (g : Coord) (a : Fin 6) (d : Fin 7),
      v (degreeThresholdNumber g a d) = decide (d.val ≤ freq D (g,a))) :
    ∀ c ∈ archiveMinTwoCandidateRectangleBlock, NumberedHolds v c := by
  intro c hc
  obtain ⟨⟨⟨i,j⟩,ij⟩,_,hs⟩ := List.mem_flatMap.mp hc
  obtain ⟨s,_,ha⟩ := List.mem_flatMap.mp hs
  obtain ⟨a,_,hb⟩ := List.mem_flatMap.mp ha
  obtain ⟨b,_,hz⟩ := List.mem_flatMap.mp hb
  obtain ⟨z,_,ht⟩ := List.mem_flatMap.mp hz
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp ht
  exact minTwoCandidateRectangleClause_holds lin sat v hP hT ⟨i,j,ij,a,b⟩ s z t

#print axioms minTwo_candidateRectangle_degree
#print axioms geometry_satisfies_archiveMinTwoCandidateRectangleBlock
end LatinGap.PairEncoding
