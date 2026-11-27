import EulerSupportValuation

namespace LatinGap.PairEncoding

def archivedCoordPairs : List CoordPair :=
  [⟨(0,1),by decide⟩,⟨(0,2),by decide⟩,⟨(0,3),by decide⟩,
   ⟨(1,2),by decide⟩,⟨(1,3),by decide⟩,⟨(2,3),by decide⟩]

theorem archivedCoordPairs_complete : ∀ ij : CoordPair, ij ∈ archivedCoordPairs := by decide +kernel

def wordAtOrdinal (i : ℕ) : Word 6 :=
  fun c => ⟨(i/(6^(3-c.val))) % 6, by omega⟩

def archivedCandidateNumbered (w : Word 6) : List ℤ :=
  archivedCoordPairs.map (fun ij => literal (pairNumber (candidatePair w ij)) true)

def archivedPairKeys : List (PairKey 6) :=
  archivedCoordPairs.flatMap fun ij =>
    (List.ofFn (fun a : Fin 6 => a)).flatMap fun a =>
      (List.ofFn (fun b : Fin 6 => b)).map fun b =>
        ⟨ij.val.1,ij.val.2,ij.prop,a,b⟩

/-- Original first 31,752 signed clauses for the non-triple base:
one saturation clause per word followed by each typed support block. -/
def archivedSupportPrefix : List (List ℤ) :=
  ((List.range 1296).map (fun i => archivedCandidateNumbered (wordAtOrdinal i))) ++
    (archivedPairKeys.flatMap archiveSupportBlock)

theorem archivedCandidateNumbered_holds (D : Design 6) (sat : Saturated D)
    (v : ℕ → Bool) (hpair : ∀ p : PairKey 6, v (pairNumber p) = (encode D).pair p)
    (w : Word 6) : NumberedHolds v (archivedCandidateNumbered w) := by
  have pack (i j : Coord) (h : i<j) (used : Used D (i,w i) (j,w j)) :
      NumberedHolds v (archivedCandidateNumbered w) := by
    let ij : CoordPair := ⟨(i,j),h⟩
    let p := candidatePair w ij
    have pos : 0<pairNumber p := by have := (pairNumber_bounds p).1; omega
    have hit : v (pairNumber p)=true :=
      (hpair p).trans ((pair_encode D p).mpr used)
    have mem : literal (pairNumber p) true ∈ archivedCandidateNumbered w :=
      List.mem_map.mpr ⟨ij,archivedCoordPairs_complete ij,rfl⟩
    exact holds_literal_of_mem mem pos hit
  obtain ⟨i,j,hij⟩ := sat w
  by_cases h : i<j
  · exact pack i j h hij
  · have h' : j<i := lt_of_le_of_ne (le_of_not_gt h) (used_coord_ne hij).symm
    exact pack j i h' (used_symm hij)

theorem geometry_satisfies_archived_support_prefix (D : Design 6)
    (linear : Linear D) (sat : Saturated D)
    (v : ℕ → Bool)
    (hword : ∀ w : Word 6, v (wordNumber w) = (encode D).select w)
    (hpair : ∀ p : PairKey 6, v (pairNumber p) = (encode D).pair p) :
    ∃ w : ℕ → Bool,
      (∀ i, i≤1512 ∨ 9073≤i → w i=v i) ∧
      ∀ c ∈ archivedSupportPrefix, NumberedHolds w c := by
  obtain ⟨w,keep,support⟩ := geometry_satisfies_archived_support_blocks D linear v hword hpair
  have pairNow (p : PairKey 6) : w (pairNumber p) = (encode D).pair p :=
    (keep _ (Or.inl (pairNumber_bounds p).2)).trans (hpair p)
  refine ⟨w,keep,?_⟩
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    exact archivedCandidateNumbered_holds D sat w pairNow (wordAtOrdinal i)
  · obtain ⟨p,_,h⟩ := List.mem_flatMap.mp h
    exact support p c h

#print axioms geometry_satisfies_archived_support_prefix

end LatinGap.PairEncoding
