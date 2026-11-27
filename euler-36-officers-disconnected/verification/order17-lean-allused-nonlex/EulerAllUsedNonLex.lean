import EulerMinTwoCandidateAssembly

namespace LatinGap.PairEncoding
open EulerAllUsedDiagrams

def archiveAllUsedDegreeBlock : List (List Int) :=
  (List.ofFn fun g : Coord => g).flatMap fun g =>
    (List.ofFn fun a : Fin 6 => a).flatMap fun a => degreeBlock 2 g a

/-- The main all-used Python generator appends the same 1296 saturation
clauses once more after the anchored base. -/
def archiveRepeatedSaturation : List (List Int) :=
  (List.range 1296).map (fun i => archivedCandidateNumbered (wordAtOrdinal i))

def archivePinnedPrefix (codes : List Nat) (g : Coord) : Nat :=
  ((codes.map fun n => (decimalWord n g).val).foldl max 1) + 1

def archiveMinTwoDegreeOrderPairs (codes : List Nat) (g : Coord) :
    List (Fin 6 × Fin 6) :=
  let start := max (if g=0 then 1 else 2) (archivePinnedPrefix codes g)
  ((List.range (5-start)).attach.map fun ⟨r,hr⟩ =>
    have h : r < 5-start := List.mem_range.mp hr
    (⟨start+r,by omega⟩,⟨start+r+1,by omega⟩)) ++
    if g = 1 then [(0,1)] else []

def archiveAllUsedDegreeOrder (codes : List Nat) : List (List Int) :=
  (List.ofFn fun g : Coord => g).flatMap fun g =>
    (archiveMinTwoDegreeOrderPairs codes g).flatMap fun (a,b) =>
      (thresholdIndices 3).map fun d =>
        [literal (degreeThresholdNumber g a d) false, literal (degreeThresholdNumber g b d) true]

/-- Exact physical clause order, with all clauses through the last
candidate rectangle clause. Later rows are free-label lex symmetry. -/
def archiveAllUsedNonLex (codes : List Nat) : List (List Int) :=
  archivedSupportPrefix ++ archiveProjectionCountBlock ++ archiveAllUsedAnchorUnits ++
  archiveAllUsedDegreeBlock ++ archiveAllUsedDegreeOrder codes ++ archiveRepeatedSaturation ++
  ((List.ofFn fun g : Coord => g).flatMap archiveDegreeExcessCountBlock) ++
  archiveAllUsedPinProfile codes ++ archiveMinTwoCandidateRectangleBlock

theorem archiveAllUsedDegreeBlock_holds {D : Design 6} (lin : Linear D)
    (v : ℕ → Bool) (W : Coord → Word 6) (hv : AllUsedPinCommon D W v)
    (prof : ∀ (g : Coord) (a : Fin 6), freq D (g,a) = if a=0 then 2 else 3) :
    ∀ c ∈ archiveAllUsedDegreeBlock, NumberedHolds v c := by
  intro c hc
  obtain ⟨g,_,hg⟩ := List.mem_flatMap.mp hc
  obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp hg
  apply degreeBlock_holds v 2 g a (freq D (g,a)) ?_ (hv.degrees g a) ?_ c ha
  · have e : (fun b => v (pairNumber (degreeNeighborPair g a b))) =
        fun b => (encode D).pair (degreeNeighborPair g a b) :=
      funext fun b => hv.core (.pair (degreeNeighborPair g a b))
    rw [e,patternCount_eq_freq lin]
  · rw [prof]
    constructor
    · by_cases h : a=0 <;> simp [h]
    · rintro ⟨_,rfl⟩
      rfl

theorem archiveMinTwoDegreeOrderPairs_le {codes : List Nat} {g : Coord} {a b : Fin 6}
    (h : (a,b) ∈ archiveMinTwoDegreeOrderPairs codes g) : a ≤ b := by
  unfold archiveMinTwoDegreeOrderPairs at h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨⟨r,hr⟩,_,e⟩ := List.mem_map.mp h
    rw [← congrArg (fun p : Fin 6 × Fin 6 => p.1 ≤ p.2) e]
    exact Nat.le_succ _
  · split at h
    · have e : (a,b) = (0,1) := by simpa using h
      rw [Prod.mk.inj e |>.1, Prod.mk.inj e |>.2]
      decide
    · contradiction

theorem archiveAllUsedDegreeOrder_holds {D : Design 6} (v : ℕ → Bool)
    (W : Coord → Word 6) (hv : AllUsedPinCommon D W v)
    (prof : ∀ (g : Coord) (a : Fin 6), freq D (g,a) = if a=0 then 2 else 3) :
    ∀ c ∈ archiveAllUsedDegreeOrder (actualRowCodes W), NumberedHolds v c := by
  intro c hc
  obtain ⟨g,_,hg⟩ := List.mem_flatMap.mp hc
  obtain ⟨⟨a,b⟩,hab,hd⟩ := List.mem_flatMap.mp hg
  obtain ⟨d,_,rfl⟩ := List.mem_map.mp hd
  have ab := archiveMinTwoDegreeOrderPairs_le hab
  have mono : freq D (g,a) ≤ freq D (g,b) := by
    rw [prof,prof]
    by_cases ha : a=0
    · by_cases hb : b=0 <;> simp [ha,hb]
    · have hb : b ≠ 0 := by
        intro h; subst b
        exact ha (Fin.ext (Nat.le_zero.mp ab))
      simp [ha,hb]
  by_cases le : d.val ≤ freq D (g,a)
  · exact holds_literal_of_mem (id := degreeThresholdNumber g b d) (b := true) (by simp)
      (by have := (degreeThresholdNumber_bounds g b d).1; omega)
      ((hv.degrees g b d).trans (decide_eq_true (le.trans mono)))
  · exact holds_literal_of_mem (id := degreeThresholdNumber g a d) (b := false) (by simp)
      (by have := (degreeThresholdNumber_bounds g a d).1; omega)
      ((hv.degrees g a d).trans (decide_eq_false le))

theorem archiveRepeatedSaturation_holds {D : Design 6} (sat : Saturated D)
    (v : ℕ → Bool) (W : Coord → Word 6) (hv : AllUsedPinCommon D W v) :
    ∀ c ∈ archiveRepeatedSaturation, NumberedHolds v c := by
  intro c hc
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc
  exact archivedCandidateNumbered_holds D sat v (fun p => hv.core (.pair p)) (wordAtOrdinal i)

/-- Exact normalized all-used CNF prefix before symmetry, with no
additional auxiliary assignment or unproved geometric hypothesis. -/
theorem actual_allUsed_nonLex_holds {D : Design 6} (lin : Linear D) (sat : Saturated D)
    (v : ℕ → Bool) (W : Coord → Word 6) (hv : AllUsedPinCommon D W v)
    (prof : ∀ (g : Coord) (a : Fin 6), freq D (g,a) = if a=0 then 2 else 3) :
    ∀ c ∈ archiveAllUsedNonLex (actualRowCodes W), NumberedHolds v c := by
  intro c hc
  simp only [archiveAllUsedNonLex,List.mem_append] at hc
  rcases hc with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
  · exact hv.support c h
  · exact hv.count c h
  · exact hv.anchors c h
  · exact archiveAllUsedDegreeBlock_holds lin v W hv prof c h
  · exact archiveAllUsedDegreeOrder_holds v W hv prof c h
  · exact archiveRepeatedSaturation_holds sat v W hv c h
  · obtain ⟨g,_,hg⟩ := List.mem_flatMap.mp h
    exact hv.excess g c hg
  · exact hv.pins c h
  · exact geometry_satisfies_archiveMinTwoCandidateRectangleBlock lin sat v
      (fun p => hv.core (.pair p)) hv.degrees c h

#print axioms actual_allUsed_nonLex_holds
end LatinGap.PairEncoding
