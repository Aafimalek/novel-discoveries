import EulerOverlapCases
import EulerArchivePrefix

namespace LatinGap.PairEncoding

inductive OverlapCase where
  | q2 | double | one | zero
  deriving DecidableEq, Repr

/-- An ordered pair of other coordinates of the selected unused pair. -/
structure Opposite (i j : Coord) where
  left : Coord
  right : Coord
  il : i ≠ left
  jl : j ≠ left
  ir : i ≠ right
  jr : j ≠ right
  different : left ≠ right

def Opposite.flip {i j : Coord} (s : Opposite i j) : Opposite i j :=
  ⟨s.right,s.left,s.ir,s.jr,s.il,s.jl,s.different.symm⟩

def opposites (i j : Coord) : List (Opposite i j) :=
  archivedCoordPairs.flatMap fun ⟨(k,l),h⟩ =>
    if ne : i ≠ k ∧ j ≠ k ∧ i ≠ l ∧ j ≠ l then
      let s : Opposite i j := ⟨k,l,ne.1,ne.2.1,ne.2.2.1,ne.2.2.2,ne_of_lt h⟩
      [s,s.flip]
    else []

abbrev OverlapEntry (p : PairKey 6) :=
  (k : Coord) ×' (_ : p.i ≠ k) ×' (_ : p.j ≠ k) ×' Fin 6

def singleLabels : List (Fin 6) := List.ofFn fun a => a
def increasingLabels : List (Fin 6 × Fin 6) :=
  singleLabels.flatMap fun a => singleLabels.filterMap fun b => if a < b then some (a,b) else none

def overlapTuples (case : OverlapCase) (p : PairKey 6) (s : Opposite p.i p.j) :
    List (List (OverlapEntry p)) :=
  let L : Fin 6 → OverlapEntry p := fun a => ⟨s.left,s.il,s.jl,a⟩
  let R : Fin 6 → OverlapEntry p := fun a => ⟨s.right,s.ir,s.jr,a⟩
  match case with
  | .q2 => increasingLabels.flatMap fun (a,b) => singleLabels.map fun c => [L a,L b,R c]
  | .double => increasingLabels.map fun (a,b) => [L a,L b]
  | .one => (increasingLabels.map fun (a,b) => [L a,L b]) ++
      if s.left < s.right then singleLabels.flatMap fun a => singleLabels.map fun b => [L a,R b] else []
  | .zero => singleLabels.map fun a => [L a]

def archivedOverlapBlock (case : OverlapCase) : List (List ℤ) :=
  archivedCoordPairs.flatMap fun ⟨(i,j),h⟩ => (opposites i j).flatMap fun s =>
    singleLabels.flatMap fun a => singleLabels.flatMap fun b =>
      let p := (⟨i,j,h,a,b⟩ : PairKey 6)
      (overlapTuples case p s).map (overlapClause p)

def NoTwoOnOneSide (D : Design 6) : Prop :=
  ∀ (p : PairKey 6) (k : Coord) (a b : Fin 6), UnusedLow D p →
    a ≠ b → Overlap D p k a → ¬ Overlap D p k b

def NoTwoSides (D : Design 6) : Prop :=
  ∀ (p : PairKey 6) (k l : Coord) (a b : Fin 6), UnusedLow D p →
    k ≠ l → Overlap D p k a → ¬ Overlap D p l b

def NoOverlap (D : Design 6) : Prop :=
  ∀ (p : PairKey 6) (k : Coord) (a : Fin 6), UnusedLow D p → ¬ Overlap D p k a

def OverlapInvariant (D : Design 6) : OverlapCase → Prop
  | .q2 => True
  | .double => NoTwoOnOneSide D
  | .one => NoTwoOnOneSide D ∧ NoTwoSides D
  | .zero => NoOverlap D

theorem increasingLabels_increasing {a b : Fin 6} (h : (a,b) ∈ increasingLabels) :
    a < b := by
  obtain ⟨x,_,hx⟩ := List.mem_flatMap.mp h
  obtain ⟨y,_,hy⟩ := List.mem_filterMap.mp hx
  split at hy
  · simp only [Option.some.injEq,Prod.mk.injEq] at hy
    rcases hy with ⟨rfl,rfl⟩
    assumption
  · contradiction

theorem overlapTuples_forbid {D : Design 6} (hD : Linear D) (hS : Saturated D)
    (size : D.card = 17) (hm : ∀ x : Label 6, 2 ≤ freq D x)
    (case : OverlapCase) (inv : OverlapInvariant D case) (p : PairKey 6)
    (s : Opposite p.i p.j) {xs : List (OverlapEntry p)} (hx : xs ∈ overlapTuples case p s)
    (low : UnusedLow D p) :
    ¬ ∀ x ∈ xs, Overlap D p x.1 x.2.2.2 := by
  intro all
  have twoLeft {ys : List (OverlapEntry p)}
      (hh : ys ∈ increasingLabels.map fun (a,b) =>
        [⟨s.left,s.il,s.jl,a⟩,⟨s.left,s.il,s.jl,b⟩])
      (hall : ∀ x ∈ ys, Overlap D p x.1 x.2.2.2) (no : NoTwoOnOneSide D) : False := by
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := List.mem_map.mp hh
    exact no p s.left a b low (ne_of_lt (increasingLabels_increasing hab))
      (hall ⟨s.left,s.il,s.jl,a⟩ (by simp)) (hall ⟨s.left,s.il,s.jl,b⟩ (by simp))
  cases case with
  | q2 =>
    obtain ⟨⟨a,b⟩,hab,hh⟩ := List.mem_flatMap.mp hx
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hh
    exact two_overlaps_forbid_opposite hD hS size hm low s.il s.jl s.ir s.jr s.different
      (ne_of_lt (increasingLabels_increasing hab)) (all ⟨s.left,s.il,s.jl,a⟩ (by simp)) (all ⟨s.left,s.il,s.jl,b⟩ (by simp))
      (all ⟨s.right,s.ir,s.jr,c⟩ (by simp))
  | double => exact twoLeft hx all inv
  | one =>
    change NoTwoOnOneSide D ∧ NoTwoSides D at inv
    simp only [overlapTuples,List.mem_append] at hx
    rcases hx with hh | hh
    · exact twoLeft hh all inv.1
    · split at hh
      · obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp hh
        obtain ⟨b,_,rfl⟩ := List.mem_map.mp ha
        exact inv.2 p s.left s.right a b low s.different (all ⟨s.left,s.il,s.jl,a⟩ (by simp)) (all ⟨s.right,s.ir,s.jr,b⟩ (by simp))
      · simp at hh
  | zero =>
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hx
    exact inv p s.left a low (all ⟨s.left,s.il,s.jl,a⟩ (by simp))

/-- All archived min-two overlap-exclusion clauses are correct for their
global overlap invariants; the 4x3 q2 exclusion requires no invariant. -/
theorem geometry_satisfies_archived_overlap_block {D : Design 6}
    (hD : Linear D) (hS : Saturated D) (size : D.card = 17)
    (hm : ∀ x : Label 6, 2 ≤ freq D x) (case : OverlapCase)
    (inv : OverlapInvariant D case) (v : ℕ → Bool)
    (hP : ∀ p : PairKey 6, v (pairNumber p) = (encode D).pair p)
    (hT : ∀ (g : Coord) (a : Fin 6) (d : Fin 7),
      v (degreeThresholdNumber g a d) = decide (d.val ≤ freq D (g,a))) :
    ∀ c ∈ archivedOverlapBlock case, NumberedHolds v c := by
  intro c hc
  obtain ⟨⟨⟨i,j⟩,hij⟩,_,hs⟩ := List.mem_flatMap.mp hc
  obtain ⟨s,_,ha⟩ := List.mem_flatMap.mp hs
  obtain ⟨a,_,hb⟩ := List.mem_flatMap.mp ha
  obtain ⟨b,_,hx⟩ := List.mem_flatMap.mp hb
  obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hx
  exact overlapClause_holds D v hP hT hm _ _ (overlapTuples_forbid hD hS size hm case inv _ s hxs)

#print axioms geometry_satisfies_archived_overlap_block
end LatinGap.PairEncoding

namespace LatinGap.PairEncoding

/-- The global overlap split, before naming pinned words and sorting free
labels. In the double branch the excluded same-side double is global. -/
theorem minTwo_overlap_exhaustive (D : Design 6) :
    (∀ p : PairKey 6, ¬ UnusedLow D p) ∨
    (∃ (p : PairKey 6) (k : Coord) (a b : Fin 6),
      UnusedLow D p ∧ a ≠ b ∧ Overlap D p k a ∧ Overlap D p k b) ∨
    (NoTwoOnOneSide D ∧ ∃ (p : PairKey 6) (k l : Coord) (a b : Fin 6),
      UnusedLow D p ∧ k ≠ l ∧ Overlap D p k a ∧ Overlap D p l b) ∨
    (NoTwoOnOneSide D ∧ NoTwoSides D ∧ ∃ (p : PairKey 6) (k : Coord) (a : Fin 6),
      UnusedLow D p ∧ Overlap D p k a) ∨
    (NoOverlap D ∧ ∃ p : PairKey 6, UnusedLow D p) := by
  classical
  by_cases hp : ∀ p : PairKey 6, ¬ UnusedLow D p
  · exact Or.inl hp
  right
  by_cases h2 : NoTwoOnOneSide D
  · right
    by_cases hs : NoTwoSides D
    · right
      by_cases hn : NoOverlap D
      · right
        exact ⟨hn,by push Not at hp; exact hp⟩
      · left
        refine ⟨h2,hs,?_⟩
        unfold NoOverlap at hn
        push Not at hn
        exact hn
    · left
      refine ⟨h2,?_⟩
      unfold NoTwoSides at hs
      push Not at hs
      exact hs
  · left
    unfold NoTwoOnOneSide at h2
    push Not at h2
    exact h2

#print axioms minTwo_overlap_exhaustive
end LatinGap.PairEncoding
