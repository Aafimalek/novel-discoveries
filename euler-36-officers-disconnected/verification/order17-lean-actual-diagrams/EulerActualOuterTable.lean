import EulerActualOuterPatterns
import EulerAllUsedDiagramData

namespace LatinGap
open EulerAllUsedDiagrams

/-- The exact column data fed to the archived finite enumeration. -/
def outerColumns (U : Coord → Word 6) : List (List ℕ) :=
  [outerColumn U 0,outerColumn U 1,outerColumn U 2,outerColumn U 3]

theorem outerColumns_mem (U : Coord → Word 6)
    (h : ∀ j, outerColumn U j ∈ outerPatterns) :
    outerColumns U ∈ fourChoices patterns := by
  exact List.mem_flatMap.mpr ⟨_,h 0,List.mem_flatMap.mpr ⟨_,h 1,
    List.mem_flatMap.mpr ⟨_,h 2,List.mem_map.mpr ⟨_,h 3,rfl⟩⟩⟩⟩

theorem outerColumns_value (U : Coord → Word 6) (hz : ∀ i, U i i = 0)
    (i j : Coord) : value (ofColumns (outerColumns U)) i.val j.val = (U i j).val := by
  fin_cases i <;> fin_cases j <;> first
  | rfl
  | simpa [ofColumns,indices,value,outerColumns] using (congrArg Fin.val (hz _)).symm

theorem indices_lt_four {i : ℕ} (hi : i ∈ indices) : i < 4 := by
  simp only [indices,List.mem_cons,List.mem_nil_iff,or_false] at hi
  omega

theorem outerColumns_oneOverlap (U : Coord → Word 6) (hz : ∀ i, U i i = 0)
    (h : ∀ i j u v : Coord, i ≠ j → u ≠ v → U i u = U j u → U i v ≠ U j v) :
    oneOverlap (ofColumns (outerColumns U)) = true := by
  unfold oneOverlap
  simp only [List.all_eq_true]
  intro x hx y hy
  split
  next lt =>
    apply decide_eq_true
    let i : Coord := ⟨x,indices_lt_four hx⟩
    let j : Coord := ⟨y,indices_lt_four hy⟩
    have ij : i ≠ j := fun e => (Nat.ne_of_lt lt) (congrArg Fin.val e)
    let M := ofColumns (outerColumns U)
    let same : ℕ → Bool := fun k => value M x k == value M y k
    let L := indices.filter same
    change L.length ≤ 1
    have sameEntry {z : ℕ} (hz' : z ∈ L) :
        ∃ hzB : z < 4, U i ⟨z,hzB⟩ = U j ⟨z,hzB⟩ := by
      obtain ⟨hzI,heq⟩ := List.mem_filter.mp hz'
      let k : Coord := ⟨z,indices_lt_four hzI⟩
      have e : (U i k).val = (U j k).val :=
        (outerColumns_value U hz i k).symm.trans
          ((beq_iff_eq.mp heq).trans (outerColumns_value U hz j k))
      exact ⟨k.isLt,Fin.ext e⟩
    have nodup : L.Nodup := List.Nodup.filter _ (by decide : indices.Nodup)
    by_cases nonempty : ∃ z, z ∈ L
    · obtain ⟨a,ha⟩ := nonempty
      have sub : L ⊆ [a] := by
        intro b hb
        obtain ⟨ha4,hae⟩ := sameEntry ha
        obtain ⟨hb4,hbe⟩ := sameEntry hb
        have eq : b = a := by
          by_contra ne
          exact h i j ⟨a,ha4⟩ ⟨b,hb4⟩ ij (fun e => ne (congrArg Fin.val e).symm) hae hbe
        simp [eq]
      simpa using nodup.length_le_of_subset sub
    · have sub : L ⊆ [] := fun z hzL => (nonempty ⟨z,hzL⟩).elim
      exact (nodup.length_le_of_subset sub).trans (by decide : ([] : List ℕ).length ≤ 1)
  next => rfl

private theorem mem_insertCase {a b : List ℕ} {l : List (List ℕ)} :
    a ∈ insertCase b l ↔ a = b ∨ a ∈ l := by
  induction l with
  | nil => simp [insertCase]
  | cons c l ih =>
    unfold insertCase
    cases e : compare b c with
    | lt => simp
    | eq => have hh := Std.compare_eq_iff_eq.mp e; subst c; simp
    | gt => simp only [List.mem_cons, ih]; tauto

private theorem mem_foldl_insertCase {b : List ℕ} {input start : List (List ℕ)} :
    b ∈ input ∨ b ∈ start → b ∈ input.foldl (fun a d => insertCase d a) start := by
  induction input generalizing start with
  | nil => simp
  | cons c rest ih =>
    intro h
    apply ih
    simp only [List.mem_cons] at h
    rw [mem_insertCase]
    tauto

/-- The exact normalized list emitted by the finite canonicalization
belongs to the audited seventeen-pattern list. -/
theorem outerColumns_canonical_cases (U : Coord → Word 6)
    (hz : ∀ i, U i i = 0) (hpat : ∀ j, outerColumn U j ∈ outerPatterns)
    (h : ∀ i j u v : Coord, i ≠ j → u ≠ v → U i u = U j u → U i v ≠ U j v) :
    canonical (ofColumns (outerColumns U)) ∈ cases := by
  unfold cases
  apply mem_foldl_insertCase
  left
  apply List.mem_map_of_mem
  apply List.mem_filter.mpr
  exact ⟨List.mem_map_of_mem (outerColumns_mem U hpat),outerColumns_oneOverlap U hz h⟩

/-- An actual size-17 all-used minimum-two design produces a valid entry of
the exact canonical enumeration. The audited numeric value of that
enumeration is a separate theorem. -/
theorem all_used_actual_canonical_cases {D : Design 6} (hD : Linear D)
    (hS : Saturated D) (a : Word 6) (ha : a ∈ D)
    (hfreq : ∀ j, freq D (j,a j) = 2) :
    ∃ E : Design 6, Linear E ∧ Saturated E ∧ E.card = D.card ∧
      (fun _ => 0) ∈ E ∧ (∀ j, freq E (j,0) = 2) ∧
      ∃ U : Coord → Word 6, Function.Injective U ∧
        (∀ i, U i ∈ E ∧ U i i = 0 ∧ ∀ j ≠ i, U i j ≠ 0) ∧
        canonical (ofColumns (outerColumns U)) ∈ cases := by
  obtain ⟨E,hE,hm,sz,hz,hf,U,ui,uw,hpat,one⟩ :=
    normalize_all_used_outer_patterns hD hS a ha hfreq
  exact ⟨E,hE,hm,sz,hz,hf,U,ui,uw,outerColumns_canonical_cases U (fun i => (uw i).2.1) hpat one⟩

#print axioms all_used_actual_canonical_cases
#print axioms outerColumns_canonical_cases
end LatinGap
