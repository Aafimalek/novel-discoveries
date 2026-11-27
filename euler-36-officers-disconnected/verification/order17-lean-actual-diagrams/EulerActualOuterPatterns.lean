import EulerAllUsedFrequencies
import EulerNormalizePattern

namespace LatinGap

/-- The three ordered row indices other than the low row in a column. -/
def outerRows (j : Coord) (r : Fin 3) : Coord :=
  if r.val < j.val then ⟨r.val,by omega⟩ else ⟨r.val + 1,by omega⟩

theorem outerRows_ne : ∀ j r, outerRows j r ≠ j := by decide
theorem outerRows_cover : ∀ i j : Coord, i ≠ j → ∃ r : Fin 3, outerRows j r = i := by decide

def outerColumn (W : Coord → Word 6) (j : Coord) : List ℕ :=
  List.ofFn fun r : Fin 3 => (W (outerRows j r) j).val

def outerPatterns : List (List ℕ) := [[1,1,1],[1,1,2],[1,2,1],[1,2,2],[1,2,3]]

private theorem column_permutation (a : Word 6) (W : Coord → Word 6)
    (only : ∀ i j : Coord, j ≠ i → W i j ≠ a j) (j : Coord) :
    ∃ p : Equiv.Perm (Fin 6), p (a j) = 0 ∧
      outerColumn (fun i k => p (W i k)) j ∈ outerPatterns := by
  let A := W (outerRows j 0) j
  let B := W (outerRows j 1) j
  let C := W (outerRows j 2) j
  obtain ⟨p,h0,h1,h2,h3⟩ :=
    first_occurrence_pattern (a j) A B C
      (only _ j (outerRows_ne j 0).symm)
      (only _ j (outerRows_ne j 1).symm)
      (only _ j (outerRows_ne j 2).symm)
  refine ⟨p,h0,?_⟩
  have exactColumn : outerColumn (fun i k => p (W i k)) j =
      [(p A).val,(p B).val,(p C).val] := by rfl
  rw [exactColumn,h1,h2,h3]
  by_cases e : B = A
  · by_cases h : C = A
    · simp [outerPatterns,e,h]
    · have h' : C ≠ B := fun he => h (he.trans e)
      simp [outerPatterns,e,h,h']
  · by_cases h : C = A
    · simp [outerPatterns,e,h]
    · by_cases h' : C = B <;> simp [outerPatterns,e,h,h']

/-- The actual four outer words can be normalized simultaneously in each
column, keeping the prescribed central word at zero and preserving all
geometric hypotheses. Any two outer rows agree in at most one column. -/
theorem normalize_all_used_outer_patterns {D : Design 6} (hD : Linear D)
    (hS : Saturated D) (a : Word 6) (ha : a ∈ D)
    (hfreq : ∀ j, freq D (j,a j) = 2) :
    ∃ E : Design 6, Linear E ∧ Saturated E ∧ E.card = D.card ∧
      (fun _ => 0) ∈ E ∧ (∀ j, freq E (j,0) = 2) ∧
      ∃ U : Coord → Word 6, Function.Injective U ∧
        (∀ i, U i ∈ E ∧ U i i = 0 ∧ ∀ j ≠ i, U i j ≠ 0) ∧
        (∀ j, outerColumn U j ∈ outerPatterns) ∧
        (∀ i j u v : Coord, i ≠ j → u ≠ v → U i u = U j u → U i v ≠ U j v) := by
  classical
  obtain ⟨W,hW,prop⟩ := all_used_four_outer_words hD a ha hfreq
  have hp (j : Coord) := column_permutation a W (fun i k => (prop i).2.2 k) j
  choose lab hzero hpattern using hp
  let E := renameDesign (Equiv.refl _) lab D
  let U (i : Coord) : Word 6 := renameWords (Equiv.refl _) lab (W i)
  have hlin := renameDesign_linear hD (Equiv.refl _) lab
  have mem (i : Coord) : U i ∈ E := Finset.mem_map.mpr ⟨W i,(prop i).1,rfl⟩
  have hinj : Function.Injective U := (renameWords (Equiv.refl _) lab).injective.comp hW
  refine ⟨E,hlin,renameDesign_saturated hS _ _,renameDesign_card _ _ _,?_,?_,
    U,hinj,?_,?_,?_⟩
  · refine Finset.mem_map.mpr ⟨a,ha,?_⟩
    funext j
    exact hzero j
  · intro j
    have h := renameDesign_freq (Equiv.refl _) lab D j (a j)
    rw [hzero j] at h
    exact h.trans (hfreq j)
  · intro i
    refine ⟨mem i,?_,?_⟩
    · change lab i (W i i) = 0
      rw [(prop i).2.1,hzero i]
    · intro j hj e
      change lab j (W i j) = 0 at e
      rw [← hzero j] at e
      exact (prop i).2.2 j hj ((lab j).injective e)
  · intro j
    have e : outerColumn U j = outerColumn (fun i k => lab j (W i k)) j := rfl
    rw [e]
    exact hpattern j
  · intro i j u v nij nuv e t
    exact nij (hinj (hlin (mem i) (mem j) nuv e t))

#print axioms normalize_all_used_outer_patterns
end LatinGap
