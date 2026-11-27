import EulerAllUsed
namespace LatinGap
open Finset

theorem minimum_two_has_low {D : Design 6} (hsize : D.card = 17)
    (hm : ∀ x : Label 6, 2 ≤ freq D x) (i : Coord) :
    ∃ a : Fin 6, freq D (i,a) = 2 := by
  by_contra! h
  have hge (a : Fin 6) : 3 ≤ freq D (i,a) := by
    have h0 := hm (i,a)
    exact Nat.lt_of_le_of_ne h0 (Ne.symm (h a))
  have hbound : (∑ a : Fin 6, (3 : ℕ)) ≤ ∑ a : Fin 6, freq D (i,a) :=
    sum_le_sum fun i _ => hge i
  rw [sum_freq,hsize] at hbound
  have bad : ¬ ((∑ _a : Fin 6, (3 : ℕ)) ≤ 17) := by decide
  exact bad hbound

theorem all_used_unique_low {D : Design 6} (hD : Linear D) (hsize : D.card = 17)
    (hm : ∀ x : Label 6, 2 ≤ freq D x)
    (hall : ∀ (i j : Coord) (a b : Fin 6), i ≠ j →
      freq D (i,a) = 2 → freq D (j,b) = 2 → Used D (i,a) (j,b))
    (i : Coord) : ∃! a : Fin 6, freq D (i,a) = 2 := by
  classical
  choose a ha using minimum_two_has_low hsize hm
  have allWord (w : Word 6) (hw : ∀ j, freq D (j,w j) = 2) : w ∈ D :=
    all_used_low_word hD w hw fun i j h => hall i j (w i) (w j) h (hw i) (hw j)
  refine ⟨a i, ha i, ?_⟩
  intro b hb
  let v : Word 6 := Function.update a i b
  have hv : v ∈ D := by
    apply allWord
    intro k
    by_cases e : k = i
    · subst k; simpa [v] using hb
    · simpa [v,Function.update_of_ne e] using ha k
  have twoOthers : ∃ j k : Coord, j ≠ k ∧ j ≠ i ∧ k ≠ i := by
    fin_cases i <;> decide
  obtain ⟨j,k,hjk,hji,hki⟩ := twoOthers
  have equal : v = a := hD hv (allWord a ha) hjk (by simp [v, hji]) (by simp [v, hki])
  simpa [v] using congrFun equal i

#print axioms minimum_two_has_low
#print axioms all_used_unique_low
end LatinGap
