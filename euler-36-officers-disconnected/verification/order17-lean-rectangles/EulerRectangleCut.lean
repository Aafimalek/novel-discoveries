import EulerDegreeThreshold

namespace LatinGap.PairEncoding
open Finset
open scoped BigOperators

/-- An unused pair leaves a candidate rectangle of side at least r.
Selecting r labels on one remaining side, each has degree at least r;
all other labels in that coordinate meet the original minimum. -/
theorem rectangle_size_lower {D : Design 6} (hD : Linear D) (hM : Saturated D)
    {x y : Label 6} (hxy : x.1 ≠ y.1) (hu : ¬ Used D x y) (r m : ℕ)
    (hr : r + freq D x + freq D y ≤ 6) (hm : ∀ z : Label 6, m ≤ freq D z) :
    r*r + (6-r)*m ≤ D.card := by
  have hpair : ∀ i j : Coord, i ≠ j →
      ∃ k l : Coord, i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l := by decide
  obtain ⟨j,k,hxj,hxk,hyj,hyk,hjk⟩ := hpair x.1 y.1 hxy
  have hJ := card_candidates_lower hD (x := x) (y := y) hxj hyj
  have hK := card_candidates_lower hD (x := x) (y := y) hxk hyk
  obtain ⟨S,hS,hc⟩ := exists_subset_card_eq (s := candidates D x y j) (n := r) (by omega)
  have hcr (a : Fin 6) (ha : a ∈ S) : r ≤ freq D (j,a) := by
    have hbound := card_candidates_le_freq hD (x := x) (y := y) hjk
      (fun b hb => candidate_rectangle hM hxy hxj hxk hyj hyk hjk hu (hS ha) hb)
    omega
  let T : Finset (Fin 6) := univ \ S
  have hdT : T.card = 6-r := by
    simp [T,card_sdiff_of_subset (subset_univ S),hc]
  have hA : r*r ≤ ∑ a ∈ S, freq D (j,a) := by
    simpa [hc] using (sum_le_sum (fun a ha => hcr a ha) :
      (∑ a ∈ S, r) ≤ ∑ a ∈ S, freq D (j,a))
  have hB : (6-r)*m ≤ ∑ a ∈ T, freq D (j,a) := by
    simpa [hdT] using (sum_le_sum (fun a _ => hm (j,a)) :
      (∑ a ∈ T, m) ≤ ∑ a ∈ T, freq D (j,a))
  have htotal : (∑ a ∈ S, freq D (j,a)) + (∑ a ∈ T, freq D (j,a)) = D.card := by
    have he := sum_sdiff (f := fun a : Fin 6 => freq D (j,a)) (subset_univ S)
    change (∑ a ∈ T, freq D (j,a)) + (∑ a ∈ S, freq D (j,a)) =
      ∑ a : Fin 6, freq D (j,a) at he
    rw [sum_freq] at he
    omega
  omega

/-- A numbered cut in the archived case formulas. -/
def rectangleCut (p : PairKey 6) (da db : Fin 6) : List Int :=
  [literal (pairNumber p) true,
   literal (degreeThresholdNumber p.i p.a da.succ) true,
   literal (degreeThresholdNumber p.j p.b db.succ) true]

/-- Every emitted rectangle cut holds for the actual pair and degree bits. -/
theorem rectangleCut_holds {D : Design 6} (hD : Linear D) (hM : Saturated D) (m : ℕ)
    (hm : ∀ z : Label 6, m ≤ freq D z)
    (p : PairKey 6) (da db : Fin 6) (v : Nat → Bool)
    (hPair : v (pairNumber p) = (encode D).pair p)
    (hDa : v (degreeThresholdNumber p.i p.a da.succ) = decide (da.val + 1 ≤ freq D (p.i,p.a)))
    (hDb : v (degreeThresholdNumber p.j p.b db.succ) = decide (db.val + 1 ≤ freq D (p.j,p.b)))
    (hr : 0 < 6-da.val-db.val)
    (hsize : D.card < (6-da.val-db.val)^2 + (6-(6-da.val-db.val))*m) :
    NumberedHolds v (rectangleCut p da db) := by
  by_cases hp : Used D (p.i,p.a) (p.j,p.b)
  · exact holds_literal_of_mem (b := true) (by simp [rectangleCut]) (by
      have := (pairNumber_bounds p).1; omega) (hPair.trans ((pair_encode D p).2 hp))
  by_cases hA : da.val + 1 ≤ freq D (p.i,p.a)
  · exact holds_literal_of_mem (b := true) (by simp [rectangleCut]) (by
      have := (degreeThresholdNumber_bounds p.i p.a da.succ).1; omega) (hDa.trans (by simp [hA]))
  by_cases hB : db.val + 1 ≤ freq D (p.j,p.b)
  · exact holds_literal_of_mem (b := true) (by simp [rectangleCut]) (by
      have := (degreeThresholdNumber_bounds p.j p.b db.succ).1; omega) (hDb.trans (by simp [hB]))
  exfalso
  have hlo := rectangle_size_lower hD hM (ne_of_lt p.increasing) hp (6-da.val-db.val) m
    (by omega) hm
  exact (Nat.not_lt_of_ge (by simpa only [pow_two] using hlo)) hsize

#print axioms rectangle_size_lower
#print axioms rectangleCut_holds
end LatinGap.PairEncoding
