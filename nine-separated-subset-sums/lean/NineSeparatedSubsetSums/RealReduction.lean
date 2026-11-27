import NineSeparatedSubsetSums.CubeFinsetEncoding
import NineSeparatedSubsetSums.ReindexWeights
import NineSeparatedSubsetSums.CriticalRankModel
import NineSeparatedSubsetSums.CriticalWidth
import NineSeparatedSubsetSums.CentralRankInjective
import Mathlib.Tactic

open scoped BigOperators

namespace NineSeparatedSubsetSums

/-- The full real-to-integer reduction when the largest weight is last. -/
theorem floor_real_counterexample_last_max (w : Fin 9 → ℝ)
    (hpos : ∀ i, 0 < w i)
    (sep : ∀ A B : Finset (Fin 9), A ≠ B →
      1 ≤ |(∑ i ∈ A, w i) - (∑ i ∈ B, w i)|)
    (maxLast : ∀ i, w i ≤ w (Fin.last 8))
    (lt149 : w (Fin.last 8) < 149) :
    (∀ i, 1 ≤ ⌊w i⌋ ∧ ⌊w i⌋ ≤ 148) ∧ ⌊w (Fin.last 8)⌋ = 148 ∧
      Function.Injective (fun S : Finset (Fin 9) => ∑ i ∈ S, ⌊w i⌋) := by
  classical
  let M := w (Fin.last 8)
  let d := M - 148
  have h1 : ∀ i, 1 ≤ w i := by
    intro i
    have h := sep {i} ∅ (by simp)
    simpa [abs_of_pos (hpos i)] using h
  have hm0 : 0 ≤ M - 1 := by linarith [h1 (Fin.last 8)]
  have hM0 : 0 ≤ M := (hpos (Fin.last 8)).le
  have hearly : ∀ i : Fin 8, w i.castSucc ≤ M - 1 := by
    exact earlier_le_last_sub_one w maxLast sep
  have small : ∀ i : Fin 8, |w i.castSucc| ≤ M - 1 :=
    fun i => (abs_of_nonneg (hpos i.castSucc).le).symm ▸ hearly i
  have hM1 : ∀ i : Fin 9, |w i| ≤ M :=
    fun i => (abs_of_nonneg (hpos i).le).symm ▸ maxLast i
  let s := actualSubsetCubeRankModel w sep
  have width := forced_critical_width s.rank s.value w M (M - 1) rfl hM0 hm0 lt149
    (by change M < 149 at lt149; linarith) hM1 small s.lookup s.gap
  have hM : M = 148 + d := by dsimp [d]; ring
  have hd : 0 ≤ d ∧ d < 1 := by
    change M < 149 at lt149
    dsimp [d]
    constructor <;> linarith [width.2]
  have hmFloor : ⌊w (Fin.last 8)⌋ = 148 := by
    change ⌊M⌋ = 148
    apply Int.floor_eq_iff.mpr
    norm_num
    exact ⟨width.2, by change M < 149 at lt149; linarith⟩
  let E := cubeFinsetEquiv 9
  let C := cubeSliceFinsetEquiv 8
  let RR := E.symm.trans s.rank
  let RF := C.symm.trans s.rank
  let w8 (i : Fin 8) : ℝ := w i.castSucc
  have slice (T : Finset (Fin 8)) (b : Bool) :
      s.value (RF (T, b)).val = liftScore M (slabScore w8 T) b := by
    change s.value (s.rank (C.symm (T,b))).val = _
    exact (s.lookup _).trans (weighted_cubeSlice_symm 8 w T b)
  obtain ⟨frac, K, off⟩ := critical_block_model w8 s.value RF M d s.gap width.1 hM hd
    (fun i => ⟨hpos i.castSucc, maxLast i.castSucc⟩) slice
  have afrac : ∀ i, Int.fract (w i) ≤ d := by
    intro i
    refine Fin.lastCases ?_ (fun j => frac j) i
    change Int.fract (w (Fin.last 8)) ≤ d
    change M - (⌊w (Fin.last 8)⌋ : ℝ) ≤ d
    rw [hmFloor]
    norm_num [d]
  have lk (S : Finset (Fin 9)) : s.value (RR S).val = ∑ i ∈ S, w i := by
    change s.value (s.rank (E.symm S)).val = _
    rw [s.lookup, weighted_eq_sum_cubeFinset, E.apply_symm_apply]
  have finit (S : Finset (Fin 9)) (hL : 157 ≤ (RR S).val) (hR : (RR S).val ≤ 305) :
      ((RR S).val : ℤ) - (∑ i ∈ S, ⌊w i⌋) = K := by
    let x := E.symm S
    let p := C x
    have pp : (p.1, p.2) = C x := Prod.eta p
    have rankEq : RF (p.1,p.2) = RR S := by
      change s.rank (C.symm (p.1,p.2)) = s.rank x
      rw [pp, C.symm_apply_apply]
    have h := off p.1 p.2 (rankEq.symm ▸ hL) (rankEq.symm ▸ hR)
    have sums : (∑ i ∈ S, ⌊w i⌋) = intLiftScore (∑ i ∈ p.1, ⌊w8 i⌋) p.2 := by
      let z (i : Fin 9) : ℝ := (⌊w i⌋ : ℝ)
      have sum1 := weighted_eq_sum_cubeFinset 9 z x
      have sum2 := weighted_cubeSlice_symm 8 z p.1 p.2
      have ee : (cubeFinsetEquiv 9) x = S := E.apply_symm_apply S
      have ce : (cubeSliceFinsetEquiv 8).symm (p.1,p.2) = x := by
        change C.symm (p.1,p.2) = x
        rw [pp, C.symm_apply_apply]
      rw [ee] at sum1
      rw [ce] at sum2
      have sf := sum1.symm.trans sum2
      change (∑ i ∈ S, (⌊w i⌋ : ℝ)) =
        (∑ i ∈ p.1, (⌊w8 i⌋ : ℝ)) + if p.2 then (⌊w (Fin.last 8)⌋ : ℝ) else 0 at sf
      rw [hmFloor] at sf
      cases H : p.2
      · simp [H] at sf
        simpa [intLiftScore, H] using (show (∑ i ∈ S, ⌊w i⌋) = ∑ i ∈ p.1, ⌊w8 i⌋ by
          exact_mod_cast sf)
      · simp [H] at sf
        simpa [intLiftScore, H] using (show (∑ i ∈ S, ⌊w i⌋) = (∑ i ∈ p.1, ⌊w8 i⌋) + 148 by
          apply (Int.cast_injective (α := ℝ)); push_cast <;> exact sf)
    rwa [rankEq, ← sums] at h
  refine ⟨fun i => rounded_weight_bounds (w i) (h1 i) ((maxLast i).trans_lt lt149), hmFloor, ?_⟩
  exact rounded_injective_from_first_block w RR s.value d hd
    (fun i => ⟨h1 i, (maxLast i).trans_lt lt149⟩) afrac s.increasing lk K finit

/-- Real counterexamples to 149 imply integer counterexamples at exact
maximum 148. No integer exclusion is assumed by this reduction. -/
theorem real_counterexample_reduces_to_integer (w : Fin 9 → ℝ)
    (hpos : ∀ i, 0 < w i)
    (sep : ∀ A B : Finset (Fin 9), A ≠ B →
      1 ≤ |(∑ i ∈ A, w i) - (∑ i ∈ B, w i)|)
    (lt149 : ∀ i, w i < 149) :
    ∃ a : Fin 9 → ℤ, (∀ i, 1 ≤ a i ∧ a i ≤ 148) ∧ a (Fin.last 8) = 148 ∧
      Function.Injective (fun S : Finset (Fin 9) => ∑ i ∈ S, a i) := by
  obtain ⟨p, mx, sp⟩ := reindex_max_last w sep
  exact ⟨fun i => ⌊w (p i)⌋,
    floor_real_counterexample_last_max (fun i => w (p i))
      (fun i => hpos (p i)) sp mx (lt149 _)⟩

/-- The 149 lower bound, conditional only on the stated finite integer
exclusion. The standalone C++ search is evidence for that exclusion, not
a Lean proof of it. -/
theorem separated_nine_at_least_149_of_integer_exclusion
    (exclude : ∀ a : Fin 9 → ℤ, (∀ i, 1 ≤ a i ∧ a i ≤ 148) →
      a (Fin.last 8) = 148 →
        ¬ Function.Injective (fun S : Finset (Fin 9) => ∑ i ∈ S, a i))
    (w : Fin 9 → ℝ) (hpos : ∀ i, 0 < w i)
    (sep : ∀ A B : Finset (Fin 9), A ≠ B →
      1 ≤ |(∑ i ∈ A, w i) - (∑ i ∈ B, w i)|) :
    ∃ i, 149 ≤ w i := by
  by_contra! h
  obtain ⟨a, ha, hm, hi⟩ := real_counterexample_reduces_to_integer w hpos sep h
  exact exclude a ha hm hi

#print axioms separated_nine_at_least_149_of_integer_exclusion
#print axioms floor_real_counterexample_last_max
#print axioms real_counterexample_reduces_to_integer

end NineSeparatedSubsetSums
