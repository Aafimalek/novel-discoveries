import NineSeparatedSubsetSums.FinsetSlab
import NineSeparatedSubsetSums.CriticalLiftedStep
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace NineSeparatedSubsetSums

/-- The arithmetic and slab arguments compose: when the coordinate
fraction bound is known, every lifted rank in the critical interval
has the same rounded offset. -/
theorem critical_offsets_constant {ι : Type*} [DecidableEq ι]
    (U : Finset ι) (w : ι → ℝ) (v : ℕ → ℝ) (idx : Finset ι → Bool → ℕ)
    (bound L R : ℕ) (M δ : ℝ)
    (hgap : ∀ k : ℕ, k + 1 < bound → 1 ≤ v (k + 1) - v k)
    (hR : R < bound) (hlen : R = L + 148)
    (hwidth : v R = v L + M)
    (hM : M = 148 + δ) (hδ : 0 ≤ δ ∧ δ < 1)
    (hw : ∀ i ∈ U, 0 < w i ∧ w i ≤ M ∧ Int.fract (w i) ≤ δ)
    (hscore : ∀ S ⊆ U, ∀ b, v (idx S b) = liftScore M (slabScore w S) b)
    (hwithin : ∀ S ⊆ U, ∀ b,
      (L ≤ idx S b ∧ idx S b ≤ R) ↔
        (v L ≤ liftScore M (slabScore w S) b ∧ liftScore M (slabScore w S) b ≤ v L + M))
    (P Q : Finset ι) (hPU : P ⊆ U) (hQU : Q ⊆ U) (p q : Bool)
    (hP : L ≤ idx P p ∧ idx P p ≤ R) (hQ : L ≤ idx Q q ∧ idx Q q ≤ R) :
    (idx P p : ℤ) - intLiftScore (∑ i ∈ P, ⌊w i⌋) p =
      (idx Q q : ℤ) - intLiftScore (∑ i ∈ Q, ⌊w i⌋) q := by
  classical
  have hpos : 0 ≤ M := by linarith [hδ.1]
  have hexcess : v R - v L - ((R - L : ℕ) : ℝ) < 1 := by
    have n : R - L = 148 := by omega
    rw [n]
    norm_num
    linarith [hδ.2]
  have hv (S : Finset ι) (h : S ⊆ U) :
      IsWeightSlab w (v L) M S ↔ ∃ b, L ≤ idx S b ∧ idx S b ≤ R := by
    constructor
    · intro hs
      obtain ⟨b, hb⟩ := (lift_exists_iff_in_slab (v L) M (slabScore w S) hpos).mpr hs
      exact ⟨b, (hwithin S h b).mpr hb⟩
    · rintro ⟨b, hb⟩
      exact (lift_exists_iff_in_slab (v L) M (slabScore w S) hpos).mp
        ⟨b, (hwithin S h b).mp hb⟩
  let off (S : Finset ι) (b : Bool) : ℤ := (idx S b : ℤ) - intLiftScore (∑ i ∈ S, ⌊w i⌋) b
  have same (S : Finset ι) (h : S ⊆ U) (a b : Bool)
      (ha : L ≤ idx S a ∧ idx S a ≤ R)
      (hb : L ≤ idx S b ∧ idx S b ≤ R) : off S a = off S b := by
    have hf (ha : L ≤ idx S false ∧ idx S false ≤ R)
        (hb : L ≤ idx S true ∧ idx S true ≤ R) : off S false = off S true := by
      have hs : v (idx S true) - v (idx S false) = M := by
        rw [hscore S h true, hscore S h false]
        simp [liftScore]
      have horder : idx S false ≤ idx S true := by
        by_contra! hh
        have hacc := accumulate_gaps v bound hgap (idx S true)
          (idx S false - idx S true) (by omega)
        have ez : idx S true + (idx S false - idx S true) = idx S false := by omega
        rw [ez] at hacc
        have hnat : (0 : ℝ) < ((idx S false - idx S true : ℕ) : ℝ) := by
          exact_mod_cast (show 0 < idx S false - idx S true by omega)
        linarith
      have hfloor : ⌊M⌋ = 148 := by
        apply Int.floor_eq_iff.mpr
        norm_num
        exact ⟨by linarith [hδ.1], by linarith [hδ.2]⟩
      have hf := rank_difference_is_floor v bound L R (idx S false) (idx S true)
        hgap ha.1 horder hb.2 hR hexcess
      rw [hs, hfloor] at hf
      dsimp [off]
      simp [intLiftScore]
      omega
    cases a <;> cases b
    · rfl
    · exact hf ha hb
    · exact (hf hb ha).symm
    · rfl
  let choose (S : Finset ι) : Bool :=
    if h : S ⊆ U ∧ IsWeightSlab w (v L) M S then Classical.choose ((hv S h.1).mp h.2) else false
  have hc (S : Finset ι) (h : S ⊆ U) (hs : IsWeightSlab w (v L) M S) :
      L ≤ idx S (choose S) ∧ idx S (choose S) ≤ R := by
    dsimp [choose]
    rw [dif_pos (And.intro h hs)]
    exact Classical.choose_spec ((hv S h).mp hs)
  have edge (S : Finset ι) (x : ι) (h : S ⊆ U) (hx : x ∈ U) (hxs : x ∉ S)
      (hs : IsWeightSlab w (v L) M S) (ht : IsWeightSlab w (v L) M (insert x S)) :
      off S (choose S) = off (insert x S) (choose (insert x S)) := by
    have hh : insert x S ⊆ U := Finset.insert_subset_iff.mpr ⟨hx, h⟩
    have e := lifted_insert_preserves_offset v bound L R (idx S (choose S))
      (idx (insert x S) (choose (insert x S))) (slabScore w S) (w x) M δ
      (∑ i ∈ S, ⌊w i⌋) (choose S) (choose (insert x S)) hgap
      (hc S h hs).1 (hc S h hs).2 (hc (insert x S) hh ht).1 (hc (insert x S) hh ht).2
      hR hexcess (by linarith) hδ hM (hw x hx).1 (hw x hx).2.1 (hw x hx).2.2
      (hscore S h (choose S)) (by
        rw [hscore (insert x S) hh (choose (insert x S))]
        simp [slabScore, Finset.sum_insert hxs, add_comm])
    simpa [off, Finset.sum_insert hxs, add_comm] using e
  have hs := (hv P hPU).mpr ⟨p, hP⟩
  have ht := (hv Q hQU).mpr ⟨q, hQ⟩
  have eq := slab_constancy U w (v L) M (fun S => off S (choose S))
      (fun j hj => ⟨(hw j hj).1.le, (hw j hj).2.1⟩) edge hPU hQU hs ht
  exact (same P hPU p (choose P) hP (hc P hPU hs)).trans
    (eq.trans (same Q hQU (choose Q) q (hc Q hQU ht) hQ))

#print axioms critical_offsets_constant

end NineSeparatedSubsetSums
