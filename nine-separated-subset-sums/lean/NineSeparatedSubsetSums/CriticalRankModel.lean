import NineSeparatedSubsetSums.CriticalProjection
import NineSeparatedSubsetSums.CriticalOffsets
import NineSeparatedSubsetSums.CoordinateFraction
import Mathlib.Order.Interval.Finset.Fin

open scoped BigOperators

namespace NineSeparatedSubsetSums

/-- The entire rounded-rank argument on the first critical block. The
inputs are a separated rank model and the width of ranks 158 through 306;
the small coordinate fractional parts are consequences, not assumptions. -/
theorem critical_block_model (w : Fin 8 → ℝ) (v : ℕ → ℝ)
    (r : Finset (Fin 8) × Bool ≃ Fin 512) (M δ : ℝ)
    (hgap : ∀ k : ℕ, k + 1 < 512 → 1 ≤ v (k + 1) - v k)
    (hwidth : v 305 = v 157 + M)
    (hM : M = 148 + δ) (hδ : 0 ≤ δ ∧ δ < 1)
    (hw : ∀ i, 0 < w i ∧ w i ≤ M)
    (hscore : ∀ S b, v (r (S, b)).val = liftScore M (slabScore w S) b) :
    (∀ i, Int.fract (w i) ≤ δ) ∧
    ∃ K : ℤ, ∀ (S : Finset (Fin 8)) (b : Bool),
      157 ≤ (r (S, b)).val → (r (S, b)).val ≤ 305 →
      ((r (S, b)).val : ℤ) - intLiftScore (∑ i ∈ S, ⌊w i⌋) b = K := by
  classical
  let U : Finset (Fin 8) := Finset.univ
  let idx (S : Finset (Fin 8)) (b : Bool) := (r (S, b)).val
  have inc (i j : ℕ) (hij : i ≤ j) (hj : j < 512) : v i ≤ v j := by
    have h := accumulate_gaps v 512 hgap i (j - i) (by omega)
    have he : i + (j - i) = j := by omega
    rw [he] at h
    linarith [Nat.cast_nonneg (α := ℝ) (j - i)]
  have strict (i j : ℕ) (hij : i < j) (hj : j < 512) : v i < v j := by
    have h := accumulate_gaps v 512 hgap i (j - i) (by omega)
    have he : i + (j - i) = j := by omega
    rw [he] at h
    have hpos : (0 : ℝ) < ((j - i : ℕ) : ℝ) := by exact_mod_cast (show 0 < j - i by omega)
    linarith
  have within (S : Finset (Fin 8)) (b : Bool) :
      (157 ≤ idx S b ∧ idx S b ≤ 305) ↔
        (v 157 ≤ liftScore M (slabScore w S) b ∧ liftScore M (slabScore w S) b ≤ v 157 + M) := by
    have hb : idx S b < 512 := (r (S, b)).isLt
    rw [← hscore S b, ← hwidth]
    constructor
    · intro h
      exact ⟨inc 157 (idx S b) h.1 hb, inc (idx S b) 305 h.2 (by decide)⟩
    · intro h
      constructor
      · by_contra! hn
        exact (not_lt_of_ge h.1) (strict (idx S b) 157 hn (by decide))
      · by_contra! hn
        exact (not_lt_of_ge h.2) (strict 305 (idx S b) hn hb)
  have hbase : Set.InjOn (slabScore w) {S : Finset (Fin 8) | S ⊆ U} := by
    intro S _ T _ he
    have hS : idx S false < 512 := (r (S, false)).isLt
    have hT : idx T false < 512 := (r (T, false)).isLt
    have hEq : v (idx S false) = v (idx T false) := by
      change v (r (S, false)).val = v (r (T, false)).val
      rw [hscore S false, hscore T false, he]
    have hidx : idx S false = idx T false := by
      rcases lt_trichotomy (idx S false) (idx T false) with h | h | h
      · exact ((strict _ _ h hT).ne hEq).elim
      · exact h
      · exact ((strict _ _ h hS).ne hEq.symm).elim
    exact congrArg Prod.fst (r.injective (Fin.ext hidx))
  let F : Finset (Finset (Fin 8) × Bool) :=
    (Finset.Icc (157 : Fin 512) 305).map r.symm.toEmbedding
  have hFR (S : Finset (Fin 8)) (b : Bool) :
      (S, b) ∈ F ↔ 157 ≤ idx S b ∧ idx S b ≤ 305 := by
    constructor
    · intro hx
      obtain ⟨t, ht, he⟩ := Finset.mem_map.mp hx
      have he' : t = r (S, b) := by simpa using congrArg r he
      subst t
      have ht' : (157 : Fin 512) ≤ r (S, b) ∧ r (S, b) ≤ 305 := Finset.mem_Icc.mp ht
      exact ht' 
    · intro hx
      exact Finset.mem_map.mpr ⟨r (S, b), Finset.mem_Icc.mpr hx, r.symm_apply_apply _⟩
  have hFm (S : Finset (Fin 8)) (b : Bool) :
      (S, b) ∈ F ↔ S ⊆ U ∧
        v 157 ≤ liftScore M (slabScore w S) b ∧ liftScore M (slabScore w S) b ≤ v 157 + M := by
    rw [hFR, within]
    exact ⟨fun h => ⟨Finset.subset_univ _, h⟩, And.right⟩
  have hF : F.card = 149 := by
    dsimp [F]
    rw [Finset.card_map, Fin.card_Icc]
    decide
  have hexcess : v 305 - v 157 - ((305 - 157 : ℕ) : ℝ) = δ := by
    norm_num
    linarith
  have hfract (x : Fin 8) : Int.fract (w x) ≤ δ := by
    have hu : U.card = 8 := by decide
    have hx : x ∈ U := Finset.mem_univ x
    obtain ⟨S, a, b, hnot, hS, hT⟩ :=
      critical_projection_has_direction U w (v 157) M F hu hbase hFm hF x hx
    have hhS := (hFm S a).mp hS
    have hhT := (hFm (insert x S) b).mp hT
    have equ : slabScore w (insert x S) = slabScore w S + w x := by
      simp [slabScore, Finset.sum_insert hnot, add_comm]
    rw [equ] at hhT
    have hz := projected_edge_length (v 157) M (slabScore w S) (w x)
      (hw x).1 (hw x).2 a b hhS.2 hhT.2
    have eS : v (idx S a) = liftScore M (slabScore w S) a := hscore S a
    have eT : v (idx (insert x S) b) = liftScore M (slabScore w S + w x) b := by
      simpa [← equ] using hscore (insert x S) b
    rw [← eS, ← eT] at hz
    have hR1 := (hFR S a).mp hS
    have hR2 := (hFR (insert x S) b).mp hT
    by_cases h : idx S a ≤ idx (insert x S) b
    · rw [abs_of_nonneg (sub_nonneg.mpr (inc _ _ h (by omega)))] at hz
      exact coordinate_fract_of_lift v 512 157 305 _ _ (w x) M δ
        hgap hR1.1 h hR2.2 (by decide) hδ hexcess hM hz
    · have hle : idx (insert x S) b ≤ idx S a := by omega
      rw [abs_of_nonpos (sub_nonpos.mpr (inc _ _ hle (by omega))), neg_sub] at hz
      exact coordinate_fract_of_lift v 512 157 305 _ _ (w x) M δ
        hgap hR2.1 hle hR1.2 (by decide) hδ hexcess hM hz
  refine ⟨hfract, ?_⟩
  let Q := (r.symm (157 : Fin 512)).1
  let q := (r.symm (157 : Fin 512)).2
  have hQidx : idx Q q = 157 := by
    dsimp [Q, q, idx]
    rw [Prod.eta, r.apply_symm_apply]
    decide
  refine ⟨(idx Q q : ℤ) - intLiftScore (∑ i ∈ Q, ⌊w i⌋) q, ?_⟩
  intro S b hL hR
  exact critical_offsets_constant U w v idx 512 157 305 M δ hgap
    (by decide) (by decide) hwidth hM hδ (fun x _ => ⟨(hw x).1, (hw x).2, hfract x⟩)
    (fun T _ a => hscore T a) (fun T _ a => within T a) S Q
    (Finset.subset_univ _) (Finset.subset_univ _) b q ⟨hL, hR⟩ ⟨by omega, by omega⟩

#print axioms critical_block_model

end NineSeparatedSubsetSums
