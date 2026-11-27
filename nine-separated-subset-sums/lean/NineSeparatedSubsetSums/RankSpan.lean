import NineSeparatedSubsetSums.Weighted

namespace NineSeparatedSubsetSums

/-- Unit-separated rank scores and a maximum weight below 149 make every
closed cube edge span at most 148 ranks. -/
theorem rank_span_le_148 (r : Cube 9 ≃ Fin 512) (v : ℕ → ℝ)
    (w : Fin 9 → ℝ) (M : ℝ) (hM : 0 ≤ M) (hlt : M < 149)
    (hw : ∀ i, |w i| ≤ M)
    (hscore : ∀ x : Cube 9, v (r x).val = weighted 9 w x)
    (hgap : ∀ i : ℕ, i + 1 < 512 → 1 ≤ v (i + 1) - v i)
    (x y : Cube 9) (hxy : near 9 x y) :
    (r x).val ≤ (r y).val + 148 := by
  by_cases h : (r y).val ≤ (r x).val
  · let d := (r x).val - (r y).val
    have hadd : (r y).val + d = (r x).val := by dsimp [d]; omega
    have hrange : (r y).val + d < 512 := by
      rw [hadd]
      exact (r x).isLt
    have hd := accumulate_gaps v 512 hgap (r y).val d hrange
    rw [hadd, hscore x, hscore y] at hd
    have hweight := near_weighted_bound 9 w M hM hw x y hxy
    have hreal : (d : ℝ) < 149 :=
      lt_of_le_of_lt (le_trans hd (le_trans (le_abs_self _) hweight)) hlt
    have hnat : d < 149 := by exact_mod_cast hreal
    omega
  · omega

#print axioms rank_span_le_148

end NineSeparatedSubsetSums

