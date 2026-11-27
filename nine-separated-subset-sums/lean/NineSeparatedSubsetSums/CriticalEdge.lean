import NineSeparatedSubsetSums.RankSpan
import NineSeparatedSubsetSums.RankCut

namespace NineSeparatedSubsetSums

theorem same_last_near_bound (n : ℕ) (w : Fin (n + 1) → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hw : ∀ i : Fin n, |w i.castSucc| ≤ M)
    (x y : Cube n × Bool) (h : near (n + 1) x y) (hlast : x.2 = y.2) :
    |weighted (n + 1) w x - weighted (n + 1) w y| ≤ M := by
  obtain ⟨x, a⟩ := x
  obtain ⟨y, b⟩ := y
  change a = b at hlast
  subst b
  change (a = a ∧ near n x y) ∨ x = y at h
  rcases h with ⟨_, hs⟩ | rfl
  · simpa only [weighted, add_sub_add_right_eq_sub] using
      near_weighted_bound n (fun j => w j.castSucc) M hM hw x y hs
  · simpa using hM

/-- Coordinates in the model are ordered with the largest weight last.
The saturated rank edge then uses that last coordinate. -/
theorem saturated_edge_changes_last (r : Cube 9 ≃ Fin 512)
    (v : ℕ → ℝ) (w : Fin 9 → ℝ) (M m : ℝ)
    (hM : 0 ≤ M) (hm : 0 ≤ m) (hlt : M < 149) (hsmall : m < 148)
    (hw : ∀ i : Fin 9, |w i| ≤ M)
    (hsmallWeights : ∀ i : Fin 8, |w i.castSucc| ≤ m)
    (hscore : ∀ x : Cube 9, v (r x).val = weighted 9 w x)
    (hgap : ∀ i : ℕ, i + 1 < 512 → 1 ≤ v (i + 1) - v i) :
    (show Cube 8 × Bool from r.symm 305).2 ≠
      (show Cube 8 × Bool from r.symm 157).2 := by
  intro hlast
  have hNear := forced_rank_edge r (rank_span_le_148 r v w M hM hlt hw hscore hgap)
  have hEdge := same_last_near_bound 8 w m hm hsmallWeights
      (r.symm 305) (r.symm 157) hNear hlast
  have hg := accumulate_gaps v 512 hgap 157 148 (by omega)
  have h305 : v 305 = weighted 9 w (r.symm 305) := by
    have h := hscore (r.symm 305)
    rw [r.apply_symm_apply] at h
    have he : (305 : Fin 512).val = 305 := by decide
    rwa [he] at h
  have h157 : v 157 = weighted 9 w (r.symm 157) := by
    have h := hscore (r.symm 157)
    rw [r.apply_symm_apply] at h
    have he : (157 : Fin 512).val = 157 := by decide
    rwa [he] at h
  have hgap' : (148 : ℝ) ≤ v 305 - v 157 := by
    exact hg
  rw [h305, h157] at hgap'
  have hh := le_trans hgap' (le_trans (le_abs_self _) hEdge)
  linarith

#print axioms saturated_edge_changes_last

end NineSeparatedSubsetSums

