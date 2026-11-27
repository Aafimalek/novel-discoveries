import NineSeparatedSubsetSums.CriticalEdge

namespace NineSeparatedSubsetSums

/-- The forced rank edge has real width equal to the largest weight. -/
theorem forced_critical_width
    (r : Cube 9 ≃ Fin 512) (v : ℕ → ℝ) (w : Fin 9 → ℝ)
    (M m : ℝ) (hM : w (Fin.last 8) = M)
    (hM0 : 0 ≤ M) (hm0 : 0 ≤ m) (h149 : M < 149) (h148 : m < 148)
    (hweight : ∀ i : Fin 9, |w i| ≤ M)
    (hearlier : ∀ i : Fin 8, |w i.castSucc| ≤ m)
    (score : ∀ x : Cube 9, v (r x).val = weighted 9 w x)
    (hgap : ∀ k : ℕ, k + 1 < 512 → 1 ≤ v (k + 1) - v k) :
    v 305 = v 157 + M ∧ 148 ≤ M := by
  have adj := forced_rank_edge r (rank_span_le_148 r v w M hM0 h149 hweight score hgap)
  have bit := saturated_edge_changes_last r v w M m hM0 hm0 h149 h148 hweight hearlier score hgap
  -- Use variables with equations so the score lookup rewrites under r.
  let x : Cube 8 × Bool := r.symm 305
  let y : Cube 8 × Bool := r.symm 157
  change (x.2 = y.2 ∧ near 8 x.1 y.1) ∨ x.1 = y.1 at adj
  change x.2 ≠ y.2 at bit
  have base : x.1 = y.1 := adj.resolve_left (fun h => bit h.1)
  have eq305 : v 305 = weighted 9 w x := by
    have h : v (r x).val = weighted 9 w x := score x
    have ex : r x = 305 := r.apply_symm_apply _
    rw [ex] at h
    exact h
  have eq157 : v 157 = weighted 9 w y := by
    have h : v (r y).val = weighted 9 w y := score y
    have ey : r y = 157 := r.apply_symm_apply _
    rw [ey] at h
    exact h
  have h1 : (148 : ℝ) ≤ v 305 - v 157 := accumulate_gaps v 512 hgap 157 148 (by decide)
  rw [eq305, eq157] at h1 ⊢
  change (weighted 8 (fun j => w j.castSucc) x.1 + (if x.2 then w (Fin.last 8) else 0) =
    weighted 8 (fun j => w j.castSucc) y.1 + (if y.2 then w (Fin.last 8) else 0) + M) ∧ 148 ≤ M
  change (148 : ℝ) ≤
    weighted 8 (fun j => w j.castSucc) x.1 + (if x.2 then w (Fin.last 8) else 0) -
    (weighted 8 (fun j => w j.castSucc) y.1 + (if y.2 then w (Fin.last 8) else 0)) at h1
  rw [base, hM] at h1
  rw [base, hM]
  cases hx : x.2 <;> cases hy : y.2
  · exact (bit (hx.trans hy.symm)).elim
  · simp [hx, hy] at h1
    linarith
  · simp [hx, hy] at h1 ⊢
    linarith
  · exact (bit (hx.trans hy.symm)).elim

#print axioms forced_critical_width

end NineSeparatedSubsetSums
