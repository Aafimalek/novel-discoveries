import QuadrupleParity

namespace ES33

/-- The second divided difference of ordinate as a function of abscissa. -/
noncomputable def curvature (a b c : Plane) : ℝ :=
  orient a b c / ((b.1-a.1)*(c.1-b.1)*(c.1-a.1))

private lemma curvature_sign (a b c : Plane) (h₁ : a.1 < b.1) (h₂ : b.1 < c.1) :
    positiveBit (curvature a b c) = positiveBit (orient a b c) := by
  have hp := mul_pos (mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂)) (sub_pos.mpr (h₁.trans h₂))
  simp [positiveBit,curvature, div_pos_iff_of_pos_right hp]

private lemma curvature_steps (a b c d : Plane) (hab : a.1 < b.1) (hbc : b.1 < c.1)
    (hcd : c.1 < d.1) :
    (curvature a b d - curvature a b c) * (d.1-a.1) =
      (curvature b c d - curvature a b c) * (d.1-c.1) ∧
    (curvature a c d - curvature a b d) * (d.1-a.1) =
      (curvature b c d - curvature a b c) * (c.1-b.1) ∧
    (curvature b c d - curvature a c d) * (d.1-a.1) =
      (curvature b c d - curvature a b c) * (b.1-a.1) := by
  have hab' := sub_ne_zero.mpr hab.ne'
  have hbc' := sub_ne_zero.mpr hbc.ne'
  have hcd' := sub_ne_zero.mpr hcd.ne'
  have hac' := sub_ne_zero.mpr (hab.trans hbc).ne'
  have hbd' := sub_ne_zero.mpr (hbc.trans hcd).ne'
  have had' := sub_ne_zero.mpr (hab.trans (hbc.trans hcd)).ne'
  refine ⟨?_,?_,?_⟩ <;> unfold curvature orient <;>
    field_simp [hab',hbc',hcd',hac',hbd',had'] <;> ring

private lemma positiveBit_monotone : Monotone positiveBit := by
  intro a b h
  apply Bool.le_iff_imp.mpr
  simp only [positiveBit, decide_eq_true_eq]
  exact fun ha => ha.trans_le h

/-- The sorted orientation packet is monotone in one direction, hence has
at most one sign change. These are genuine real-geometric constraints, not
postulated Boolean axioms. -/
theorem ordered_quad_signotope (a b c d : Plane) (hab : a.1 < b.1)
    (hbc : b.1 < c.1) (hcd : c.1 < d.1) :
    let u := positiveBit (orient a b c)
    let v := positiveBit (orient a b d)
    let w := positiveBit (orient a c d)
    let z := positiveBit (orient b c d)
    (u ≤ v ∧ v ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ v ∧ v ≤ u) := by
  have had := sub_pos.mpr (hab.trans (hbc.trans hcd))
  obtain ⟨h1,h2,h3⟩ := curvature_steps a b c d hab hbc hcd
  dsimp only
  rw [← curvature_sign a b c hab hbc, ← curvature_sign a b d hab (hbc.trans hcd),
    ← curvature_sign a c d (hab.trans hbc) hcd, ← curvature_sign b c d hbc hcd]
  rcases le_total (curvature a b c) (curvature b c d) with h|h
  · have hp := sub_nonneg.mpr h
    have t1 := (mul_nonneg_iff_of_pos_right had).mp
      (show 0 ≤ (curvature a b d - curvature a b c) * (d.1-a.1) by
        rw [h1]; exact mul_nonneg hp (sub_nonneg.mpr hcd.le))
    have t2 := (mul_nonneg_iff_of_pos_right had).mp
      (show 0 ≤ (curvature a c d - curvature a b d) * (d.1-a.1) by
        rw [h2]; exact mul_nonneg hp (sub_nonneg.mpr hbc.le))
    have t3 := (mul_nonneg_iff_of_pos_right had).mp
      (show 0 ≤ (curvature b c d - curvature a c d) * (d.1-a.1) by
        rw [h3]; exact mul_nonneg hp (sub_nonneg.mpr hab.le))
    exact Or.inl ⟨positiveBit_monotone (sub_nonneg.mp t1),
      positiveBit_monotone (sub_nonneg.mp t2),positiveBit_monotone (sub_nonneg.mp t3)⟩
  · have hp := sub_nonpos.mpr h
    have t1 := nonpos_of_mul_nonpos_left
      (show (curvature a b d - curvature a b c) * (d.1-a.1) ≤ 0 by
        rw [h1]; exact mul_nonpos_of_nonpos_of_nonneg hp (sub_nonneg.mpr hcd.le)) had
    have t2 := nonpos_of_mul_nonpos_left
      (show (curvature a c d - curvature a b d) * (d.1-a.1) ≤ 0 by
        rw [h2]; exact mul_nonpos_of_nonpos_of_nonneg hp (sub_nonneg.mpr hbc.le)) had
    have t3 := nonpos_of_mul_nonpos_left
      (show (curvature b c d - curvature a c d) * (d.1-a.1) ≤ 0 by
        rw [h3]; exact mul_nonpos_of_nonpos_of_nonneg hp (sub_nonneg.mpr hab.le)) had
    exact Or.inr ⟨positiveBit_monotone (sub_nonpos.mp t3),
      positiveBit_monotone (sub_nonpos.mp t2),positiveBit_monotone (sub_nonpos.mp t1)⟩

#print axioms curvature_steps
#print axioms ordered_quad_signotope

end ES33
