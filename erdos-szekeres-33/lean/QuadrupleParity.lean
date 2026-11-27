import TriangleOrientation

namespace ES33

/-- Encode a nonzero determinant by whether it is positive. -/
noncomputable def positiveBit (x : ℝ) : Bool := by
  classical exact decide (0 < x)

/-- Odd parity of four orientation bits. -/
def oddFour (a b c d : Bool) : Bool :=
  Bool.xor a (Bool.xor b (Bool.xor c d))

private lemma ratio_nonneg_iff_bits {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    0 ≤ x/y ↔ positiveBit x = positiveBit y := by
  classical
  rcases lt_or_gt_of_ne hx with hx | hx <;> rcases lt_or_gt_of_ne hy with hy | hy <;>
    simp [div_nonneg_iff,positiveBit,hx,hy,le_of_lt hx,le_of_lt hy,
      not_le_of_gt hx, not_le_of_gt hy, not_lt_of_ge (le_of_lt hx), not_lt_of_ge (le_of_lt hy)]

private lemma positiveBit_neg {x : ℝ} (hx : x ≠ 0) : positiveBit (-x) = !positiveBit x := by
  classical
  rcases lt_or_gt_of_ne hx with hx|hx
  · simp [positiveBit,not_lt_of_ge (le_of_lt hx),neg_pos.mpr hx]
  · simp [positiveBit,hx,not_lt_of_ge (le_of_lt (neg_neg_of_pos hx))]

private lemma parity_table (u v w z : Bool) :
    oddFour u v w z = true ↔
      (w = z ∧ (!v) = z ∧ u = z) ∨
      (z = w ∧ v = w ∧ (!u) = w) ∨
      ((!z) = v ∧ w = v ∧ u = v) ∨
      (z = u ∧ (!w) = u ∧ v = u) := by
  cases u <;> cases v <;> cases w <;> cases z <;> decide

private lemma not_convex_quad_iff (a b c d : Plane)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ¬ ConvexPosition ({a,b,c,d} : Finset Plane) ↔
      a ∈ convexHull ℝ ({b,c,d} : Set Plane) ∨
      b ∈ convexHull ℝ ({a,c,d} : Set Plane) ∨
      c ∈ convexHull ℝ ({a,b,d} : Set Plane) ∨
      d ∈ convexHull ℝ ({a,b,c} : Set Plane) := by
  classical
  rw [ConvexPosition, convexIndependent_set_iff_notMem_convexHull_sdiff]
  push Not
  have eq : (↑({a,b,c,d} : Finset Plane) : Set Plane) = {a,b,c,d} := by simp
  rw [eq]
  have ha : ({a,b,c,d} : Set Plane) \ {a} = {b,c,d} := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have hb : ({a,b,c,d} : Set Plane) \ {b} = {a,c,d} := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have hc : ({a,b,c,d} : Set Plane) \ {c} = {a,b,d} := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  have hd : ({a,b,c,d} : Set Plane) \ {d} = {a,b,c} := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, h⟩
    rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inl (ha ▸ h)
    · exact Or.inr (Or.inl (hb ▸ h))
    · exact Or.inr (Or.inr (Or.inl (hc ▸ h)))
    · exact Or.inr (Or.inr (Or.inr (hd ▸ h)))
  · rintro (h | h | h | h)
    · exact ⟨a,Or.inl rfl, ha.symm ▸ h⟩
    · exact ⟨b,Or.inr (Or.inl rfl), hb.symm ▸ h⟩
    · exact ⟨c,Or.inr (Or.inr (Or.inl rfl)), hc.symm ▸ h⟩
    · exact ⟨d,Or.inr (Or.inr (Or.inr rfl)), hd.symm ▸ h⟩

/-- A nondegenerate real quadruple is nonconvex iff its four triple
orientations have odd parity. This justifies the parity indicator in the
33-point Erdős–Szekeres SAT formulation. -/
theorem not_convex_quad_iff_odd_orientation (a b c d : Plane)
    (hu : orient a b c ≠ 0) (hv : orient a b d ≠ 0)
    (hw : orient a c d ≠ 0) (hz : orient b c d ≠ 0) :
    ¬ ConvexPosition ({a,b,c,d} : Finset Plane) ↔
      oddFour (positiveBit (orient a b c)) (positiveBit (orient a b d))
        (positiveBit (orient a c d)) (positiveBit (orient b c d)) = true := by
  classical
  have hab : a ≠ b := by rintro rfl; simp at hu
  have hac : a ≠ c := by rintro rfl; simp at hu
  have had : a ≠ d := by rintro rfl; simp at hv
  have hbc : b ≠ c := by rintro rfl; simp at hu
  have hbd : b ≠ d := by rintro rfl; simp at hv
  have hcd : c ≠ d := by rintro rfl; simp at hw
  rw [not_convex_quad_iff a b c d hab hac had hbc hbd hcd, parity_table]
  rw [mem_triangle_iff_orient hz, mem_triangle_iff_orient hw,
    mem_triangle_iff_orient hv, mem_triangle_iff_orient hu]
  have h1 : orient c d a = orient a c d := by unfold orient; ring
  have h2 : orient d b a = -orient a b d := by unfold orient; ring
  have h3 : orient b c a = orient a b c := by unfold orient; ring
  have h4 : orient c d b = orient b c d := by unfold orient; ring
  have h5 : orient d a b = orient a b d := by unfold orient; ring
  have h6 : orient a c b = -orient a b c := by unfold orient; ring
  have h7 : orient b d c = -orient b c d := by unfold orient; ring
  have h8 : orient d a c = orient a c d := by unfold orient; ring
  have h9 : orient c a d = -orient a c d := by unfold orient; ring
  rw [h1,h2,h3,h4,h5,h6,h7,h8,h9]
  simp only [ratio_nonneg_iff_bits hu hz, ratio_nonneg_iff_bits hv hw,
    ratio_nonneg_iff_bits hw hz, ratio_nonneg_iff_bits (neg_ne_zero.mpr hv) hz,
    ratio_nonneg_iff_bits hz hw, ratio_nonneg_iff_bits (neg_ne_zero.mpr hu) hw,
    ratio_nonneg_iff_bits (neg_ne_zero.mpr hz) hv, ratio_nonneg_iff_bits hw hv,
    ratio_nonneg_iff_bits hu hv, ratio_nonneg_iff_bits hz hu,
    ratio_nonneg_iff_bits (neg_ne_zero.mpr hw) hu, ratio_nonneg_iff_bits hv hu,
    positiveBit_neg hu, positiveBit_neg hv, positiveBit_neg hw, positiveBit_neg hz]

#print axioms parity_table
#print axioms not_convex_quad_iff_odd_orientation

end ES33
