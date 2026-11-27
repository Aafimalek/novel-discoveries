import ES33.QuadrupleReduction
import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation

namespace ES33

/-- Twice signed area for an ordered triple of planar points. -/
def orient (a b c : Plane) : ℝ :=
  (b.1-a.1)*(c.2-a.2) - (b.2-a.2)*(c.1-a.1)

@[simp] theorem orient_same₁ (a b : Plane) : orient a a b = 0 := by simp [orient]
@[simp] theorem orient_same₂ (a b : Plane) : orient a b a = 0 := by simp [orient]
@[simp] theorem orient_same₃ (a b : Plane) : orient a b b = 0 := by unfold orient; ring

theorem orient_cycle (a b c : Plane) : orient b c a = orient a b c := by unfold orient; ring
theorem orient_exchange (a b c : Plane) : orient a c b = - orient a b c := by unfold orient; ring

private theorem mem_triangle_iff_coeffs {a b c p : Plane} (h : orient a b c ≠ 0) :
    p ∈ convexHull ℝ ({a,b,c} : Set Plane) ↔
      ∃ u v w : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w ∧
        u+v+w=1 ∧ u • a + v • b + w • c = p := by
  classical
  have hab : a ≠ b := by rintro rfl; simp at h
  have hac : a ≠ c := by rintro rfl; simp at h
  have hbc : b ≠ c := by rintro rfl; simp at h
  constructor
  · intro hp
    have hp' : p ∈ convexHull ℝ (↑({a,b,c} : Finset Plane) : Set Plane) := by simpa using hp
    obtain ⟨w, hw₀, hw₁, hw₂⟩ := Finset.mem_convexHull'.1 hp'
    refine ⟨w a,w b,w c,hw₀ a (by simp),hw₀ b (by simp),hw₀ c (by simp), ?_, ?_⟩
    · simpa [Finset.sum_insert,hab,hac,hbc,add_assoc] using hw₁
    · simpa [Finset.sum_insert,hab,hac,hbc,add_assoc] using hw₂
  · rintro ⟨u,v,w,hu,hv,hw,hs,hp⟩
    apply mem_convexHull_of_exists_fintype (![u,v,w] : Fin 3 → ℝ) (![a,b,c] : Fin 3 → Plane)
    · intro i; fin_cases i <;> simp [hu,hv,hw]
    · simpa [Fin.sum_univ_succ,add_assoc] using hs
    · intro i; fin_cases i <;> simp
    · simpa [Fin.sum_univ_succ,add_assoc] using hp

private theorem plane_fst_smul (r : ℝ) (p : Plane) : (r • p).1 = r * p.1 := rfl
private theorem plane_snd_smul (r : ℝ) (p : Plane) : (r • p).2 = r * p.2 := rfl

private theorem orient_mix (a b x y z : Plane) (u v w : ℝ) (h : u+v+w=1) :
    orient a b (u • x + v • y + w • z) =
      u * orient a b x + v * orient a b y + w * orient a b z := by
  have hw : w = 1-u-v := by linarith
  rw [hw]
  simp only [orient, Prod.fst_add, Prod.snd_add, plane_fst_smul, plane_snd_smul]
  ring

/-- The three normalized signed areas are the barycentric coordinates
of a point in a nondegenerate triangle. This connects convex hull membership
to a sign-only test for points not collinear with a triangle edge. -/
theorem mem_triangle_iff_orient {a b c p : Plane} (h : orient a b c ≠ 0) :
    p ∈ convexHull ℝ ({a,b,c} : Set Plane) ↔
      0 ≤ orient b c p / orient a b c ∧
      0 ≤ orient c a p / orient a b c ∧
      0 ≤ orient a b p / orient a b c := by
  rw [mem_triangle_iff_coeffs h]
  constructor
  · rintro ⟨u,v,w,hu,hv,hw,hs,rfl⟩
    have hbc := orient_mix b c a b c u v w hs
    have hca := orient_mix c a a b c u v w hs
    have hab := orient_mix a b a b c u v w hs
    rw [orient_cycle a b c] at hbc
    rw [orient_cycle b c a, orient_cycle a b c] at hca
    simp only [orient_same₂, orient_same₃, mul_zero, zero_add, add_zero] at hbc hca hab
    rw [hbc,hca,hab]
    simpa only [mul_div_cancel_right₀ _ h] using (show 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w from ⟨hu,hv,hw⟩)
  · rintro ⟨hu,hv,hw⟩
    refine ⟨_,_,_,hu,hv,hw,?_ ,?_⟩
    · unfold orient at h ⊢
      field_simp
      ring
    · apply Prod.ext <;>
        simp only [Prod.fst_add,Prod.snd_add,plane_fst_smul,plane_snd_smul,orient] at h ⊢ <;>
        field_simp <;> ring

#print axioms orient_mix
#print axioms mem_triangle_iff_orient

end ES33
