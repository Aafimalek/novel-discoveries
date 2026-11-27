import AlgebraicWitness
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace PlaneColouring

private theorem rat_pair_zero_of_nonsquare (m a b : ℚ) (hm : ¬ IsSquare m)
    (h : a^2 = m*b^2) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst b
    simp at h ⊢
    exact h
  · exfalso
    apply hm
    refine ⟨a / b, ?_⟩
    field_simp
    linear_combination -h

private theorem rat_linear_sqrt_zero (r a b : ℚ) (hr : 0 ≤ r) (hn : ¬ IsSquare r)
    (h : (a : ℝ) + (b : ℝ) * Real.sqrt (r : ℝ) = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst b
    norm_cast at h
    simp_all
  · exfalso
    have hir := (irrational_sqrt_ratCast_iff_of_nonneg hr).mpr hn
    apply hir
    refine ⟨-a/b, ?_⟩
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    push_cast
    apply (div_eq_iff hb').2
    nlinarith only [h]

namespace Radical4

/-- Independence of 1, √r, √s and √r√s when all three quadratic
radicands are nonsquares. This is stronger than the soundness premise. -/
theorem eval_injective_of_nonsquares (r s : ℚ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hnr : ¬ IsSquare r) (hns : ¬ IsSquare s) (hnrs : ¬ IsSquare (r*s)) :
    Function.Injective (eval r s) := by
  have zero {a b c d : ℚ} (h : eval r s ⟨a,b,c,d⟩ = 0) :
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
    have hr' : 0 ≤ (r : ℝ) := by exact_mod_cast hr
    have hs' : 0 ≤ (s : ℝ) := by exact_mod_cast hs
    have hrr := Real.sq_sqrt hr'
    have hss := Real.sq_sqrt hs'
    have E : (a : ℝ) + (b : ℝ)*Real.sqrt (r : ℝ) =
          -((c : ℝ) + (d : ℝ)*Real.sqrt (r : ℝ))*Real.sqrt (s : ℝ) := by
      dsimp [eval] at h
      linear_combination h
    have E2 : ((a : ℝ) + (b : ℝ)*Real.sqrt (r : ℝ))^2 -
        (s : ℝ)*((c : ℝ) + (d : ℝ)*Real.sqrt (r : ℝ))^2 = 0 := by
      rw [E]
      linear_combination ((c : ℝ) + (d : ℝ)*Real.sqrt (r : ℝ))^2 * hss
    have split : (↑(a^2 + r*b^2 - s*(c^2+r*d^2)) : ℝ) +
        (↑(2*(a*b-s*c*d)) : ℝ) * Real.sqrt (r : ℝ) = 0 := by
      push_cast
      linear_combination E2 + (-(b : ℝ)^2 + (s : ℝ)*(d : ℝ)^2)*hrr
    obtain ⟨hA,hB⟩ := rat_linear_sqrt_zero r _ _ hr hnr split
    have hB' : a*b - s*c*d = 0 := by
      nlinarith only [hB]
    have H : (a^2-r*b^2)^2 = (s*(c^2-r*d^2))^2 := by
      linear_combination (a^2+r*b^2+s*(c^2+r*d^2))*hA -
        (4*r*(a*b+s*c*d))*hB'
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp H with H | H
    · have h₁ : a^2 = s*c^2 := by linear_combination hA/2 + H/2
      have H₂ : r*(b^2 - s*d^2) = 0 := by linear_combination hA/2 - H/2
      have hrn : r ≠ 0 := fun h => hnr (h ▸ (show IsSquare (0 : ℚ) from ⟨0,by norm_num⟩))
      have h₂ : b^2 = s*d^2 := sub_eq_zero.mp ((mul_eq_zero.mp H₂).resolve_left hrn)
      obtain ⟨ha,hc⟩ := rat_pair_zero_of_nonsquare s a c hns h₁
      obtain ⟨hb,hd⟩ := rat_pair_zero_of_nonsquare s b d hns h₂
      exact ⟨ha,hb,hc,hd⟩
    · have h₁ : a^2 = (r*s)*d^2 := by linear_combination hA/2 + H/2
      have h₂ : (r*b)^2 = (r*s)*c^2 := by linear_combination (r/2)*hA - (r/2)*H
      obtain ⟨ha,hd⟩ := rat_pair_zero_of_nonsquare (r*s) a d hnrs h₁
      obtain ⟨hrb,hc⟩ := rat_pair_zero_of_nonsquare (r*s) (r*b) c hnrs h₂
      have hrn : r ≠ 0 := fun h => hnr (h ▸ (show IsSquare (0 : ℚ) from ⟨0,by norm_num⟩))
      exact ⟨ha,(mul_eq_zero.mp hrb).resolve_left hrn,hc,hd⟩
  intro x y he
  have diff : eval r s (sub x y) = 0 := by rw [eval_sub,he,sub_self]
  cases x with
  | mk a b c d =>
    cases y with
    | mk e f g h =>
      obtain ⟨ha,hb,hc,hd⟩ := zero diff
      dsimp at ha hb hc hd
      rw [sub_eq_zero.mp ha, sub_eq_zero.mp hb, sub_eq_zero.mp hc, sub_eq_zero.mp hd]

end Radical4

/-- The rational coefficients recover every true unit edge in this field. -/
theorem unitTest_iff_dist (r s : ℚ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hnr : ¬ IsSquare r) (hns : ¬ IsSquare s) (hnrs : ¬ IsSquare (r*s))
    (a b : Coordinate) :
    unitTest r s a b = true ↔ dist (coordinateEval r s a) (coordinateEval r s b) = 1 := by
  refine ⟨dist_eq_one_of_unitTest r s hr hs a b, fun h => ?_⟩
  apply decide_eq_true
  apply Radical4.eval_injective_of_nonsquares r s hr hs hnr hns hnrs
  rw [Radical4.eval_add, Radical4.eval_sq _ _ hr hs,
    Radical4.eval_sq _ _ hr hs, Radical4.eval_sub, Radical4.eval_sub,
    Radical4.eval_one]
  have h₂ := EuclideanSpace.dist_sq_eq (coordinateEval r s a) (coordinateEval r s b)
  rw [h,one_pow] at h₂
  simpa only [Fin.sum_univ_two, coordinateEval, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.dist_eq, sq_abs] using h₂.symm

/-- The Euclidean unit-distance graph, on the whole plane. -/
def planeGraph : SimpleGraph Plane where
  Adj a b := dist a b = 1
  symm := by constructor; intro a b h; exact (dist_comm b a).trans h
  loopless := by constructor; intro a h; change dist a a = 1 at h; simpa using h

/-- Dimension and radicands are explicit; this is the end link to the
Mathlib chromatic number. A successful six-colour refutation yields ≥7. -/
theorem chromatic_lower_of_radical_witness (r s : ℚ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (n k : ℕ) (pts : Fin n → Coordinate) (edges : List (Fin n × Fin n))
    (euclidean : ∀ e ∈ edges, unitTest r s (pts e.1) (pts e.2) = true)
    (unsat : ¬ ∃ colour : Fin n → Fin k, ∀ e ∈ edges, colour e.1 ≠ colour e.2) :
    ((k+1 : ℕ) : ℕ∞) ≤ planeGraph.chromaticNumber := by
  rw [planeGraph.le_chromaticNumber_iff_colorable]
  intro m hm
  by_contra! small
  have hmk : m ≤ k := by omega
  obtain ⟨c⟩ := hm
  exact no_plane_colouring_of_radical_witness r s hr hs n k pts edges euclidean unsat
    ⟨fun p => Fin.castLE hmk (c p), fun a b hab hcolour =>
      c.valid hab (Fin.castLE_injective hmk hcolour)⟩

#print axioms Radical4.eval_injective_of_nonsquares
#print axioms unitTest_iff_dist
#print axioms chromatic_lower_of_radical_witness

end PlaneColouring
