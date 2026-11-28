/- Static draft. Designed for standalone compilation without any ES33,
real analysis, geometry, ring, or linarith tactic imports. -/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Basic

namespace ES33.ReflectionAlgebra

variable {R : Type*} [CommRing R]

abbrev Point (R : Type*) := R × R

def det (u v : Point R) : R := u.1 * v.2 - u.2 * v.1
def diff (u v : Point R) : Point R := (u.1 - v.1, u.2 - v.2)
def negVec (u : Point R) : Point R := (-u.1, -u.2)
def mirror (u : Point R) : Point R := (-u.1, u.2)

def orient (a b c : Point R) : R := det (diff b a) (diff c a)

private theorem det_sub_left (u v w : Point R) :
    det (diff u v) w = det u w - det v w := by
  simp only [det, diff, sub_mul]
  rw [sub_sub_sub_comm]

private theorem det_neg_right (u v : Point R) :
    det u (negVec v) = -det u v := by
  simp only [det, negVec, mul_neg, neg_sub_neg, neg_sub]

private theorem det_self (u : Point R) : det u u = 0 := by
  unfold det
  rw [mul_comm u.1 u.2, sub_self]

private theorem det_mirror (u v : Point R) :
    det (mirror u) (mirror v) = -det u v := by
  simp only [det, mirror, neg_mul, mul_neg, neg_sub_neg, neg_sub]

private theorem mirror_diff (u v : Point R) :
    diff (mirror u) (mirror v) = mirror (diff u v) := by
  apply Prod.ext
  · simp only [diff, mirror, neg_sub_neg, neg_sub]
  · rfl

private theorem diff_rebase (u v a : Point R) :
    diff u v = diff (diff u a) (diff v a) := by
  apply Prod.ext
  · exact (sub_sub_sub_cancel_right u.1 v.1 a.1).symm
  · exact (sub_sub_sub_cancel_right u.2 v.2 a.2).symm

private theorem diff_flip (u v : Point R) :
    diff u v = negVec (diff v u) := by
  apply Prod.ext <;> simp only [diff, negVec, neg_sub]

theorem orient_reverse (a b c : Point R) :
    orient c b a = -orient a b c := by
  calc
    orient c b a =
        det (diff (diff b a) (diff c a)) (negVec (diff c a)) := by
      change det (diff b c) (diff a c) = _
      rw [diff_rebase b c a, diff_flip a c]
    _ = -(det (diff b a) (diff c a) - det (diff c a) (diff c a)) := by
      rw [det_neg_right, det_sub_left]
    _ = -orient a b c := by simp only [det_self, sub_zero, orient]

theorem orient_mirror (a b c : Point R) :
    orient (mirror a) (mirror b) (mirror c) = -orient a b c := by
  simp only [orient, mirror_diff, det_mirror]

theorem orient_mirror_reverse (a b c : Point R) :
    orient (mirror c) (mirror b) (mirror a) = orient a b c := by
  rw [orient_mirror, orient_reverse, neg_neg]

#print axioms orient_reverse
#print axioms orient_mirror
#print axioms orient_mirror_reverse

end ES33.ReflectionAlgebra
