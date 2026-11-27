import ModFive

namespace PlaneColouring.Finite25

abbrev Pt := ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5

def moves : List Pt := [(0,0,1,0), (0,0,4,0), (0,1,0,1), (0,1,0,4), (0,2,2,0), (0,2,3,0), (0,3,2,0), (0,3,3,0), (0,4,0,1), (0,4,0,4), (1,0,0,0), (1,2,1,3), (1,2,4,2), (1,3,1,2), (1,3,4,3), (2,0,0,2), (2,0,0,3), (3,0,0,2), (3,0,0,3), (4,0,0,0), (4,2,1,2), (4,2,4,3), (4,3,1,3), (4,3,4,2)]

def isMove (u : Pt) : Prop :=
  u.1^2 + 3*u.2.1^2 + u.2.2.1^2 + 3*u.2.2.2^2 = 1 ∧
  u.1*u.2.1 + u.2.2.1*u.2.2.2 = 0

def against (a v : Pt) : ZMod 5 :=
  a.1*v.1 + a.2.1*v.2.1 + a.2.2.1*v.2.2.1 + a.2.2.2*v.2.2.2

def n (a : Pt) (i : ZMod 5) : ℤ :=
  moves.countP (fun v => decide (against a v = i))

def specL (a : Pt) : ℤ :=
  let a0 := n a 0
  let a1 := n a 1
  let a2 := n a 2
  8*a0 - 4*(a1+a2) + (if a1 ≥ a2 then 8 else 9)*(a1-a2)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem catalogue_exact : ∀ u : Pt, u ∈ moves ↔ isMove u := by
  unfold isMove
  decide +kernel

theorem catalogue_length : moves.length = 24 := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem spectrum_table_bound : ∀ a : Pt, a ≠ 0 →
    n a 1 = n a 4 ∧ n a 2 = n a 3 ∧ -62 ≤ specL a := by
  unfold n specL against
  decide +kernel

/-- The closed numerical eigenvalue formula for every nonzero frequency
satisfies the Hoffman threshold. The identification of these numbers as the
graph spectrum is the Fourier argument in the companion note. -/
theorem eigenvalue_formula_lower (a : Pt) (ha : a ≠ 0) :
    (-31/4 : ℝ) ≤ ((2 : ℝ)*(n a 0 : ℤ) - (n a 1 : ℤ) - (n a 2 : ℤ) +
        ((n a 1 : ℤ) - (n a 2 : ℤ) : ℤ) * Real.sqrt 5) / 2 := by
  have H := (spectrum_table_bound a ha).2.2
  have hs₁ : (2 : ℝ) ≤ Real.sqrt 5 := by
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    nlinarith [Real.sqrt_nonneg 5]
  have hs₂ : Real.sqrt 5 ≤ (9/4 : ℝ) := by
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    nlinarith [Real.sqrt_nonneg 5]
  by_cases h : n a 1 ≥ n a 2
  · unfold specL at H
    simp only [if_pos h] at H
    have Hr : (-62 : ℝ) ≤ 8*(n a 0 : ℤ) - 4*((n a 1 : ℤ)+(n a 2 : ℤ)) +
        8*((n a 1 : ℤ)-(n a 2 : ℤ)) := by exact_mod_cast H
    have h' : (0 : ℝ) ≤ (n a 1 : ℤ) - (n a 2 : ℤ) := by exact_mod_cast sub_nonneg.mpr h
    push_cast
    linarith [mul_nonneg h' (sub_nonneg.mpr hs₁)]
  · unfold specL at H
    simp only [if_neg h] at H
    have Hr : (-62 : ℝ) ≤ 8*(n a 0 : ℤ) - 4*((n a 1 : ℤ)+(n a 2 : ℤ)) +
        9*((n a 1 : ℤ)-(n a 2 : ℤ)) := by exact_mod_cast H
    have h' : (n a 2 : ℤ) - (n a 1 : ℤ) ≥ (0 : ℝ) := by exact_mod_cast sub_nonneg.mpr (le_of_not_ge h)
    push_cast
    linarith [mul_nonneg h' (sub_nonneg.mpr hs₂)]

#print axioms eigenvalue_formula_lower
#print axioms catalogue_exact
#print axioms catalogue_length
#print axioms spectrum_table_bound

end PlaneColouring.Finite25
