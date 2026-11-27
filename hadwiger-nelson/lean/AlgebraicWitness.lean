import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

namespace PlaneColouring

/-- Rational coefficients in the basis 1, √r, √s, √r√s. No field structure
or independence assumptions are needed for the soundness direction. -/
structure Radical4 where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  deriving DecidableEq, Repr

namespace Radical4

def one : Radical4 := ⟨1,0,0,0⟩
def sub (x y : Radical4) : Radical4 := ⟨x.a-y.a,x.b-y.b,x.c-y.c,x.d-y.d⟩
def add (x y : Radical4) : Radical4 := ⟨x.a+y.a,x.b+y.b,x.c+y.c,x.d+y.d⟩

def sq (r s : ℚ) (x : Radical4) : Radical4 :=
  ⟨x.a^2+r*x.b^2+s*x.c^2+r*s*x.d^2,
    2*(x.a*x.b+s*x.c*x.d),
    2*(x.a*x.c+r*x.b*x.d),
    2*(x.a*x.d+x.b*x.c)⟩

noncomputable def eval (r s : ℚ) (x : Radical4) : ℝ :=
  x.a + x.b * Real.sqrt (r : ℝ) + x.c * Real.sqrt (s : ℝ) +
    x.d * Real.sqrt (r : ℝ) * Real.sqrt (s : ℝ)

theorem eval_one (r s : ℚ) : eval r s one = 1 := by
  norm_num [eval, one]

theorem eval_sub (r s : ℚ) (x y : Radical4) :
    eval r s (sub x y) = eval r s x - eval r s y := by
  simp only [eval, sub, Rat.cast_sub]
  ring

theorem eval_add (r s : ℚ) (x y : Radical4) :
    eval r s (add x y) = eval r s x + eval r s y := by
  simp only [eval, add, Rat.cast_add]
  ring

theorem eval_sq (r s : ℚ) (hr : 0 ≤ r) (hs : 0 ≤ s) (x : Radical4) :
    eval r s (sq r s x) = eval r s x ^ 2 := by
  have hr' : 0 ≤ (r : ℝ) := by exact_mod_cast hr
  have hs' : 0 ≤ (s : ℝ) := by exact_mod_cast hs
  have eqr := Real.sq_sqrt hr'
  have eqs := Real.sq_sqrt hs'
  simp only [eval, sq, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  rw [← eqr, ← eqs]
  simp only [Real.sqrt_sq (Real.sqrt_nonneg _)]
  ring

end Radical4

abbrev Coordinate := Radical4 × Radical4
abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def coordinateEval (r s : ℚ) (a : Coordinate) : Plane :=
  !₂[Radical4.eval r s a.1, Radical4.eval r s a.2]

def unitTest (r s : ℚ) (a b : Coordinate) : Bool :=
  decide (Radical4.add (Radical4.sq r s (Radical4.sub a.1 b.1))
    (Radical4.sq r s (Radical4.sub a.2 b.2)) = Radical4.one)

/-- A coefficientwise rational check is enough to certify a claimed unit edge
in the same Euclidean metric as the unrestricted Hadwiger–Nelson problem. -/
theorem dist_eq_one_of_unitTest (r s : ℚ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (a b : Coordinate) (h : unitTest r s a b = true) :
    dist (coordinateEval r s a) (coordinateEval r s b) = 1 := by
  have h₁ := congrArg (Radical4.eval r s) (of_decide_eq_true h)
  rw [Radical4.eval_add, Radical4.eval_sq _ _ hr hs,
    Radical4.eval_sq _ _ hr hs, Radical4.eval_sub, Radical4.eval_sub,
    Radical4.eval_one] at h₁
  have h₂ := EuclideanSpace.dist_sq_eq (coordinateEval r s a) (coordinateEval r s b)
  simp only [Fin.sum_univ_two, coordinateEval, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.dist_eq, sq_abs] at h₂
  have nonneg : 0 ≤ dist (coordinateEval r s a) (coordinateEval r s b) := dist_nonneg
  rw [h₁] at h₂
  change dist (coordinateEval r s a) (coordinateEval r s b) ^ 2 = 1 at h₂
  nlinarith

def Proper (k : ℕ) (colour : Plane → Fin k) : Prop :=
  ∀ a b, dist a b = 1 → colour a ≠ colour b

/-- Generic interface: a refutation of a finite color assignment strengthens
the chromatic lower bound for the entire plane once its edges pass unitTest. -/
theorem no_plane_colouring_of_radical_witness (r s : ℚ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (n k : ℕ) (pts : Fin n → Coordinate) (edges : List (Fin n × Fin n))
    (euclidean : ∀ e ∈ edges, unitTest r s (pts e.1) (pts e.2) = true)
    (unsat : ¬ ∃ colour : Fin n → Fin k, ∀ e ∈ edges, colour e.1 ≠ colour e.2) :
    ¬ ∃ colour : Plane → Fin k, Proper k colour := by
  rintro ⟨colour, hp⟩
  apply unsat
  refine ⟨fun i => colour (coordinateEval r s (pts i)), ?_⟩
  intro e he
  exact hp _ _ (dist_eq_one_of_unitTest r s hr hs _ _ (euclidean e he))

#print axioms dist_eq_one_of_unitTest
#print axioms no_plane_colouring_of_radical_witness

end PlaneColouring
