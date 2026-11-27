import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.RingTheory.RootsOfUnity.Complex

open scoped BigOperators

namespace PlaneColouring.Cyclotomic42

abbrev Coeff := Fin 12 → ℤ
abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def zeta : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 42)

theorem zeta_primitive : IsPrimitiveRoot zeta 42 := by
  simpa [zeta] using Complex.isPrimitiveRoot_exp 42 (by decide)

theorem zeta_pow : zeta ^ 42 = 1 := zeta_primitive.pow_eq_one

theorem zeta_ne_zero : zeta ≠ 0 := Complex.exp_ne_zero _

theorem conj_zeta_mul : zeta * (starRingEnd ℂ) zeta = 1 := by
  have hn : ‖zeta‖ = 1 := by
    unfold zeta
    rw [Complex.norm_exp]
    simp [div_eq_mul_inv, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im,
      Complex.normSq_apply]
  rw [Complex.mul_conj, ← Complex.sq_norm, hn, one_pow, Complex.ofReal_one]

def phiLow : Coeff := ![1,1,0,-1,-1,0,1,0,-1,-1,0,1]

noncomputable def eval (v : Coeff) : ℂ := ∑ i, (v i : ℂ) * zeta ^ (i : ℕ)

theorem phi_relation : zeta ^ 12 + eval phiLow = 0 := by
  have z21 : zeta ^ 21 = -1 := by
    have z42 : (zeta ^ 21)^2 = (1 : ℂ)^2 := by rw [← pow_mul]; norm_num [zeta_pow]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp z42 with one | neg
    · exact False.elim (by have f := (zeta_primitive.pow_eq_one_iff_dvd 21).mp one; norm_num at f)
    · exact neg
  have nz7 : zeta ^ 7 + 1 ≠ 0 := by
    intro h
    have h' : zeta ^ 7 = -1 := eq_neg_of_add_eq_zero_left h
    have z14 : zeta ^ 14 = 1 := by rw [show (14 : ℕ) = 7*2 by decide, pow_mul, h']; norm_num
    have f := (zeta_primitive.pow_eq_one_iff_dvd 14).mp z14
    norm_num at f
  have nz3 : zeta ^ 3 + 1 ≠ 0 := by
    intro h
    have h' : zeta ^ 3 = -1 := eq_neg_of_add_eq_zero_left h
    have z6 : zeta ^ 6 = 1 := by rw [show (6 : ℕ) = 3*2 by decide, pow_mul, h']; norm_num
    have f := (zeta_primitive.pow_eq_one_iff_dvd 6).mp z6
    norm_num at f
  refine (mul_eq_zero.mp (show (zeta^7+1)*(zeta^3+1)*(zeta^12+eval phiLow) = 0 from ?_)).resolve_left
    (mul_ne_zero nz7 nz3)
  calc
    _ = (zeta ^ 21 + 1) * (zeta + 1) := by
      norm_num [eval,phiLow,Fin.sum_univ_succ,Fin.val_succ]
      ring
    _ = 0 := by rw [z21]; ring

def start : Coeff := ![1,0,0,0,0,0,0,0,0,0,0,0]

def shift (v : Coeff) : Coeff :=
  fun i => (if h : 0 < i.val then v ⟨i.val-1, by omega⟩ else 0) - v 11 * phiLow i

theorem eval_start : eval start = 1 := by
  norm_num [eval,start,Fin.sum_univ_succ,Fin.val_succ]

theorem eval_shift (v : Coeff) : eval (shift v) = zeta * eval v := by
  have h := phi_relation
  unfold eval at h ⊢
  simp only [Fin.sum_univ_succ] at h ⊢
  norm_num [shift,phiLow,Fin.val_succ] at h ⊢
  linear_combination -(v 11 : ℂ)*h

def checkedPowers (T : Fin 54 → Coeff) : Prop :=
  (∀ i, T 0 i = start i) ∧
  (∀ (j : Fin 53) i, T j.succ i = shift (T j.castSucc) i)

theorem eval_powerTable (T : Fin 54 → Coeff) (chk : checkedPowers T) (j : Fin 54) :
    eval (T j) = zeta ^ (j : ℕ) := by
  obtain ⟨h1,h2⟩ := chk
  induction j using Fin.induction with
  | zero => rw [show T 0 = start from funext h1, eval_start]; rfl
  | succ j ih =>
    rw [show T j.succ = shift (T j.castSucc) from funext (h2 j),eval_shift,ih]
    simp only [Fin.val_succ,Fin.val_castSucc,pow_succ']
  
def indexPow (i j : Fin 12) : Fin 54 :=
  ⟨i.val + (42-j.val), by omega⟩

def normCoeffs (T : Fin 54 → Coeff) (v : Coeff) : Coeff :=
  fun t => ∑ i, ∑ j, v i * v j * T (indexPow i j) t

theorem eval_conj_pow (j : Fin 12) : (starRingEnd ℂ) (zeta ^ (j : ℕ)) = zeta ^ (42 - j.val) := by
  apply mul_left_cancel₀ (pow_ne_zero j.val zeta_ne_zero)
  have h : j.val + (42-j.val) = 42 := by omega
  rw [← pow_add, h, zeta_pow, map_pow, ← mul_pow, conj_zeta_mul, one_pow]

theorem eval_normCoeffs (T : Fin 54 → Coeff) (chk : checkedPowers T) (v : Coeff) :
    eval (normCoeffs T v) = eval v * (starRingEnd ℂ) (eval v) := by
  unfold eval normCoeffs
  simp only [Int.cast_sum, Finset.sum_mul, Int.cast_mul, map_sum, map_mul]
  simp only [show ∀ x : ℤ, (starRingEnd ℂ) (x : ℂ) = x by intro x; simp,
    eval_conj_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum,← Finset.mul_sum, ←mul_assoc]
  have E := eval_powerTable T chk (indexPow i j)
  unfold eval at E
  rw [E]
  unfold indexPow
  simp only [Fin.val_mk,pow_add]
  ring

def diff (a b : Coeff) : Coeff := fun i => a i - b i

theorem eval_diff (a b : Coeff) : eval (diff a b) = eval a - eval b := by
  unfold eval diff
  simp only [Int.cast_sub,sub_mul,Finset.sum_sub_distrib]

noncomputable def point (a : Coeff) : Plane :=
  let x := eval a / 49
  !₂[x.re,x.im]

theorem dist_one_of_normCoeffs (T : Fin 54 → Coeff) (chk : checkedPowers T) (a b : Coeff)
    (hv : ∀ i, normCoeffs T (diff a b) i = (49^2 : ℤ) * start i) :
    dist (point a) (point b) = 1 := by
  have P := eval_normCoeffs T chk (diff a b)
  rw [show normCoeffs T (diff a b) = fun i => (49^2 : ℤ)*start i from funext hv] at P
  have he : eval (fun i => (49^2 : ℤ)*start i) = (49^2 : ℂ) := by
    unfold eval
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat,mul_assoc,← Finset.mul_sum]
    change 49^2 * eval start = (49^2 : ℂ)
    rw [eval_start,mul_one]
  rw [he,Complex.mul_conj] at P
  have hQ : Complex.normSq (eval (diff a b)) = (49^2 : ℝ) := by exact_mod_cast P.symm
  have H : eval a/49 - eval b/49 = eval (diff a b)/49 := by rw [eval_diff,sub_div]
  have HU : Complex.normSq (eval a/49 - eval b/49) = 1 := by
    rw [H,Complex.normSq_div,hQ]
    norm_num [Complex.normSq_apply]
  have Eq := EuclideanSpace.dist_sq_eq (point a) (point b)
  simp only [Fin.sum_univ_two,point,Matrix.cons_val_zero,Matrix.cons_val_one,Real.dist_eq,sq_abs] at Eq
  rw [Complex.normSq_apply,Complex.sub_re,Complex.sub_im] at HU
  have hdist : dist (point a) (point b)^2 = 1 := by
    change dist (point a) (point b)^2 = _ at Eq
    nlinarith
  have hn : 0 ≤ dist (point a) (point b) := dist_nonneg
  nlinarith

#print axioms dist_one_of_normCoeffs
#print axioms phi_relation
#print axioms eval_powerTable
#print axioms eval_normCoeffs

end PlaneColouring.Cyclotomic42
