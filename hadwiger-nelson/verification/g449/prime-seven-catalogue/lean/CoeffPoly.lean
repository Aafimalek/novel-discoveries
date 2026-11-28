import Init

namespace CyclotomicModSeven

abbrev CoeffPoly := List Int

def eval (x : Int) : CoeffPoly → Int
  | [] => 0
  | a::p => a+x*eval x p

def polyAdd : CoeffPoly → CoeffPoly → CoeffPoly
  | [], q => q
  | a::p, [] => a::p
  | a::p, b::q => (a+b)::polyAdd p q

def polyNeg (p : CoeffPoly) : CoeffPoly := p.map Int.neg

def polySub (p q : CoeffPoly) : CoeffPoly := polyAdd p (polyNeg q)

def polyScale (a : Int) (p : CoeffPoly) : CoeffPoly := p.map (a * ·)

def polyMul : CoeffPoly → CoeffPoly → CoeffPoly
  | [], _ => []
  | a::p, q => polyAdd (polyScale a q) (0::polyMul p q)

def xPow : Nat → CoeffPoly
  | 0 => [1]
  | n+1 => 0::xPow n

def polyComp : CoeffPoly → CoeffPoly → CoeffPoly
  | [], _ => []
  | a::p, q => polyAdd [a] (polyMul q (polyComp p q))

def coeffEq (p q : CoeffPoly) : Prop := ∀ n, p.getD n 0=q.getD n 0

theorem eval_add (x : Int) (p q : CoeffPoly) :
    eval x (polyAdd p q)=eval x p+eval x q := by
  induction p generalizing q with
  | nil => simp [eval,polyAdd]
  | cons a p ih =>
    cases q with
    | nil => simp [eval,polyAdd]
    | cons b q =>
      simp only [eval,polyAdd,ih,Int.mul_add]
      omega

theorem eval_neg (x : Int) (p : CoeffPoly) : eval x (polyNeg p) = -eval x p := by
  induction p with
  | nil => simp [eval,polyNeg]
  | cons a p ih =>
    simp only [eval,polyNeg,List.map_cons] at ih ⊢
    rw [ih,Int.mul_neg]
    change -a + -(x*eval x p) = -(a+x*eval x p)
    omega

theorem eval_sub (x : Int) (p q : CoeffPoly) :
    eval x (polySub p q)=eval x p-eval x q := by
  rw [polySub,eval_add,eval_neg,Int.sub_eq_add_neg]

theorem eval_scale (x a : Int) (p : CoeffPoly) :
    eval x (polyScale a p)=a*eval x p := by
  induction p with
  | nil => simp [eval,polyScale]
  | cons b p ih =>
    simp only [eval,polyScale,List.map_cons,Int.mul_add] at ih ⊢
    rw [ih,Int.mul_left_comm x a]

theorem eval_mul (x : Int) (p q : CoeffPoly) :
    eval x (polyMul p q)=eval x p*eval x q := by
  induction p with
  | nil => simp [eval,polyMul]
  | cons a p ih =>
    rw [polyMul,eval_add,eval_scale,eval,eval,ih,Int.add_mul,Int.mul_assoc]
    simp

theorem eval_xPow (x : Int) (n : Nat) : eval x (xPow n)=x^n := by
  induction n with
  | zero => simp [eval,xPow]
  | succ n ih =>
    simp only [eval,xPow,ih,Int.zero_add,Int.pow_succ]
    exact Int.mul_comm _ _

theorem eval_comp (x : Int) (p q : CoeffPoly) :
    eval x (polyComp p q)=eval (eval x q) p := by
  induction p with
  | nil => simp [eval,polyComp]
  | cons a p ih =>
    rw [polyComp,eval_add,eval_mul,ih]
    simp [eval]

theorem eval_eq_zero_of_coeffs (x : Int) (p : CoeffPoly)
    (h : ∀ n, p.getD n 0=0) : eval x p=0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have ha : a=0 := h 0
    have hp : ∀ n, p.getD n 0=0 := fun n => h (n+1)
    simp [eval,ha,ih hp]

theorem eval_of_coeffEq (x : Int) (p q : CoeffPoly) (h : coeffEq p q) :
    eval x p = eval x q := by
  induction p generalizing q with
  | nil =>
    exact (eval_eq_zero_of_coeffs x q (fun n => (h n).symm)).symm
  | cons a p ih =>
    cases q with
    | nil => exact eval_eq_zero_of_coeffs x (a::p) h
    | cons b q =>
      have e : a=b := h 0
      have eq : coeffEq p q := fun n => h (n+1)
      simp [eval,e,ih q eq]

def phi42 : CoeffPoly := [1,1,0,-1,-1,0,1,0,-1,-1,0,1,1]

/-- Coefficient certificate for a common-denominator numerator: the shifted
conjugate represents the real-field conjugation X ↦ X⁴¹ at a 42nd root. -/
def normWitness (p : CoeffPoly) (d : Int) (w : CoeffPoly) : Prop :=
  coeffEq (polySub (polyMul p (polyComp p (xPow 41))) [d*d]) (polyMul phi42 w)

theorem normWitness_eval (p : CoeffPoly) (d : Int) (w : CoeffPoly)
    (h : normWitness p d w) (x : Int) :
    eval x p * eval (x^41) p-d*d = eval x phi42*eval x w := by
  have E := eval_of_coeffEq x _ _ h
  simp only [eval_sub,eval_mul,eval_comp,eval_xPow] at E
  simpa [eval] using E

#print axioms eval_of_coeffEq
#print axioms normWitness_eval
end CyclotomicModSeven
