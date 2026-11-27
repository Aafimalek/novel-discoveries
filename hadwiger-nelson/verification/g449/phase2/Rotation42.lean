import DirectNorm

namespace PlaneColouring.Cyclotomic42

def rotateSix (v : Coeff) : Coeff := ![
  -v 6 + v 7 + -v 8,
  -v 6 + -v 9,
  -v 7 + -v 10,
  v 6 + -v 7 + -v 11,
  v 6,
  v 7,
  v 0 + -v 6 + v 7,
  v 1 + -v 7 + v 8,
  v 2 + v 6 + -v 7 + v 9,
  v 3 + v 6 + v 10,
  v 4 + v 7 + v 11,
  v 5 + -v 6 + v 7]

theorem eval_rotateSix (v : Coeff) : eval (rotateSix v) = zeta ^ 6 * eval v := by
  have H : (1 : ℂ) + (1 : ℂ)*zeta^1 + (-1 : ℂ)*zeta^3 + (-1 : ℂ)*zeta^4 + (1 : ℂ)*zeta^6 + (-1 : ℂ)*zeta^8 + (-1 : ℂ)*zeta^9 + (1 : ℂ)*zeta^11 + (1 : ℂ)*zeta^12 = 0 := by
    have h := phi_relation
    norm_num [eval, phiLow, Fin.sum_univ_succ, Fin.val_succ] at h
    linear_combination h
  norm_num [eval, rotateSix, Fin.sum_univ_succ, Fin.val_succ]
  push_cast
  linear_combination -((v 6 : ℂ)*((1 : ℂ)) + (v 7 : ℂ)*((-1 : ℂ) + (1 : ℂ)*zeta^1) + (v 8 : ℂ)*((1 : ℂ) + (-1 : ℂ)*zeta^1 + (1 : ℂ)*zeta^2) + (v 9 : ℂ)*((1 : ℂ)*zeta^1 + (-1 : ℂ)*zeta^2 + (1 : ℂ)*zeta^3) + (v 10 : ℂ)*((1 : ℂ)*zeta^2 + (-1 : ℂ)*zeta^3 + (1 : ℂ)*zeta^4) + (v 11 : ℂ)*((1 : ℂ)*zeta^3 + (-1 : ℂ)*zeta^4 + (1 : ℂ)*zeta^5))*H

theorem norm_rotateSix (v : Coeff) : normUnreduced (rotateSix v) = normUnreduced v := by
  rw [normUnreduced_eq, normUnreduced_eq, eval_rotateSix, map_mul, map_pow]
  calc
    _ = (zeta*(starRingEnd ℂ) zeta)^6 * (eval v * (starRingEnd ℂ) (eval v)) := by
      rw [mul_pow]
      ring
    _ = _ := by rw [conj_zeta_mul,one_pow,one_mul]

#print axioms eval_rotateSix
#print axioms norm_rotateSix

end PlaneColouring.Cyclotomic42
