import CyclotomicWitness
namespace PlaneColouring.Cyclotomic42

/-- Unreduced Laurent product, with exponents shifted by the period 42. -/
noncomputable def normUnreduced (v : Coeff) : ℂ :=
  ∑ i, ∑ j, (v i : ℂ) * (v j : ℂ) * zeta ^ (i.val + (42-j.val))

theorem normUnreduced_eq (v : Coeff) :
    normUnreduced v = eval v * (starRingEnd ℂ) (eval v) := by
  unfold normUnreduced eval
  simp only [map_sum, map_mul]
  simp only [show ∀ x : ℤ, (starRingEnd ℂ) (x : ℂ) = x by intro x; simp,
    eval_conj_pow, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  ring

/-- A complex norm certificate gives the claimed geometric distance. -/
theorem dist_one_of_unreduced (a b : Coeff)
    (check : normUnreduced (diff a b) = (49^2 : ℂ)) :
    dist (point a) (point b) = 1 := by
  rw [normUnreduced_eq,Complex.mul_conj] at check
  have hQ : Complex.normSq (eval (diff a b)) = (49^2 : ℝ) := by exact_mod_cast check
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

theorem normUnreduced_neg (a : Coeff) :
    normUnreduced (fun i => -a i) = normUnreduced a := by
  unfold normUnreduced
  simp only [Int.cast_neg, neg_mul_neg]

#print axioms dist_one_of_unreduced
#print axioms normUnreduced_neg

end PlaneColouring.Cyclotomic42
