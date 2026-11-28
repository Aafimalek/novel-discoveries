import CoeffPoly
import Residue7
import ResidueTorus

namespace CyclotomicModSeven

theorem residue_eval_congr (p : CoeffPoly) (x y : Int) (h : residue x=residue y) :
    residue (eval x p)=residue (eval y p) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [eval,residue_add,residue_mul,h,ih]

theorem phi_residue_three : residue (eval 3 phi42)=0 := by decide +kernel
theorem phi_residue_five : residue (eval 5 phi42)=0 := by decide +kernel

theorem conjugate_swaps_three (p : CoeffPoly) :
    residue (eval (3^41) p)=residue (eval 5 p) :=
  residue_eval_congr p _ _ (by decide +kernel)

theorem conjugate_swaps_five (p : CoeffPoly) :
    residue (eval (5^41) p)=residue (eval 3 p) :=
  residue_eval_congr p _ _ (by decide +kernel)

private theorem zero_mul_f7 : ∀ a : F7, 0*a=0 := by decide +kernel
private theorem sub_zero_f7 : ∀ a b : F7, a-b=0 → a=b := by decide +kernel

/-- Reduction of the exact cyclotomic norm certificate yields the product
of the two reciprocal-root evaluations. -/
theorem residue_norm_of_witness (p : CoeffPoly) (d : Int) (w : CoeffPoly)
    (h : normWitness p d w) :
    residue (eval 3 p) * residue (eval 5 p) = residue d * residue d := by
  have e := congrArg residue (normWitness_eval p d w h 3)
  simp only [residue_sub,residue_mul,phi_residue_three,zero_mul_f7,conjugate_swaps_three] at e
  exact sub_zero_f7 _ _ e

/-- Residue at x of a polynomial divided by an integer prime to seven. -/
def red (x : Int) (p : CoeffPoly) (d : Int) : F7 :=
  residue (eval x p) * inverse (residue d)

def normalizedTrace (p : CoeffPoly) (d : Int) : F7 := red 3 p d + red 5 p d

def localizedColour (p : CoeffPoly) (d : Int) : Fin 4 := group (normalizedTrace p d)

def diffNumerator (p q : CoeffPoly) (d e : Int) : CoeffPoly :=
  polySub (polyScale e p) (polyScale d q)

theorem red_difference (x : Int) (p q : CoeffPoly) (d e : Int)
    (hd : d%7 ≠ 0) (he : e%7 ≠ 0) :
    red x p d - red x q e = red x (diffNumerator p q d e) (d*e) := by
  have h := normalized_sub (residue (eval x p)) (residue (eval x q)) (residue d)
    (residue e) (residue_nonzero_of_prime_to_seven d hd) (residue_nonzero_of_prime_to_seven e he)
  simpa only [red,diffNumerator,eval_sub,eval_scale,residue_sub,residue_mul] using h

/-- The exact four-colour separation on the prime-to-seven witness model.
The assumption is an explicit coefficient-wise norm certificate for the
common-denominator difference, not a hypothesis about rounded reals. -/
theorem localized_colour_separates_of_witness
    (p q : CoeffPoly) (d e : Int) (hd : d%7 ≠ 0) (he : e%7 ≠ 0)
    (w : CoeffPoly) (cert : normWitness (diffNumerator p q d e) (d*e) w) :
    localizedColour p d ≠ localizedColour q e := by
  have hn := residue_norm_of_witness _ _ _ cert
  have Hne : residue (d*e) ≠ 0 := by
    rw [residue_mul]
    exact nonzero_mul _ _ (residue_nonzero_of_prime_to_seven d hd)
      (residue_nonzero_of_prime_to_seven e he)
  have H : red 3 (diffNumerator p q d e) (d*e)*red 5 (diffNumerator p q d e) (d*e)=1 :=
    normalized_pair_norm _ _ _ Hne hn
  apply distinct_of_trace_norm (normalizedTrace p d) (normalizedTrace q e) _ _ H
  rw [normalizedTrace,normalizedTrace,add_sub_pair,red_difference _ _ _ _ _ hd he,
    red_difference _ _ _ _ _ hd he]

theorem residue_norm_graph_four_colourable :
    ∃ c : F7 → F7 → Fin 4, residueProper c := by
  refine ⟨fun x y => group (x+y), ?_⟩
  intro x y u v h
  exact distinct_of_trace_norm (x+y) (u+v) (x-u) (y-v) h (add_sub_pair x y u v)

#print axioms residue_norm_of_witness
#print axioms red_difference
#print axioms localized_colour_separates_of_witness
#print axioms residue_norm_graph_four_colourable

end CyclotomicModSeven
