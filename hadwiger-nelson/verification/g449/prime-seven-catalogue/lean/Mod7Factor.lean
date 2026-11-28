import Mod7Witness

namespace CyclotomicModSeven

def polyPow (p : CoeffPoly) : Nat → CoeffPoly
  | 0 => [1]
  | n+1 => polyMul p (polyPow p n)

def phi6 : CoeffPoly := [1,-1,1]

/-- The degree-12 Φ42 is congruent coefficientwise to (X²-X+1)⁶ mod 7. -/
theorem phi42_mod7_factor :
    phi42.map residue = (polyPow phi6 6).map residue := by
  decide +kernel

private theorem zero_mul_f7' : ∀ a : F7, 0*a=0 := by decide +kernel
private theorem sub_zero_f7' : ∀ a b : F7, a-b=0 → a=b := by decide +kernel

/-- Equal fractions in the explicit localized coefficient quotient have equal
reduced evaluations. A multiple of Φ42 witnesses the equality. -/
theorem red_respects_fraction_equality
    (x : Int) (hx : residue (eval x phi42)=0)
    (p q : CoeffPoly) (d e : Int) (hd : d%7 ≠ 0) (he : e%7 ≠ 0)
    (w : CoeffPoly)
    (eq : coeffEq (diffNumerator p q d e) (polyMul phi42 w)) :
    red x p d = red x q e := by
  have ev := congrArg residue (eval_of_coeffEq x _ _ eq)
  rw [eval_mul,residue_mul,hx,zero_mul_f7'] at ev
  have E := red_difference x p q d e hd he
  simp only [red,ev,zero_mul_f7'] at E
  exact sub_zero_f7' _ _ E

theorem localized_colour_respects_fraction_equality
    (p q : CoeffPoly) (d e : Int) (hd : d%7 ≠ 0) (he : e%7 ≠ 0)
    (w : CoeffPoly)
    (eq : coeffEq (diffNumerator p q d e) (polyMul phi42 w)) :
    localizedColour p d = localizedColour q e := by
  unfold localizedColour normalizedTrace
  rw [red_respects_fraction_equality 3 phi_residue_three _ _ _ _ hd he w eq,
    red_respects_fraction_equality 5 phi_residue_five _ _ _ _ hd he w eq]

/-- No graph with such localized, norm-certified edges requires five colours. -/
theorem graph_colourable_of_prime_to_seven_norm_certificates
    {V : Type} (p : V → CoeffPoly) (d : V → Int)
    (prime : ∀ v, d v % 7 ≠ 0) (E : V → V → Prop)
    (cert : ∀ a b, E a b → ∃ w : CoeffPoly, normWitness
      (diffNumerator (p a) (p b) (d a) (d b)) (d a * d b) w) :
    ∃ colour : V → Fin 4, ∀ a b, E a b → colour a ≠ colour b := by
  refine ⟨fun v => localizedColour (p v) (d v), ?_⟩
  intro a b h
  obtain ⟨w,hcode⟩ := cert a b h
  exact localized_colour_separates_of_witness _ _ _ _ (prime a) (prime b) w hcode

#print axioms phi42_mod7_factor
#print axioms localized_colour_respects_fraction_equality
#print axioms graph_colourable_of_prime_to_seven_norm_certificates
end CyclotomicModSeven
