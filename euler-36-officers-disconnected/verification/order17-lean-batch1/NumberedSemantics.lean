import EulerNumbering
import Mathlib.Tactic.Sat.FromLRAT

namespace LatinGap.PairEncoding

/-- Shift a one-based numeric Boolean assignment to Mathlib's zero-based
SAT valuation without changing the represented variable values. -/
def dimacsSatValuation (v : ℕ → Bool) : Sat.Valuation :=
  fun i => v (i+1) = true

theorem negate_dimacsLit_iff (v : ℕ → Bool) (l : ℤ) (nz : l ≠ 0) :
    (dimacsSatValuation v).neg (Sat.Literal.ofInt l) ↔
      ¬ v l.natAbs = decide (0 < l) := by
  by_cases h : l < 0
  · have e : (-l-1).toNat+1 = l.natAbs := by omega
    have hn : ¬ 0 < l := by omega
    rw [Sat.Literal.ofInt, if_pos h]
    change v ((-l-1).toNat+1) = true ↔ ¬ v l.natAbs = decide (0<l)
    rw [e, decide_eq_false hn]
    cases v l.natAbs <;> decide
  · have hpos : 0 < l := by omega
    have e : (l-1).toNat+1 = l.natAbs := by omega
    rw [Sat.Literal.ofInt, if_neg h]
    change (¬ v ((l-1).toNat+1) = true) ↔ ¬ v l.natAbs = decide (0<l)
    rw [e,decide_eq_true hpos]

def asSatNumberedClause (c : List ℤ) : Sat.Clause :=
  c.map Sat.Literal.ofInt

def asSatNumberedFormula (cs : List (List ℤ)) : Sat.Fmla :=
  cs.map asSatNumberedClause

theorem holds_numbered_cons_iff (v : ℕ → Bool) (l : ℤ) (c : List ℤ) (nz : l ≠ 0) :
    NumberedHolds v (l::c) ↔
      (v l.natAbs = decide (0 < l)) ∨ NumberedHolds v c := by
  constructor
  · rintro ⟨a,ha,nzA,valA⟩
    rcases List.mem_cons.mp ha with h | h
    · subst a; exact Or.inl valA
    · exact Or.inr ⟨a,h,nzA,valA⟩
  · rintro (h | ⟨a,ha,nzA,valA⟩)
    · exact ⟨l,List.mem_cons_self,nz,h⟩
    · exact ⟨a,List.mem_cons_of_mem _ ha,nzA,valA⟩

/-- A signed numeric clause is satisfied precisely by the proposition
used in the certified Mathlib RUP refutations. -/
theorem numberedHolds_iff_sat_satisfies (v : ℕ → Bool) (c : List ℤ)
    (nz : ∀ l ∈ c, l ≠ 0) :
    NumberedHolds v c ↔ (dimacsSatValuation v).satisfies (asSatNumberedClause c) := by
  induction c with
  | nil => simp [NumberedHolds, asSatNumberedClause, Sat.Valuation.satisfies]
  | cons l c ih =>
    have nzL := nz l List.mem_cons_self
    have nzC : ∀ t ∈ c, t ≠ 0 := fun x hx => nz x (List.mem_cons_of_mem _ hx)
    rw [holds_numbered_cons_iff v l c nzL, ih nzC]
    change (_ ∨ _) ↔ ((dimacsSatValuation v).neg (Sat.Literal.ofInt l) →
      (dimacsSatValuation v).satisfies (asSatNumberedClause c))
    rw [negate_dimacsLit_iff v l nzL]
    by_cases e : v l.natAbs = decide (0 < l) <;> simp [e]

theorem numberedFormula_iff_sat_satisfies (v : ℕ → Bool) (cs : List (List ℤ))
    (nz : ∀ c ∈ cs, ∀ l ∈ c, l ≠ 0) :
    (∀ c ∈ cs, NumberedHolds v c) ↔
      (dimacsSatValuation v).satisfies_fmla (asSatNumberedFormula cs) := by
  constructor
  · intro h
    refine ⟨fun c hc => ?_⟩
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    exact (numberedHolds_iff_sat_satisfies v d (nz d hd)).mp (h d hd)
  · intro h c hc
    exact (numberedHolds_iff_sat_satisfies v c (nz c hc)).mpr
      (h.1 _ (List.mem_map_of_mem hc))

/-- An empty-clause proof in the kernel refutes numbered Boolean
assignments directly, provided the exact formula is the signed list. -/
theorem numberedUnsat_of_kernel_proof (cs : List (List ℤ))
    (nz : ∀ c ∈ cs, ∀ l ∈ c, l ≠ 0)
    (h : (asSatNumberedFormula cs).proof Sat.Clause.nil) :
    ¬ ∃ v : ℕ → Bool, ∀ c ∈ cs, NumberedHolds v c := by
  rintro ⟨v,hv⟩
  exact h _ ((numberedFormula_iff_sat_satisfies v cs nz).mp hv)

#print axioms negate_dimacsLit_iff
#print axioms numberedHolds_iff_sat_satisfies
#print axioms numberedFormula_iff_sat_satisfies
#print axioms numberedUnsat_of_kernel_proof

end LatinGap.PairEncoding
