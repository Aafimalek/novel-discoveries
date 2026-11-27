import EulerAllUsedFullGeometry
import EulerBatch.NumberedSemantics

namespace LatinGap.PairEncoding
open EulerAllUsedDiagrams

/-- In the direction needed for UNSAT transfer, the numbered satisfaction
witness is already nonzero. Other literals need not be checked nonzero. -/
theorem numberedHolds_sat_forward (v : ℕ → Bool) (c : List ℤ)
    (h : NumberedHolds v c) :
    (dimacsSatValuation v).satisfies (asSatNumberedClause c) := by
  induction c with
  | nil => obtain ⟨_, hm, _, _⟩ := h; cases hm
  | cons l tail ih =>
    obtain ⟨a,mem,nz,good⟩ := h
    change (dimacsSatValuation v).neg (Sat.Literal.ofInt l) →
      (dimacsSatValuation v).satisfies (asSatNumberedClause tail)
    intro no
    rcases List.mem_cons.mp mem with h | h
    · subst a
      exact False.elim ((negate_dimacsLit_iff v l nz).mp no good)
    · exact ih ⟨a,h,nz,good⟩

theorem numberedFormula_sat_forward (v : ℕ → Bool) (cs : List (List ℤ))
    (h : ∀ c ∈ cs, NumberedHolds v c) :
    (dimacsSatValuation v).satisfies_fmla (asSatNumberedFormula cs) := by
  refine ⟨fun c hc => ?_⟩
  obtain ⟨row,hr,rfl⟩ := List.mem_map.mp hc
  exact numberedHolds_sat_forward v row (h row hr)

/-- A refuted formula included in a modeled archive rules out every
numbered model of that archive. Whole-formula identity is sufficient
but not necessary: checked containment of a refuted core suffices. -/
theorem archiveAllUsedNoModel_of_refuted_subsumed (codes : List ℕ) (f : Sat.Fmla)
    (inc : (asSatNumberedFormula (archiveAllUsedCNF codes)).subsumes f)
    (refuted : f.proof Sat.Clause.nil) :
    ¬ ∃ v : ℕ → Bool, ∀ c ∈ archiveAllUsedCNF codes, NumberedHolds v c := by
  rintro ⟨v,hv⟩
  have hs := numberedFormula_sat_forward v _ hv
  exact refuted _ ⟨fun c hc => hs.1 c (inc.1 c hc)⟩

theorem archiveAllUsedNoModel_of_exact_refutation (codes : List ℕ) (f : Sat.Fmla)
    (same : asSatNumberedFormula (archiveAllUsedCNF codes) = f)
    (refuted : f.proof Sat.Clause.nil) :
    ¬ ∃ v : ℕ → Bool, ∀ c ∈ archiveAllUsedCNF codes, NumberedHolds v c := by
  apply archiveAllUsedNoModel_of_refuted_subsumed codes f ?_ refuted
  rw [same]
  exact Sat.Fmla.subsumes_self _

def remainingAllUsedDiagrams (excluded : List (List ℕ)) : List (List ℕ) :=
  published.filter fun c => !(excluded.contains c)

/-- Once a set of published archives has checked no-model theorems, a
hypothetical actual all-used design must be represented by an archive
outside that set, with a satisfying numbered valuation. -/
theorem allUsed_geometry_only_remaining {D : Design 6} (lin : Linear D)
    (sat : Saturated D) (size : D.card=17) (min : ∀ x : Label 6, 2 ≤ freq D x)
    (allused : ∀ (i j : Coord) (a b : Fin 6), i ≠ j →
      freq D (i,a)=2 → freq D (j,b)=2 → Used D (i,a) (j,b))
    (excluded : List (List ℕ))
    (noModel : ∀ codes ∈ excluded, ¬ ∃ v : ℕ → Bool,
      ∀ c ∈ archiveAllUsedCNF codes, NumberedHolds v c) :
    ∃ codes ∈ remainingAllUsedDiagrams excluded, ∃ v : ℕ → Bool,
      ∀ c ∈ archiveAllUsedCNF codes, NumberedHolds v c := by
  obtain ⟨codes,pub,v,hv⟩ := allUsed_geometry_full_archive lin sat size min allused
  refine ⟨codes,?_,v,hv⟩
  have notExcluded : codes ∉ excluded := fun h => noModel codes h ⟨v,hv⟩
  simpa [remainingAllUsedDiagrams,notExcluded] using pub

#print axioms numberedFormula_sat_forward
#print axioms archiveAllUsedNoModel_of_refuted_subsumed
#print axioms archiveAllUsedNoModel_of_exact_refutation
#print axioms allUsed_geometry_only_remaining
end LatinGap.PairEncoding
