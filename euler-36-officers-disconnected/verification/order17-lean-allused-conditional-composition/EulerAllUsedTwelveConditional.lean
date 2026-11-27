import EulerAllUsedConditionalRefutations

namespace LatinGap.PairEncoding
open EulerAllUsedDiagrams

/-- The exact diagram codes corresponding to the 12 currently checked
whole-archive SAT refutations. This list does not install the separate
trusted-kernel equality witnesses to the geometric clause model. -/
def archivedCheckedTwelve : List (List ℕ) :=
  [[111,1012,1103,1220], [111,1012,1201,1120],
   [111,1012,1201,1320], [111,1012,1201,2120],
   [111,1012,2201,1220], [111,1012,1201,2320],
   [111,1012,1103,2220], [111,1012,1203,2120],
   [111,1012,2201,1320], [111,1012,1203,2320],
   [111,1012,2203,2320], [111,1012,1203,1320]]

def archivedRemainingFive : List (List ℕ) :=
  [[111,1012,2201,3120], [111,1012,2201,3320],
   [111,1012,2203,3310], [111,1012,2203,3320],
   [111,1022,2203,3330]]

theorem checkedTwelve_complement : remainingAllUsedDiagrams archivedCheckedTwelve = archivedRemainingFive := by
  decide +kernel

/-- The five-diagram reduction requires the exact checked contents
link between each of the 12 refutations and its geometric clause model. -/
theorem allUsed_geometry_only_five_given_links {D : Design 6} (lin : Linear D)
    (sat : Saturated D) (size : D.card=17) (min : ∀ x : Label 6, 2 ≤ freq D x)
    (allused : ∀ (i j : Coord) (a b : Fin 6), i ≠ j →
      freq D (i,a)=2 → freq D (j,b)=2 → Used D (i,a) (j,b))
    (links : ∀ codes ∈ archivedCheckedTwelve, ∃ f : Sat.Fmla,
      f.proof Sat.Clause.nil ∧ (asSatNumberedFormula (archiveAllUsedCNF codes)).subsumes f) :
    ∃ codes ∈ archivedRemainingFive, ∃ v : ℕ → Bool,
      ∀ c ∈ archiveAllUsedCNF codes, NumberedHolds v c := by
  rw [← checkedTwelve_complement]
  refine allUsed_geometry_only_remaining lin sat size min allused archivedCheckedTwelve ?_
  intro codes hc
  obtain ⟨f,refuted,inc⟩ := links codes hc
  exact archiveAllUsedNoModel_of_refuted_subsumed codes f inc refuted

#print axioms checkedTwelve_complement
#print axioms allUsed_geometry_only_five_given_links
end LatinGap.PairEncoding
