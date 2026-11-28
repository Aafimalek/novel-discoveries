import FranklSingleTripleEndpoint
import FranklFourAllPairEndpoint

/- Checked by pinned ordinary Lean with warnings as errors. -/
namespace FranklForcingFiber
open FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

/-- Assembly limited to at least two sources and maximum deficit at
most one. It does not cover deficit two or the bound on max deficit. -/
theorem exact_four_not_multiple_sources_of_deficit_le_one {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hI : (isolated G).card = 4) (hk : 2 ≤ (sources G).card)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 2) :
    False := by
  classical
  let C := triples (starBlocks G)
  by_cases hMany : 2 ≤ C.card
  · exact exact_four_deficit_le_one_not_many_triples hG hm hI hDeg hMany
  by_cases hOne : C.card = 1
  · obtain ⟨T,hT⟩ := Finset.card_eq_one.mp hOne
    exact exact_four_deficit_le_one_not_single_triple hG hm hI hDeg hT
  have he : C = ∅ := Finset.card_eq_zero.mp (by omega)
  have hD := starBlocks_pairDesign hG hm
  have h3 := (deficit_le_one_triples_classification hD hDeg).1
  have hB : AllOrdinaryStarPairs G := by
    intro A hA
    have hlo := (hD.1 A hA).2
    have hhi := h3 A hA
    by_contra hn
    have hAc : A.card = 3 := by omega
    have hAT : A ∈ C := Finset.mem_filter.mpr ⟨hA,hAc⟩
    simp [he] at hAT
  exact exact_four_allPair_not_multiple_sources hG hm hI hB hk

#print axioms exact_four_not_multiple_sources_of_deficit_le_one
end FranklForcingFiber
