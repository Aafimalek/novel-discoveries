import FranklFourAllPairTwo
import FranklFourAllPairThree

/- Direct Lean-checked all-pair d=0 branch and supporting lemmas. -/
namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

/-- All-pair d=0 branch only. This excludes exactly four isolates and
at least two sources when every omitted-star block is an ordinary pair.
It does not address other omitted-block designs (d=1 or d=2). -/
theorem exact_four_allPair_not_multiple_sources {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hI : (isolated G).card = 4) (hB : AllOrdinaryStarPairs G)
    (hk : 2 ≤ (sources G).card) : False := by
  by_cases h2 : (sources G).card = 2
  · exact exact_four_allPair_not_two_sources hG hm hI hB h2
  by_cases h3 : (sources G).card = 3
  · exact exact_four_allPair_not_three_sources hG hm hI hB h3
  exact exact_four_allPair_not_four_le_sources hG hm hI hB (by omega)

#print axioms exact_four_allPair_not_multiple_sources
end FranklForcingFiber
