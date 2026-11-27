import Lean

namespace WidthThree.LayerArithmetic

/-- Two marginals whose difference is bounded by less than a third cannot
straddle the forbidden middle interval. -/
theorem sameSide_of_smallGap (total low high gap : Nat)
    (hgap : high ≤ low + gap) (hgapSmall : 3 * gap < total)
    (hlo : 3 * low < total) : ¬ 2 * total < 3 * high := by
  omega

/-- After the first rank, the arithmetic excludes a jump from a low singleton
to a high pair. The pair's numerator is the sum of two marginal counts. -/
theorem no_lateSingleton_to_pair (total low highSum q : Nat)
    (hlow : 3 * low < total)
    (hprev : 2 * q ≤ low)
    (hstep : highSum ≤ 2 * low + 3 * q) :
    ¬ 4 * total < 3 * highSum := by
  omega

/-- The numerator of the average for a low pair controls all later bins. -/
theorem no_pair_to_pair (total lowSum highSum q : Nat)
    (hlow : 3 * lowSum < 2 * total)
    (hprev : 5 * q ≤ lowSum)
    (hstep : highSum ≤ lowSum + 4 * q) :
    ¬ 4 * total < 3 * highSum := by
  omega

/-- The first pair is also impossible when the first bin is at most 5/18
of all extensions. The minority-order bin at index 2 has two larger bins. -/
theorem no_firstPair_of_five_eighteenths (total first minority q high : Nat)
    (hfirst : 18 * first ≤ 5 * total)
    (hminority : 3 * minority < total)
    (hbin : 3 * q ≤ minority)
    (hhigh : high ≤ 2 * first + q) :
    ¬ 2 * total < 3 * high := by
  omega

/-- Equal downsets allow a swap when both members of the first pair precede
the pivot, contributing one half of that tail to the minority order. -/
theorem no_firstPair_of_thirteen_fortyFifths
    (total first minority q high front middle tail minorityTail : Nat)
    (hfirst : 45 * first ≤ 13 * total)
    (hminority : 3 * minority < total)
    (hbin : 3 * q + minorityTail ≤ minority)
    (hhalf : 2 * minorityTail = tail)
    (hpartition : front + middle + tail = total)
    (hfront : front ≤ 2 * first)
    (hmiddle : middle ≤ first)
    (hhigh : high ≤ front + q) :
    ¬ 2 * total < 3 * high := by
  omega

end WidthThree.LayerArithmetic
#print axioms WidthThree.LayerArithmetic.sameSide_of_smallGap
#print axioms WidthThree.LayerArithmetic.no_lateSingleton_to_pair
#print axioms WidthThree.LayerArithmetic.no_pair_to_pair
#print axioms WidthThree.LayerArithmetic.no_firstPair_of_five_eighteenths
#print axioms WidthThree.LayerArithmetic.no_firstPair_of_thirteen_fortyFifths
