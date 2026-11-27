import NineSeparatedSubsetSums.IntegerMomentBridge
import NineSeparatedSubsetSums.LowShelf
import Mathlib.Data.List.Nodup

namespace NineSeparatedSubsetSums

/-- All sorted nine-weight integer sets with maximum 148 and second
weight at most 94 fail distinctness of subset sums. -/
theorem noDistinctSublistsMax148SecondLe94
    (a b c d e f g h : ℤ)
    (apos : 0 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hde : d < e) (hef : e < f) (hfg : f < g) (hgh : g < h) (hhi : h ≤ 94) :
    ¬ ([a,b,c,d,e,f,g,h,148].sublists.map List.sum).Nodup := by
  intro distinct
  have moment0 := integerMomentBoundOfDistinctSublists [a,b,c,d,e,f,g,h,148] rfl distinct
  have moment : 87381 ≤ a^2 + b^2 + c^2 + d^2 + e^2 + f^2 + g^2 + h^2 + 148^2 := by
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]
      using moment0
  have same := lowShelfMustCollide a b c d e f g h apos hab hbc hcd hde hef hfg hgh hhi moment
  have m₁ : [a,d] ∈ [a,b,c,d,e,f,g,h,148].sublists := by
    apply List.mem_sublists.mpr
    exact List.Sublist.cons_cons a (List.Sublist.cons b (List.Sublist.cons c
      (List.Sublist.cons_cons d (List.nil_sublist _))))
  have m₂ : [b,c] ∈ [a,b,c,d,e,f,g,h,148].sublists := by
    apply List.mem_sublists.mpr
    exact List.Sublist.cons a (List.Sublist.cons_cons b (List.Sublist.cons_cons c
      (List.nil_sublist _)))
  have eq : [a,d] = [b,c] := by
    apply List.inj_on_of_nodup_map distinct m₁ m₂
    simpa only [List.sum_cons, List.sum_nil, add_zero] using same
  have hab' : a = b := by simpa using congrArg List.head? eq
  omega

#print axioms noDistinctSublistsMax148SecondLe94

end NineSeparatedSubsetSums
