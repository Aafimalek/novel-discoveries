import NineSeparatedSubsetSums.FourPoint113Tables
import NineSeparatedSubsetSums.FourPointBudget
open scoped BigOperators
namespace NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 50000000 in

theorem fourPoint113Budget1 :
    (∑ z ∈ fourPointLookupBox fourPoint113Table1,
      fourPointLookupPenalty fourPoint113Table1 z) = 74208128 := by rw [fourPointLookupBudget_eq]; decide +kernel
#print axioms fourPoint113Budget1

end NineSeparatedSubsetSums
