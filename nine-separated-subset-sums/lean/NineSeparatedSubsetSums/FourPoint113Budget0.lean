import NineSeparatedSubsetSums.FourPoint113Tables
import NineSeparatedSubsetSums.FourPointBudget
open scoped BigOperators
namespace NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 50000000 in

theorem fourPoint113Budget0 :
    (∑ z ∈ fourPointLookupBox fourPoint113Table0,
      fourPointLookupPenalty fourPoint113Table0 z) = 74228608 := by rw [fourPointLookupBudget_eq]; decide +kernel
#print axioms fourPoint113Budget0

end NineSeparatedSubsetSums
