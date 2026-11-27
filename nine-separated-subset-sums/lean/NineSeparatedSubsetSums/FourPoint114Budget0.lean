import NineSeparatedSubsetSums.FourPoint114Tables
import NineSeparatedSubsetSums.FourPointBudget
open scoped BigOperators
namespace NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 50000000 in

theorem fourPoint114Budget0 :
    (∑ z ∈ fourPointLookupBox fourPoint114Table0,
      fourPointLookupPenalty fourPoint114Table0 z) = 75681536 := by rw [fourPointLookupBudget_eq]; decide +kernel
#print axioms fourPoint114Budget0

end NineSeparatedSubsetSums
