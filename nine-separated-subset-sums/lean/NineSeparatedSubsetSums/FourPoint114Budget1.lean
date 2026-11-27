import NineSeparatedSubsetSums.FourPoint114Tables
import NineSeparatedSubsetSums.FourPointBudget
open scoped BigOperators
namespace NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 50000000 in

theorem fourPoint114Budget1 :
    (∑ z ∈ fourPointLookupBox fourPoint114Table1,
      fourPointLookupPenalty fourPoint114Table1 z) = 75664128 := by rw [fourPointLookupBudget_eq]; decide +kernel
#print axioms fourPoint114Budget1

end NineSeparatedSubsetSums
