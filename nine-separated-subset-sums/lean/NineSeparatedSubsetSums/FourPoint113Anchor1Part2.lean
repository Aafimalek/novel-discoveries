import NineSeparatedSubsetSums.FourPoint113Tables
open scoped BigOperators
namespace NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 50000000 in

theorem fourPoint113Anchor1Part2 :
    ∀ j : Fin 117, ((j.val : ℤ)+234+113)%2=1 →
      1016308 ≤ blockCharge 113 (fun z => z^2+fourPointLookupPenalty fourPoint113Table1 z)
        ((j.val : ℤ)+234) := by decide +kernel
#print axioms fourPoint113Anchor1Part2

end NineSeparatedSubsetSums
