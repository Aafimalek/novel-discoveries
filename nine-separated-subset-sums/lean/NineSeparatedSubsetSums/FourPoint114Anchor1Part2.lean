import NineSeparatedSubsetSums.FourPoint114Tables
open scoped BigOperators
namespace NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 50000000 in

theorem fourPoint114Anchor1Part2 :
    ∀ j : Fin 118, ((j.val : ℤ)+236+114)%2=1 →
      1027988 ≤ blockCharge 114 (fun z => z^2+fourPointLookupPenalty fourPoint114Table1 z)
        ((j.val : ℤ)+236) := by decide +kernel
#print axioms fourPoint114Anchor1Part2

end NineSeparatedSubsetSums
