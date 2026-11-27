import NineSeparatedSubsetSums.FourPoint114Tables
open scoped BigOperators
namespace NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 50000000 in

theorem fourPoint114Anchor0Part0 :
    ∀ j : Fin 118, ((j.val : ℤ)+0+114)%2=0 →
      1028128 ≤ blockCharge 114 (fun z => z^2+fourPointLookupPenalty fourPoint114Table0 z)
        ((j.val : ℤ)+0) := by decide +kernel
#print axioms fourPoint114Anchor0Part0

end NineSeparatedSubsetSums
