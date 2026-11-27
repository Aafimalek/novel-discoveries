import NineSeparatedSubsetSums.FourPoint119PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem fourPoint119PackedAnchor0Part2 :
    ∀ j : Fin 3, 1090968 ≤ FourPointNumeric.packedCharge 119 20 packedWeight119_0
      (2*((j.val : Int)+240)+1) := by decide +kernel

end NineSeparatedSubsetSums
