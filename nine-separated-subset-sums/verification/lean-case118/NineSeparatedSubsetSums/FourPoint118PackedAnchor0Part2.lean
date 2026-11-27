import NineSeparatedSubsetSums.FourPoint118PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem fourPoint118PackedAnchor0Part2 :
    ∀ j : Fin 2, 1077792 ≤ FourPointNumeric.packedCharge 118 20 packedWeight118_0
      (2*((j.val : Int)+240)+0) := by decide +kernel

end NineSeparatedSubsetSums
