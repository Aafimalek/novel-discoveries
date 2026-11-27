import NineSeparatedSubsetSums.FourPoint119PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem fourPoint119PackedAnchor1Part2 :
    ∀ j : Fin 4, 1090948 ≤ FourPointNumeric.packedCharge 119 20 packedWeight119_1
      (2*((j.val : Int)+240)+0) := by decide +kernel

end NineSeparatedSubsetSums
