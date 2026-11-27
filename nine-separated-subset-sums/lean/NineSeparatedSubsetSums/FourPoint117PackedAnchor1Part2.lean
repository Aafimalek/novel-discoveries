import NineSeparatedSubsetSums.FourPoint117PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem fourPoint117PackedAnchor1Part2 :
    ∀ j : Fin 1, 1064612 ≤ FourPointNumeric.packedCharge 117 20 packedWeight117_1
      (2*((j.val : Int)+240)+0) := by decide +kernel

end NineSeparatedSubsetSums
