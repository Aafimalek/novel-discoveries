import NineSeparatedSubsetSums.FourPoint117PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem fourPoint117PackedAnchor0Part1 :
    ∀ j : Fin 120, 1064600 ≤ FourPointNumeric.packedCharge 117 20 packedWeight117_0
      (2*((j.val : Int)+120)+1) := by decide +kernel

end NineSeparatedSubsetSums
