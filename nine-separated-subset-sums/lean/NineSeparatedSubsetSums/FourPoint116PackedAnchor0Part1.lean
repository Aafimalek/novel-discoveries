import NineSeparatedSubsetSums.FourPoint116PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem fourPoint116PackedAnchor0Part1 :
    ∀ j : Fin 118, 1043136 ≤ FourPointNumeric.packedCharge 116 20 packedWeight116_0
      (2*((j.val : Int)+120)+0) := by decide +kernel

end NineSeparatedSubsetSums
