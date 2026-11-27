import NineSeparatedSubsetSums.EightPoint120_118PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem eightPoint120_118PackedAnchor1Part1 :
    ∀ j : Fin 115, 2175060 ≤ FourPointNumeric.octPackedCharge 120 118 20 packedOct120_118_1
      (2*((j.val : Int)+120)+1) := by decide +kernel

end NineSeparatedSubsetSums
