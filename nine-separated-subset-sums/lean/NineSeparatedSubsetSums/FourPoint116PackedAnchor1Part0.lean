import NineSeparatedSubsetSums.FourPoint116PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem fourPoint116PackedAnchor1Part0 :
    ∀ j : Fin 120, 1043012 ≤ FourPointNumeric.packedCharge 116 20 packedWeight116_1
      (2*((j.val : Int)+0)+1) := by decide +kernel

end NineSeparatedSubsetSums
