import NineSeparatedSubsetSums.FourPoint118PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem fourPoint118PackedAnchor1Part0 :
    ∀ j : Fin 120, 1077780 ≤ FourPointNumeric.packedCharge 118 20 packedWeight118_1
      (2*((j.val : Int)+0)+1) := by decide +kernel

end NineSeparatedSubsetSums
