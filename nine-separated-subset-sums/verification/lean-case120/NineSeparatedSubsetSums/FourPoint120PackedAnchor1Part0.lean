import NineSeparatedSubsetSums.FourPoint120PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem fourPoint120PackedAnchor1Part0 :
    ∀ j : Fin 120, 1022564 ≤ FourPointNumeric.packedCharge 120 20 packedWeight120_1
      (2*((j.val : Int)+0)+1) := by decide +kernel

end NineSeparatedSubsetSums
