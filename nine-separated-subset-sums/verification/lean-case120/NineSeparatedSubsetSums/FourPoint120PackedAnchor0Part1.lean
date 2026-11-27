import NineSeparatedSubsetSums.FourPoint120PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem fourPoint120PackedAnchor0Part1 :
    ∀ j : Fin 115, 1022592 ≤ FourPointNumeric.packedCharge 120 20 packedWeight120_0
      (2*((j.val : Int)+120)+0) := by decide +kernel

end NineSeparatedSubsetSums
