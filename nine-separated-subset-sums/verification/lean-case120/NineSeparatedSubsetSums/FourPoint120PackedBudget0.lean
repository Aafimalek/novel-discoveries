import NineSeparatedSubsetSums.FourPoint120PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem packedWeight120_0_budget :
    FourPointNumeric.packedBudget 20 packedWeight120_0 469 = 75340800 := by decide +kernel

#print axioms packedWeight120_0_budget

end NineSeparatedSubsetSums
