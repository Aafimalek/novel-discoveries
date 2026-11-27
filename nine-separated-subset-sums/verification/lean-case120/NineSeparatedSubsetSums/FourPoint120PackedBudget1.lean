import NineSeparatedSubsetSums.FourPoint120PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem packedWeight120_1_budget :
    FourPointNumeric.packedBudget 20 packedWeight120_1 576 = 75337728 := by decide +kernel

#print axioms packedWeight120_1_budget

end NineSeparatedSubsetSums
