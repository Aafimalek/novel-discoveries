import NineSeparatedSubsetSums.FourPoint118PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem packedWeight118_1_budget :
    FourPointNumeric.packedBudget 20 packedWeight118_1 544 = 82141056 := by decide +kernel

#print axioms packedWeight118_1_budget

end NineSeparatedSubsetSums
