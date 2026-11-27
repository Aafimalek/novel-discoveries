import NineSeparatedSubsetSums.FourPoint117PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem packedWeight117_0_budget :
    FourPointNumeric.packedBudget 20 packedWeight117_0 571 = 80369408 := by decide +kernel

#print axioms packedWeight117_0_budget

end NineSeparatedSubsetSums
