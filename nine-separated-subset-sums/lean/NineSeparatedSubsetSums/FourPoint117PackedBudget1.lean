import NineSeparatedSubsetSums.FourPoint117PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem packedWeight117_1_budget :
    FourPointNumeric.packedBudget 20 packedWeight117_1 566 = 80371040 := by decide +kernel

#print axioms packedWeight117_1_budget

end NineSeparatedSubsetSums
