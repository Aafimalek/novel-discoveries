import NineSeparatedSubsetSums.EightPoint120_118PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem packedOct120_118_1_budget :
    FourPointNumeric.packedBudget 20 packedOct120_118_1 500 = 76903876 := by decide +kernel

#print axioms packedOct120_118_1_budget

end NineSeparatedSubsetSums
