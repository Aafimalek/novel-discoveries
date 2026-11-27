import NineSeparatedSubsetSums.EightPoint120_118PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem packedOct120_118_0_budget :
    FourPointNumeric.packedBudget 20 packedOct120_118_0 407 = 76978618 := by decide +kernel

#print axioms packedOct120_118_0_budget

end NineSeparatedSubsetSums
