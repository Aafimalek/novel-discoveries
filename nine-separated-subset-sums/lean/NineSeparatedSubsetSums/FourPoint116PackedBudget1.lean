import NineSeparatedSubsetSums.FourPoint116PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem packedWeight116_1_budget :
    FourPointNumeric.packedBudget 20 packedWeight116_1 444 = 77555200 := by decide +kernel

#print axioms packedWeight116_1_budget

end NineSeparatedSubsetSums
