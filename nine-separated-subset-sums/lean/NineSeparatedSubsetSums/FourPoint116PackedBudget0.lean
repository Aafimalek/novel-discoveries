import NineSeparatedSubsetSums.FourPoint116PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem packedWeight116_0_budget :
    FourPointNumeric.packedBudget 20 packedWeight116_0 445 = 77570560 := by decide +kernel

#print axioms packedWeight116_0_budget

end NineSeparatedSubsetSums
