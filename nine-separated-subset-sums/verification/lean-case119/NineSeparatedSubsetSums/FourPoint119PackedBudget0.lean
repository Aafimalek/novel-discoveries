import NineSeparatedSubsetSums.FourPoint119PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem packedWeight119_0_budget :
    FourPointNumeric.packedBudget 20 packedWeight119_0 461 = 83948416 := by decide +kernel

#print axioms packedWeight119_0_budget

end NineSeparatedSubsetSums
