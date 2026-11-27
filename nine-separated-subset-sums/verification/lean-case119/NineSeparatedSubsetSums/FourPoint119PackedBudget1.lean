import NineSeparatedSubsetSums.FourPoint119PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem packedWeight119_1_budget :
    FourPointNumeric.packedBudget 20 packedWeight119_1 466 = 83946368 := by decide +kernel

#print axioms packedWeight119_1_budget

end NineSeparatedSubsetSums
