import NineSeparatedSubsetSums.EightPoint120_119PackedTables

namespace NineSeparatedSubsetSums

set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem packedOct120_119_1_budget :
    FourPointNumeric.packedBudget 20 packedOct120_119_1 490 = 77324126 := by decide +kernel

#print axioms packedOct120_119_1_budget

end NineSeparatedSubsetSums
