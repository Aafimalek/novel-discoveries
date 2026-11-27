import NineSeparatedSubsetSums.FourPoint115Tables
namespace NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 50000000 in

theorem fourPoint115Budget1 :
    FourPointNumeric.budget fourPoint115Table1 = 76681024 := by decide +kernel
#print axioms fourPoint115Budget1

end NineSeparatedSubsetSums
