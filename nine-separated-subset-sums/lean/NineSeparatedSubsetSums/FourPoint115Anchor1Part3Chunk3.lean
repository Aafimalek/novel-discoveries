import NineSeparatedSubsetSums.FourPoint115Tables
namespace NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 50000000 in

theorem fourPoint115Anchor1Part3Chunk3 :
    ∀ j : Fin 27, ((j.val : Int)+447+115)%2=1 →
      1036084 ≤ FourPointNumeric.charge 115 fourPoint115Table1
        ((j.val : Int)+447) := by decide +kernel
#print axioms fourPoint115Anchor1Part3Chunk3

end NineSeparatedSubsetSums
