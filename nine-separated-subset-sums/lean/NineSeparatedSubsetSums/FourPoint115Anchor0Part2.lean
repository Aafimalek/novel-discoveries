import NineSeparatedSubsetSums.FourPoint115Tables
namespace NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 50000000 in

theorem fourPoint115Anchor0Part2 :
    ∀ j : Fin 119, ((j.val : Int)+238+115)%2=0 →
      1036088 ≤ FourPointNumeric.charge 115 fourPoint115Table0
        ((j.val : Int)+238) := by decide +kernel
#print axioms fourPoint115Anchor0Part2

end NineSeparatedSubsetSums
