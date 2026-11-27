import NineSeparatedSubsetSums.FourPoint115Tables
namespace NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 50000000 in

theorem fourPoint115Anchor0Part3 :
    ∀ j : Fin 117, ((j.val : Int)+357+115)%2=0 →
      1036088 ≤ FourPointNumeric.charge 115 fourPoint115Table0
        ((j.val : Int)+357) := by decide +kernel
#print axioms fourPoint115Anchor0Part3

end NineSeparatedSubsetSums
