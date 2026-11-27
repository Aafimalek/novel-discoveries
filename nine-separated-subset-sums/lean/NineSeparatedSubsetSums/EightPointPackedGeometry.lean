import NineSeparatedSubsetSums.EightPointNumeric
import NineSeparatedSubsetSums.EightPointPacking
import NineSeparatedSubsetSums.FourPointPackedGeometry

open scoped BigOperators

namespace NineSeparatedSubsetSums
open FourPointNumeric

/-- A checked compressed numerical table supplies an eight-point
certificate for real positional integer subset-sum geometry. -/
def eightPointCertificateOfPacked (a b p target lambda : Int) (width P size radius : Nat)
    (hp : P < 2^(width*size))
    (outer : lambda ≤ 8*((radius : Int)^2+148^2+a^2+b^2))
    (anchor : ∀ j : Fin radius, ((j.val : Int)+a+b)%2=p →
        lambda ≤ octPackedCharge a b width P (j.val : Int))
    (strong : 512*(target-1) < 64*lambda - packedBudget width P size) :
    EightPointCertificate a b p target := by
  refine ⟨lambda,packedPenalty width P,Finset.Icc (-(size : Int)) size,
    fun _ => Int.natCast_nonneg _,packedPenalty_support width P size hp,?_,?_⟩
  · intro c h
    exact octCharge_check_from_positive_window a b lambda p (packedPenalty width P)
      (fun _ => Int.natCast_nonneg _) (packedPenalty_neg width P) radius outer anchor c h
  · rwa [packedPenalty_budget width P size hp]

#print axioms eightPointCertificateOfPacked
end NineSeparatedSubsetSums
