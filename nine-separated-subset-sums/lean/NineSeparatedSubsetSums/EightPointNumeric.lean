import NineSeparatedSubsetSums.FourPointNumeric

namespace NineSeparatedSubsetSums.FourPointNumeric

def octPackedCharge (a b : Int) (width P : Nat) (c : Int) : Int :=
  packedCharge a width P (c-b)+packedCharge a width P (c+b)

end NineSeparatedSubsetSums.FourPointNumeric
