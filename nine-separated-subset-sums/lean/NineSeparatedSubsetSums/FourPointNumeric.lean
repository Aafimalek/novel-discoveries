import Lean.Elab.Tactic.Decide

namespace NineSeparatedSubsetSums.FourPointNumeric

/-- Computational part of an absolute-value indexed penalty table.
This module only imports Lean, not the geometric development. -/
def penalty (T : Array Nat) (z : Int) : Int :=
  Int.ofNat (T[z.natAbs]?.getD 0)

/-- The charge on one four-point cluster, before the full geometric proof. -/
def charge (a : Int) (T : Array Nat) (c : Int) : Int :=
  let f (z : Int) : Int := z ^ 2 + penalty T z
  f (c-a-148) + f (c-a+148) + f (c+a-148) + f (c+a+148)

def budget (T : Array Nat) : Int :=
  2*Int.ofNat T.toList.sum - penalty T 0

end NineSeparatedSubsetSums.FourPointNumeric

namespace NineSeparatedSubsetSums.FourPointNumeric

/-- A penalty table encoded by fixed-width natural-number digits.
Kernel normalization uses integer shift/remainder instead of rebuilding an array. -/
def packedDigit (width packed idx : Nat) : Nat :=
  (packed >>> (width*idx)) % 2^width

def packedPenalty (width packed : Nat) (z : Int) : Int :=
  Int.ofNat (packedDigit width packed z.natAbs)

def packedCharge (a : Int) (width packed : Nat) (c : Int) : Int :=
  let f (z : Int) : Int := z ^ 2 + packedPenalty width packed z
  f (c-a-148) + f (c-a+148) + f (c+a-148) + f (c+a+148)

def packedBudget (width packed size : Nat) : Int :=
  2*Int.ofNat (((List.range size).map (packedDigit width packed)).sum) -
    packedPenalty width packed 0

end NineSeparatedSubsetSums.FourPointNumeric
