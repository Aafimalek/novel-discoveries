import NineSeparatedSubsetSums.FourPointBudget
import NineSeparatedSubsetSums.FourPointNumeric

open scoped BigOperators

namespace NineSeparatedSubsetSums
open FourPointNumeric

/-- The compressed table has zero penalty beyond its stored digit range. -/
theorem packedPenalty_support (width P size : Nat) (hp : P < 2^(width*size))
    (z : Int) (outside : z ∉ Finset.Icc (-(size : Int)) size) :
    packedPenalty width P z = 0 := by
  have hsize : size ≤ z.natAbs := by
    by_contra! h
    apply outside
    exact Finset.mem_Icc.mpr (by omega)
  have he : width*size ≤ width*z.natAbs := Nat.mul_le_mul_left width hsize
  have ht : P < 2^(width*z.natAbs) :=
    hp.trans_le (Nat.pow_le_pow_of_le (by decide) he)
  simp [packedPenalty, packedDigit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt ht]

theorem packedPenalty_neg (width P : Nat) (z : Int) :
    packedPenalty width P (-z) = packedPenalty width P z := by
  simp [packedPenalty]

private theorem finRangeSum_cast (N : Nat) (f : Nat → Nat) :
    (∑ i ∈ Finset.range N, (f i : Int)) =
      Int.ofNat (((List.range N).map f).sum) := by
  induction N with
  | zero => simp
  | succ N h =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append,
      h]
    simp

/-- The symmetric finite budget is exactly one packed-digit sum. -/
theorem packedPenalty_budget (width P size : Nat) (hp : P < 2^(width*size)) :
    (∑ z ∈ Finset.Icc (-(size : Int)) size, packedPenalty width P z) =
      packedBudget width P size := by
  rw [Finset.sum_Icc_of_even_eq_range (packedPenalty_neg width P) size,
    Finset.sum_range_succ]
  have tail : packedPenalty width P size = 0 := by
    simp [packedPenalty, packedDigit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hp]
  rw [tail, add_zero]
  have mid : (∑ z ∈ Finset.range size, packedPenalty width P (z : Int)) =
        Int.ofNat (((List.range size).map (packedDigit width P)).sum) := by
    simpa [packedPenalty] using finRangeSum_cast size (packedDigit width P)
  rw [mid, nsmul_eq_mul]
  rfl

/-- A compact numeric certificate is bridged to the general geometric one. -/
def fourPointCertificateOfPacked (a p target lambda : Int) (width P size radius : Nat)
    (hp : P < 2^(width*size))
    (cap : lambda ≤ 4*(801^2+148^2+a^2))
    (outer : lambda ≤ 4*((radius : Int)^2+148^2+a^2))
    (anchor : ∀ j : Fin radius, ((j.val : Int)+a)%2=p →
        lambda ≤ packedCharge a width P (j.val : Int))
    (strong : 512*(target-1) < 128*lambda - packedBudget width P size) :
    FourPointCertificate a p target := by
  refine ⟨lambda,packedPenalty width P,Finset.Icc (-(size : Int)) size,
    fun _ => Int.natCast_nonneg _,packedPenalty_support width P size hp,cap,?_,?_⟩
  · intro j hj
    exact blockCharge_check_from_positive_window a lambda p (packedPenalty width P)
      (fun _ => Int.natCast_nonneg _) (packedPenalty_neg width P) radius outer anchor
      ((j.val : Int)-800) hj
  · rwa [packedPenalty_budget width P size hp]

#print axioms fourPointCertificateOfPacked
end NineSeparatedSubsetSums
