import NineSeparatedSubsetSums.ConstructDifferenceMask
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Push

namespace NineSeparatedSubsetSums

/-- The smallest natural number whose square reaches n. -/
def ceilSquareRootNat (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.sqrt (n-1) + 1

theorem ceilSquareRootNat_le (n b : ℕ) :
    ceilSquareRootNat n ≤ b ↔ n ≤ b^2 := by
  by_cases h : n = 0
  · simp [ceilSquareRootNat, h]
  · simp only [ceilSquareRootNat, if_neg h]
    rw [Nat.succ_le_iff, Nat.sqrt_lt']
    omega

/-- After fixing the penultimate weight a, all arithmetic constraints
on the last positive weight become one inclusive lower bound. -/
def finalTwoLower (minSum minSq R Q a : ℕ) : ℕ :=
  max 1 (max (minSum - (R+a)) (ceilSquareRootNat (minSq - (Q+a^2))))

theorem finalTwoLower_le (minSum minSq R Q a b : ℕ) :
    finalTwoLower minSum minSq R Q a ≤ b ↔
      0 < b ∧ minSum ≤ R+a+b ∧ minSq ≤ Q+a^2+b^2 := by
  simp only [finalTwoLower, max_le_iff, ceilSquareRootNat_le]
  omega

/-- Given a fixed penultimate weight a, a single interval mask tests
all eligible last weights b with b<a. An empty interval is rejected. -/
def finalTwoAt (D R Q minSum minSq a : ℕ) : Bool :=
  let lo := finalTwoLower minSum minSq R Q a
  let m := intervalMask lo (a-lo)
  decide (¬ (D.testBit (R+a) = true ∨ (m &&& forbiddenTailMask D R a) = m))

/-- A fixed first choice passes the mask test iff at least one last
weight meets both minimum moments and avoids every subset collision. -/
theorem finalTwoAt_true_iff (weights : List ℕ)
    (old : (natSubsetSums weights).Nodup)
    (Q minSum minSq a : ℕ) (ha : a ≤ weights.sum) :
    finalTwoAt (computeCenteredMask weights) weights.sum Q minSum minSq a = true ↔
      ∃ b : ℕ, 0 < b ∧ b < a ∧ minSum ≤ weights.sum+a+b ∧
        minSq ≤ Q+a^2+b^2 ∧ (natSubsetSums (weights ++ [a,b])).Nodup := by
  classical
  let lo := finalTwoLower minSum minSq weights.sum Q a
  let D := computeCenteredMask weights
  let R := weights.sum
  have opp := subset_tail_interval_excluded_iff weights old a lo (a-lo) ha
  change (decide (¬ (D.testBit (R+a) = true ∨
    (intervalMask lo (a-lo) &&& forbiddenTailMask D R a) = intervalMask lo (a-lo))) = true) ↔ _
  rw [decide_eq_true_eq, ← opp]
  push_neg
  constructor
  · rintro ⟨b, hbLo, hbHi, hbN⟩
    obtain ⟨hpos, hsum, hsq⟩ := (finalTwoLower_le minSum minSq R Q a b).mp hbLo
    exact ⟨b, hpos, by omega, hsum, hsq, hbN⟩
  · rintro ⟨b, hpos, hbHi, hsum, hsq, hbN⟩
    have hbLo : lo ≤ b := (finalTwoLower_le minSum minSq R Q a b).mpr ⟨hpos,hsum,hsq⟩
    exact ⟨b, hbLo, by omega, hbN⟩

/-- Search a closed interval [loA,hiA] for the last two weights.
Only the first component a is enumerated; the interval for b is masked
in one step. If loA>hiA the search is empty. -/
def finalTwoSearch (weights : List ℕ) (minSum minSq loA hiA : ℕ) : Bool :=
  let D := computeCenteredMask weights
  let R := weights.sum
  let Q := (weights.map (· ^ 2)).sum
  (List.range (hiA+1-loA)).any (fun j => finalTwoAt D R Q minSum minSq (loA+j))

theorem finalTwoSearch_true_iff (weights : List ℕ)
    (old : (natSubsetSums weights).Nodup)
    (minSum minSq loA hiA : ℕ) (hiR : hiA ≤ weights.sum) :
    finalTwoSearch weights minSum minSq loA hiA = true ↔
      ∃ a b : ℕ, loA ≤ a ∧ a ≤ hiA ∧ 0 < b ∧ b < a ∧
        minSum ≤ weights.sum+a+b ∧ minSq ≤ (weights.map (· ^ 2)).sum+a^2+b^2 ∧
        (natSubsetSums (weights ++ [a,b])).Nodup := by
  rw [finalTwoSearch, List.any_eq_true]
  constructor
  · rintro ⟨j, hj, ht⟩
    have hj' := List.mem_range.mp hj
    have haR : loA+j ≤ weights.sum := by omega
    obtain ⟨b,hb₁,hb₂,hb₃,hb₄,hb₅⟩ := (finalTwoAt_true_iff weights old
      ((weights.map (· ^ 2)).sum) minSum minSq (loA+j) haR).mp ht
    exact ⟨loA+j,b,by omega,by omega,hb₁,hb₂,hb₃,hb₄,hb₅⟩
  · rintro ⟨a,b,ha₁,ha₂,hb₁,hb₂,hb₃,hb₄,hb₅⟩
    have hj : a-loA ∈ List.range (hiA+1-loA) := List.mem_range.mpr (by omega)
    refine ⟨a-loA,hj,?_⟩
    have hre : loA+(a-loA) = a := by omega
    rw [hre]
    exact (finalTwoAt_true_iff weights old ((weights.map (· ^ 2)).sum)
      minSum minSq a (by omega)).mpr ⟨b,hb₁,hb₂,hb₃,hb₄,hb₅⟩

/-- Search false excludes every pair in the chosen shard. -/
theorem no_finalTwo_of_false (weights : List ℕ)
    (old : (natSubsetSums weights).Nodup)
    (minSum minSq loA hiA : ℕ) (hiR : hiA ≤ weights.sum)
    (hfalse : finalTwoSearch weights minSum minSq loA hiA = false)
    (a b : ℕ) (ha₁ : loA ≤ a) (ha₂ : a ≤ hiA) (hb₁ : 0 < b) (hb₂ : b < a)
    (hs : minSum ≤ weights.sum+a+b) (hq : minSq ≤ (weights.map (· ^ 2)).sum+a^2+b^2) :
    ¬ (natSubsetSums (weights ++ [a,b])).Nodup := by
  intro h
  have ht := (finalTwoSearch_true_iff weights old minSum minSq loA hiA hiR).mpr
    ⟨a,b,ha₁,ha₂,hb₁,hb₂,hs,hq,h⟩
  rw [hfalse] at ht
  exact Bool.noConfusion ht

#print axioms ceilSquareRootNat_le
#print axioms finalTwoAt_true_iff
#print axioms finalTwoSearch_true_iff
#print axioms no_finalTwo_of_false

end NineSeparatedSubsetSums
