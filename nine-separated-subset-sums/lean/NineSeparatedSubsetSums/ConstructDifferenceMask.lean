import NineSeparatedSubsetSums.DifferenceMask

namespace NineSeparatedSubsetSums

private theorem sum_le_sum_of_natSublist {s t : List ℕ} (h : List.Sublist s t) :
    s.sum ≤ t.sum := by
  induction h with
  | slnil => simp
  | cons x h ih => simp only [List.sum_cons]; omega
  | cons_cons x h ih => simp only [List.sum_cons]; omega

theorem natSubsetSums_le_sum {weights : List ℕ} {x : ℕ} (hx : x ∈ natSubsetSums weights) :
    x ≤ weights.sum := by
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx
  exact sum_le_sum_of_natSublist (List.mem_sublists.mp hs)

def computeCenteredMask (weights : List ℕ) : ℕ :=
  weights.foldl addCenteredDiffMask 1

/-- Computing the ternary translations from scratch represents the exact
centered signed differences of the already chosen weights. -/
theorem computeCenteredMask_correct (weights : List ℕ) :
    centeredDiffRep (natSubsetSums weights) weights.sum (computeCenteredMask weights) := by
  refine List.reverseRecOn weights ?_ (fun ws a ih => ?_)
  · intro k
    change (1 : ℕ).testBit k = true ↔ ∃ x ∈ ([0] : List ℕ), ∃ y ∈ ([0] : List ℕ), k+y = 0+x
    simp [Nat.testBit_one_eq_true_iff_self_eq_zero]
  · rw [natSubsetSums_snoc, List.sum_append]
    simp only [computeCenteredMask, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.sum_cons, List.sum_nil, add_zero]
    exact addCenteredDiffMask_rep ih (fun _ => natSubsetSums_le_sum) a

/-- Ready-to-use interval pruning on the ordinary positional subset-sum list.
The weights are a feasible chosen prefix; all rejected tails would collide. -/
theorem subset_tail_interval_excluded_iff (weights : List ℕ)
    (old : (natSubsetSums weights).Nodup)
    (a lo len : ℕ) (leR : a ≤ weights.sum) :
    (∀ b, lo ≤ b → b < lo+len →
      ¬ (natSubsetSums (weights ++ [a,b])).Nodup) ↔
    (let D := computeCenteredMask weights
     let R := weights.sum
     D.testBit (R+a) = true ∨
       (intervalMask lo len &&& forbiddenTailMask D R a) = intervalMask lo len) := by
  have es (b : ℕ) : natSubsetSums (weights ++ [a,b]) =
      (natSubsetSums weights ++ (natSubsetSums weights).map (· + a)) ++
      (natSubsetSums weights ++ (natSubsetSums weights).map (· + a)).map (· + b) := by
    rw [show weights ++ [a,b] = (weights ++ [a]) ++ [b] by simp [List.append_assoc]]
    rw [natSubsetSums_snoc, natSubsetSums_snoc]
  simp_rw [es]
  exact two_weight_interval_excluded_iff (computeCenteredMask_correct weights)
    (fun _ => natSubsetSums_le_sum) old a lo len leR

example : computeCenteredMask [1,2,4] = 32767 := by decide

#print axioms natSubsetSums_le_sum
#print axioms computeCenteredMask_correct
#print axioms subset_tail_interval_excluded_iff

end NineSeparatedSubsetSums
