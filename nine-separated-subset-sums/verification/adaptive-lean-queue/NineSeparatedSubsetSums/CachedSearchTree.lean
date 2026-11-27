import NineSeparatedSubsetSums.CachedFourPointShards

namespace NineSeparatedSubsetSums

/-- A state has `depth + 2` weights still to select. -/
structure CachedSearchNode where
  depth : Nat
  top : Nat
  differences : Nat
  total : Nat
  squares : Nat

/-- The one Boolean associated with a node. -/
def runCachedNode (S Q : Nat) (v : CachedSearchNode) : Bool :=
  searchCachedCentered S Q v.depth v.top v.differences v.total v.squares

/-- Use an explicit branch state rather than an opaque calculation inside
the recursion, so arbitrarily large computations can be split at any depth. -/
def cachedChild (v : CachedSearchNode) (a : Nat) : CachedSearchNode :=
  ⟨v.depth-1, a-1, addCenteredDiffMask v.differences a,
    v.total+a, v.squares+a^2⟩

/-- The exact immediate child values on a node with depth at least one. -/
def cachedChildChoices (S Q : Nat) (v : CachedSearchNode) : List Nat :=
  if 0 < v.depth ∧ S ≤ v.total + topSum (v.depth+2) v.top ∧
      Q ≤ v.squares + topSquare (v.depth+2) v.top then
    let lo := capacityWindow (v.depth+2) v.top v.total v.squares S Q
    ((List.range (v.top+1-lo)).map (lo+·)).filter
      (fun a => !(v.differences.testBit (v.total+a)))
  else []

theorem runCachedNode_true_iff_child (S Q : Nat) (v : CachedSearchNode)
    (notLeaf : 0 < v.depth) :
    runCachedNode S Q v = true ↔
      ∃ a ∈ cachedChildChoices S Q v, runCachedNode S Q (cachedChild v a) = true := by
  rcases v with ⟨n,hi,d,t,q⟩
  cases n with
  | zero => simp at notLeaf
  | succ k =>
    simp only [runCachedNode, cachedChildChoices, cachedChild]
    have hn : 0 < k + 1 := by omega
    simp only [hn,true_and, Nat.succ_sub_one, Nat.succ_eq_add_one,
      Nat.add_assoc, show 1 + 2 = 3 by decide]
    by_cases hc : S ≤ t + topSum (k+3) hi ∧ Q ≤ q + topSquare (k+3) hi
    · rw [searchCachedCentered, ite_eq_left hc, ite_eq_left hc, List.any_eq_true]
      constructor
      · rintro ⟨j,hj,hs⟩
        generalize he : capacityWindow (k+3) hi t q S Q + j = a at hs
        cases hb : d.testBit (t+a)
        · refine ⟨a,List.mem_filter.mpr ⟨List.mem_map.mpr ⟨j,hj,he⟩,by simp [hb]⟩,?_⟩
          simpa [hb] using hs
        · simp [hb] at hs
      · rintro ⟨a,ha,hrun⟩
        obtain ⟨hm,hb⟩ := List.mem_filter.mp ha
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
        refine ⟨j,hj,?_⟩
        have hbit : d.testBit (t + (capacityWindow (k+3) hi t q S Q+j)) = false := by
          simpa using hb
        simpa only [hbit, Bool.false_eq_true, ite_false] using hrun
    · rw [searchCachedCentered, ite_eq_right hc, ite_eq_right hc]
      simp

/-- A branch can be discharged without computing its descendants in the
same Lean module. This theorem applies at every nonterminal depth. -/
theorem runCachedNode_false_of_children (S Q : Nat) (v : CachedSearchNode)
    (notLeaf : 0 < v.depth)
    (leaves : ∀ a ∈ cachedChildChoices S Q v, runCachedNode S Q (cachedChild v a) = false) :
    runCachedNode S Q v = false := by
  cases e : runCachedNode S Q v with
  | false => rfl
  | true =>
    obtain ⟨a,hm,ht⟩ := (runCachedNode_true_iff_child S Q v notLeaf).mp e
    rw [leaves a hm] at ht
    exact Bool.noConfusion ht

#print axioms runCachedNode_false_of_children

end NineSeparatedSubsetSums
