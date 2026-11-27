import NineSeparatedSubsetSums.CachedCenteredSearch

namespace NineSeparatedSubsetSums

/-- Second-largest `a` under any independently sound square-sum threshold. -/
def cachedSecondShard (a B : Nat) : Bool :=
  searchCachedCentered 511 B 5 (a-1) (computeCenteredMask [148,a])
    (148+a) (148^2+a^2)

/-- Third-largest range, with the same capacity bound as the full shard. -/
def cachedThirdLower (a B : Nat) : Nat :=
  capacityWindow 7 (a-1) (148+a) (148^2+a^2) 511 B

def cachedThirdCount (a B : Nat) : Nat :=
  a-1+1-cachedThirdLower a B

def cachedThirdShard (a B t : Nat) : Bool :=
  let d := computeCenteredMask [148,a]
  let b := cachedThirdLower a B+t
  if d.testBit (148+a+b) then false else
    searchCachedCentered 511 B 4 (b-1) (addCenteredDiffMask d b)
      (148+a+b) (148^2+a^2+b^2)

theorem cachedSecondFalse_of_thirds (a B : Nat)
    (checks : ∀ t, t < cachedThirdCount a B → cachedThirdShard a B t = false) :
    cachedSecondShard a B = false := by
  cases e : cachedSecondShard a B with
  | false => rfl
  | true =>
    unfold cachedSecondShard at e
    rw [show (5 : Nat) = 4+1 by rfl, searchCachedCentered] at e
    split at e
    · obtain ⟨t, ht, good⟩ := List.any_eq_true.mp e
      have tt : t < cachedThirdCount a B := List.mem_range.mp ht
      change cachedThirdShard a B t = true at good
      rw [checks t tt] at good
      exact Bool.noConfusion good
    · contradiction

def NoDescendingTail (a : Nat) : Prop :=
  ∀ tail : List Nat, tail.length=7 → (a::tail).Pairwise (· > ·) →
    (∀ x ∈ tail, 0 < x) → (natSubsetSums (148::a::tail)).Nodup →
    511 ≤ (148::a::tail).sum → False

/-- Any compatible geometric moment bound may be supplied to the same
checker. Checked search alone is not treated as a moment proof. -/
theorem noDescendingTail_of_cached (a B : Nat)
    (moment : ∀ tail : List Nat, tail.length=7 →
      (natSubsetSums (148::a::tail)).Nodup → B ≤ ((148::a::tail).map (· ^ 2)).sum)
    (check : cachedSecondShard a B = false) : NoDescendingTail a := by
  intro tail len desc pos distinct total
  have hm := moment tail len distinct
  have hi : ∀ x ∈ tail, x ≤ a - 1 := by
    intro x hx
    have h := (List.pairwise_cons.mp desc).1 x hx
    omega
  have ht := searchCachedCentered_true_of_completion 511 B 5 tail [148,a] (a-1)
    (by simpa using len) (by simp; omega) pos hi (List.pairwise_cons.mp desc).2 distinct
    (by simpa only [List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc] using total)
    (by simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, Nat.add_assoc] using hm)
  change cachedSecondShard a B = true at ht
  rw [check] at ht
  exact Bool.noConfusion ht

#print axioms cachedSecondFalse_of_thirds
#print axioms noDescendingTail_of_cached

end NineSeparatedSubsetSums
