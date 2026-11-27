import NineSeparatedSubsetSums.CachedFourPointShards

namespace NineSeparatedSubsetSums

/-- The cached search starting with three already fixed weights. -/
def cachedFixedThirdShard (a b B : Nat) : Bool :=
  searchCachedCentered 511 B 4 (b-1) (computeCenteredMask [148,a,b])
    (148+a+b) (148^2+a^2+b^2)

def NoDescendingTailAfterThird (a b : Nat) : Prop :=
  ∀ tail : List Nat, tail.length=6 → (b::tail).Pairwise (· > ·) →
    (∀ x ∈ tail, 0 < x) → (natSubsetSums (148::a::b::tail)).Nodup →
    511 ≤ (148::a::b::tail).sum → False

theorem noDescendingThirdTail_of_cached (a b B : Nat)
    (moment : ∀ tail : List Nat, tail.length=6 →
      (natSubsetSums (148::a::b::tail)).Nodup → B ≤ ((148::a::b::tail).map (· ^ 2)).sum)
    (check : cachedFixedThirdShard a b B = false) : NoDescendingTailAfterThird a b := by
  intro tail len desc pos distinct total
  have hm := moment tail len distinct
  have hi : ∀ x ∈ tail, x ≤ b - 1 := by
    intro x hx
    have h := (List.pairwise_cons.mp desc).1 x hx
    omega
  have ht := searchCachedCentered_true_of_completion 511 B 4 tail [148,a,b] (b-1)
    (by simpa using len) (by simp; omega) pos hi (List.pairwise_cons.mp desc).2 distinct
    (by simpa only [List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc] using total)
    (by simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, Nat.add_assoc] using hm)
  rw [cachedFixedThirdShard] at check
  simp only [List.sum_cons, List.sum_nil, List.map_cons, List.map_nil,
    Nat.add_zero, Nat.add_assoc] at ht check
  rw [check] at ht
  exact Bool.noConfusion ht

/-- A weaker second-weight moment bound identifies which third weights
must be considered. Each resulting third-weight branch can use a
different, stronger geometric certificate (or any other valid method). -/
theorem noDescendingTail_of_third_tails (a B : Nat)
    (moment : ∀ tail : List Nat, tail.length=7 →
      (natSubsetSums (148::a::tail)).Nodup → B ≤ ((148::a::tail).map (· ^ 2)).sum)
    (checks : ∀ b, cachedThirdLower a B ≤ b → b ≤ a-1 →
      NoDescendingTailAfterThird a b) : NoDescendingTail a := by
  intro t len desc pos distinct total
  have hm := moment t len distinct
  rcases t with _ | ⟨b,r⟩
  · simp at len
  have dp := List.pairwise_cons.mp desc
  have bHi : b ≤ a-1 := by have := dp.1 b (by simp); omega
  have cmp := List.pairwise_cons.mp dp.2
  have lim : ∀ x ∈ b::r, x ≤ b := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_rfl
    · exact (cmp.1 x hx).le
  have ct := capacityWindow_sound (b::r) (a-1) b (148+a) (148^2+a^2) 511 B
    dp.2 lim pos bHi
    (by simpa only [List.sum_cons, Nat.add_assoc] using total)
    (by simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using hm)
  rw [len] at ct
  exact checks b ct bHi r (by simp at len; omega) dp.2
    (fun x h => pos x (List.mem_cons_of_mem _ h)) distinct total

#print axioms noDescendingTail_of_third_tails
#print axioms noDescendingThirdTail_of_cached
end NineSeparatedSubsetSums
