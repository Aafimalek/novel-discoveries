import NineSeparatedSubsetSums.IntegerSearchWindowedCap

namespace NineSeparatedSubsetSums

/-- With k extra indices beyond the final two, test the descending tail
using only a cached signed-difference mask and the two prefix moments.
No list or subset-sum bitset is rebuilt at the terminal node. -/
def searchCachedCentered (minSum minSq : Nat) :
    Nat → Nat → Nat → Nat → Nat → Bool
  | 0, hi, d, s, q =>
    let lo := capacityWindow 2 hi s q minSum minSq
    (List.range (hi+1-lo)).any (fun j => finalTwoAt d s q minSum minSq (lo+j))
  | k+1, hi, d, s, q =>
    if minSum ≤ s + topSum (k+3) hi ∧ minSq ≤ q + topSquare (k+3) hi then
      let lo := capacityWindow (k+3) hi s q minSum minSq
      (List.range (hi+1-lo)).any (fun j =>
        let a := lo+j
        if d.testBit (s+a) then false
        else searchCachedCentered minSum minSq k (a-1)
          (addCenteredDiffMask d a) (s+a) (q+a^2))
    else false

theorem computeCenteredMask_snoc (hist : List Nat) (a : Nat) :
    computeCenteredMask (hist ++ [a]) = addCenteredDiffMask (computeCenteredMask hist) a := by
  simp [computeCenteredMask, List.foldl_append]

private theorem prefix_subsets_nodup (p q : List ℕ) (h : (natSubsetSums (p ++ q)).Nodup) :
    (natSubsetSums p).Nodup := by
  induction q using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton q a ih =>
    rw [← List.append_assoc, natSubsetSums_snoc] at h
    exact ih h.of_append_left

private theorem centered_new_bit_false (p : List Nat) (a : Nat)
    (nd : (natSubsetSums (p ++ [a])).Nodup) :
    (computeCenteredMask p).testBit (p.sum+a) = false := by
  cases hx : (computeCenteredMask p).testBit (p.sum+a) with
  | false => rfl
  | true =>
    have rep := computeCenteredMask_correct p
    obtain ⟨x,hx₀,y,hy,he⟩ := (rep (p.sum+a)).mp hx
    have e : y+a = x := by omega
    rw [natSubsetSums_snoc] at nd
    have hy' : x ∈ (natSubsetSums p).map (· + a) := List.mem_map.mpr ⟨y,hy,e⟩
    have dis := (List.nodup_append.mp nd).2.2
    exfalso
    exact dis x hx₀ x hy' rfl

/-- Any actual descending collision-free tail meeting the moment cuts
is accepted. All pruning, including the cached-mask test, is proved
sound independently of running the finite search. -/
theorem searchCachedCentered_true_of_completion (minSum minSq k : Nat)
    (suffix hist : List Nat) (hi : Nat) (len : suffix.length = k+2)
    (hR : hi ≤ hist.sum)
    (pos : ∀ a ∈ suffix, 0 < a) (bound : ∀ a ∈ suffix, a ≤ hi)
    (ds : suffix.Pairwise (· > ·))
    (distinct : (natSubsetSums (hist ++ suffix)).Nodup)
    (total : minSum ≤ hist.sum + suffix.sum)
    (moment : minSq ≤ (hist.map (· ^ 2)).sum + (suffix.map (· ^ 2)).sum) :
    searchCachedCentered minSum minSq k hi (computeCenteredMask hist) hist.sum
      (hist.map (· ^ 2)).sum = true := by
  induction k generalizing suffix hist hi with
  | zero =>
    rcases suffix with _ | ⟨a,t⟩
    · simp at len
    rcases t with _ | ⟨b,t⟩
    · simp at len
    have ht : t = [] := by simpa using len
    subst t
    change finalTwoSearch hist minSum minSq
      (capacityWindow 2 hi hist.sum (hist.map (· ^ 2)).sum minSum minSq) hi = true
    apply (finalTwoSearch_true_iff hist (prefix_subsets_nodup hist [a,b] distinct)
      minSum minSq _ hi hR).mpr
    have hba := (List.pairwise_cons.mp ds).1 b (by simp)
    have ha := bound a (by simp)
    have window : capacityWindow 2 hi hist.sum (hist.map (· ^ 2)).sum minSum minSq ≤ a :=
      capacityWindow_sound [a,b] hi a hist.sum (hist.map (· ^ 2)).sum minSum minSq ds
        (fun x hx => by rcases (show x=a ∨ x=b by simpa using hx) with rfl | rfl
                        · exact le_rfl
                        · exact hba.le)
        pos ha total moment
    exact ⟨a,b,window,ha,pos b (by simp),hba,
      by simpa [Nat.add_assoc] using total,
      by simpa [Nat.add_assoc] using moment,distinct⟩
  | succ k ih =>
    rcases suffix with _ | ⟨a,t⟩
    · simp at len
    have lt : t.length = k+2 := by simp at len; omega
    have ha := bound a (by simp)
    have next := List.pairwise_cons.mp ds
    have newDistinct : (natSubsetSums ((hist++[a])++t)).Nodup := by
      rw [List.append_assoc]; exact distinct
    have hmask := centered_new_bit_false hist a (prefix_subsets_nodup (hist++[a]) t newDistinct)
    have cap := capacity_cut_sound (a::t) hi hist.sum (hist.map (· ^ 2)).sum
      minSum minSq ds bound total moment
    have len' : (a::t).length = k+3 := by simp [lt, Nat.add_assoc]
    rw [len'] at cap
    rw [searchCachedCentered, ite_eq_left cap, List.any_eq_true]
    let lo := capacityWindow (k+3) hi hist.sum (hist.map (· ^ 2)).sum minSum minSq
    have hlo : lo ≤ a := by
      unfold lo
      rw [← len']
      exact capacityWindow_sound (a::t) hi a hist.sum (hist.map (· ^ 2)).sum minSum minSq ds
        (fun x hx => by rcases List.mem_cons.mp hx with rfl | hx
                        · exact le_rfl
                        · exact (next.1 _ hx).le)
        pos ha total moment
    refine ⟨a-lo,List.mem_range.mpr (by omega),?_⟩
    change (if (computeCenteredMask hist).testBit (hist.sum+(lo+(a-lo))) then false
      else searchCachedCentered minSum minSq k (lo+(a-lo)-1)
        (addCenteredDiffMask (computeCenteredMask hist) (lo+(a-lo)))
        (hist.sum+(lo+(a-lo))) ((hist.map (· ^ 2)).sum+(lo+(a-lo))^2)) = true
    simp only [show lo+(a-lo) = a by omega, hmask, Bool.false_eq_true, ite_false]
    have advance := ih t (hist++[a]) (a-1) lt
      (by simp [List.sum_append]; omega)
      (fun x hx => pos x (List.mem_cons_of_mem _ hx))
      (fun x hx => by have := next.1 x hx; omega)
      next.2 newDistinct
      (by simpa [List.sum_append, Nat.add_assoc] using total)
      (by simpa [List.map_append, List.sum_append, Nat.add_assoc] using moment)
    simpa [computeCenteredMask_snoc, List.sum_append, List.map_append] using advance

#print axioms searchCachedCentered_true_of_completion

end NineSeparatedSubsetSums
