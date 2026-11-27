import NineSeparatedSubsetSums.CapacityWindow
import NineSeparatedSubsetSums.FinalTwoSearch
import NineSeparatedSubsetSums.IntegerShards

namespace NineSeparatedSubsetSums

/-- The verified search with a terminal interval-mask check for the
last two choices. The current prefix is retained for constructing that mask. -/
def searchWindowed (minSum minSq : ℕ) :
    ℕ → ℕ → List ℕ → ℕ → ℕ → ℕ → Bool
  | 0, hi, _, m, s, q => searchIntegerWeights minSum minSq 0 hi m s q
  | 1, hi, _, m, s, q => searchIntegerWeights minSum minSq 1 hi m s q
  | 2, hi, hist, m, s, q =>
    if hi ≤ s then finalTwoSearch hist minSum minSq 1 hi
    else searchIntegerWeights minSum minSq 2 hi m s q
  | k + 3, hi, hist, m, total, square =>
    if minSum ≤ total + topSum (k + 3) hi ∧
        minSq ≤ square + topSquare (k + 3) hi then
      let lo := capacityWindow (k + 3) hi total square minSum minSq
      (List.range (hi + 1 - lo)).any (fun t =>
        let a := lo + t
        if m &&& (m <<< a) = 0 then
          searchWindowed minSum minSq (k + 2) (a - 1) (hist ++ [a])
            (addSubsetMask m a) (total+a) (square+a^2)
        else false)
    else false

private theorem initial_sums_nodup (p q : List ℕ) (h : (natSubsetSums (p ++ q)).Nodup) :
    (natSubsetSums p).Nodup := by
  induction q using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton q a ih =>
    rw [← List.append_assoc, natSubsetSums_snoc] at h
    exact ih h.of_append_left

theorem searchWindowed_true_of_completion
    (minSum minSq : ℕ) (suffix hist : List ℕ) (hi m s q : ℕ)
    (ms : maskRep (natSubsetSums hist) m) (hs : s = hist.sum)
    (hq : q = (hist.map (· ^ 2)).sum)
    (pos : ∀ a ∈ suffix, 0 < a) (bound : ∀ a ∈ suffix, a ≤ hi)
    (ds : suffix.Pairwise (· > ·))
    (distinct : (natSubsetSums (hist ++ suffix)).Nodup)
    (total : minSum ≤ s + suffix.sum)
    (moment : minSq ≤ q + (suffix.map (· ^ 2)).sum) :
    searchWindowed minSum minSq suffix.length hi hist m s q = true := by
  induction suffix generalizing hist hi m s q with
  | nil =>
    simpa only [List.length_nil, searchWindowed] using
      search_true_of_completion minSum minSq [] hist hi m s q ms pos bound ds distinct total moment
  | cons a rest ih =>
    cases rest with
    | nil =>
      simpa only [List.length_cons, List.length_nil, searchWindowed] using
        search_true_of_completion minSum minSq [a] hist hi m s q ms pos bound ds distinct total moment
    | cons b tail =>
      cases tail with
      | nil =>
        by_cases h : hi ≤ s
        · rw [show ([a,b] : List ℕ).length = 2 by rfl, searchWindowed, if_pos h]
          apply (finalTwoSearch_true_iff hist (initial_sums_nodup hist [a,b] distinct)
            minSum minSq 1 hi (hs ▸ h)).mpr
          refine ⟨a,b,pos a (by simp),bound a (by simp),pos b (by simp),
            (List.pairwise_cons.mp ds).1 b (by simp),?_,?_,distinct⟩
          · simpa [hs,Nat.add_assoc] using total
          · simpa [hq,Nat.add_assoc] using moment
        · rw [show ([a,b] : List ℕ).length = 2 by rfl, searchWindowed, if_neg h]
          exact search_true_of_completion minSum minSq [a,b] hist hi m s q ms pos bound ds distinct total moment
      | cons c tail =>
        let rest := b :: c :: tail
        have hrest : (a :: rest).Pairwise (· > ·) := ds
        have ha := pos a (List.mem_cons_self)
        have hai := bound a (List.mem_cons_self)
        have next := List.pairwise_cons.mp hrest
        have dd : (natSubsetSums ((hist ++ [a]) ++ rest)).Nodup := by
          rw [List.append_assoc]
          exact distinct
        have test := (addSubsetMask_collision_iff hist a m ms
          (initial_sums_nodup hist (a::rest) distinct)).mpr
          (initial_sums_nodup (hist ++ [a]) rest dd)
        have cap := capacity_cut_sound (a::rest) hi s q minSum minSq hrest bound total moment
        have cap' : minSum ≤ s + topSum (tail.length + 3) hi ∧
          minSq ≤ q + topSquare (tail.length + 3) hi := cap
        rw [show (a::b::c::tail).length = tail.length + 3 by rfl,
          searchWindowed, if_pos cap', List.any_eq_true]
        let lo := capacityWindow (tail.length + 3) hi s q minSum minSq
        have hlo : lo ≤ a := capacityWindow_sound (a::rest) hi a s q minSum minSq
          hrest (fun x hx => by
            rcases List.mem_cons.mp hx with rfl | hm
            · exact le_rfl
            · exact (next.1 x hm).le)
          pos hai total moment
        refine ⟨a - lo, List.mem_range.mpr (by omega), ?_⟩
        have ha' : lo + (a - lo) = a := by omega
        change (if m &&& (m <<< (lo+(a-lo))) = 0 then
          searchWindowed minSum minSq (tail.length+2) (lo+(a-lo)-1)
            (hist ++ [lo+(a-lo)]) (addSubsetMask m (lo+(a-lo))) (s+(lo+(a-lo))) (q+(lo+(a-lo))^2)
          else false) = true
        simp only [ha', if_pos test]
        apply ih (hist ++ [a]) (a - 1) (addSubsetMask m a) (s + a) (q + a^2)
        · exact addSubsetMask_represents hist a m ms
        · rw [List.sum_append, hs]; simp
        · rw [List.map_append, List.sum_append, hq]; simp
        · exact fun x h => pos x (List.mem_cons_of_mem _ h)
        · intro x h
          have := next.1 x h
          omega
        · exact next.2
        · exact dd
        · simpa [Nat.add_assoc] using total
        · simpa [Nat.add_assoc] using moment

/-- Checked second-largest split for the optimized search. -/
def windowed_second_shard (a : ℕ) : Bool :=
  searchWindowed 511 87381 7 (a - 1) [148,a] (computeSubsetMask [148,a]).1
    (148 + a) (148 ^ 2 + a ^ 2)

theorem counterexample_hits_windowed_shard (w : Fin 9 → ℤ)
    (positive : ∀ i, 0 < w i) (bounded : ∀ i, w i ≤ 148)
    (last : w (Fin.last 8) = 148)
    (distinct : Function.Injective (fun S : Finset (Fin 9) => ∑ i ∈ S, w i)) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ 147 ∧ windowed_second_shard a = true := by
  obtain ⟨t, hlen, hd, hp, hn, ht, hm⟩ :=
    integer_max148_to_search_input w positive bounded last distinct
  cases t with
  | nil => simp at hlen
  | cons a t =>
    have ha : 1 ≤ a := hp a (by simp)
    have hb : a ≤ 147 := by
      have h := (List.pairwise_cons.mp hd).1 a (by simp)
      omega
    have inner := (List.pairwise_cons.mp hd).2
    have hsmall : ∀ x ∈ t, x ≤ a - 1 := by
      intro x h
      have hh := (List.pairwise_cons.mp inner).1 x h
      omega
    have count : t.length = 7 := by simp at hlen; omega
    have h := searchWindowed_true_of_completion 511 87381 t [148,a] (a - 1)
      (computeSubsetMask [148,a]).1 (148+a) (148^2+a^2)
      (computeSubsetMask_correct [148,a]).1 (by simp) (by simp)
      (fun x hx => hp x (by simp [hx])) hsmall (List.pairwise_cons.mp inner).2 hn
      (by simpa only [List.sum_cons, Nat.add_assoc] using ht)
      (by simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using hm)
    rw [count] at h
    exact ⟨a, ha, hb, h⟩

theorem integer_max148_excluded_of_windowed_shards
    (checks : ∀ a : ℕ, 1 ≤ a → a ≤ 147 → windowed_second_shard a = false)
    (w : Fin 9 → ℤ) (positive : ∀ i, 0 < w i) (bounded : ∀ i, w i ≤ 148)
    (last : w (Fin.last 8) = 148) :
    ¬ Function.Injective (fun S : Finset (Fin 9) => ∑ i ∈ S, w i) := by
  intro h
  obtain ⟨a, ha, hb, hc⟩ := counterexample_hits_windowed_shard w positive bounded last h
  rw [checks a ha hb] at hc
  exact Bool.false_ne_true hc

#print axioms counterexample_hits_windowed_shard
#print axioms integer_max148_excluded_of_windowed_shards
#print axioms searchWindowed_true_of_completion

end NineSeparatedSubsetSums
