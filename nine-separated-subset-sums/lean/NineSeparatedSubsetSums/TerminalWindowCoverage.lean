import NineSeparatedSubsetSums.IntegerShardCoverage
import NineSeparatedSubsetSums.TerminalWindowShard104
import NineSeparatedSubsetSums.RealReduction

namespace NineSeparatedSubsetSums

/-- The same second-largest weight also selects the terminal-window search. -/
theorem counterexample_hits_all_three_shards (w : Fin 9 → ℤ)
    (positive : ∀ i, 0 < w i) (bounded : ∀ i, w i ≤ 148)
    (last : w (Fin.last 8) = 148)
    (distinct : Function.Injective (fun S : Finset (Fin 9) => ∑ i ∈ S, w i)) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ 147 ∧ integer_second_shard a = true ∧ windowed_second_shard a = true ∧ windowed_cap_second_shard a = true := by
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
    have hbase := search_true_of_completion 511 87381 t [148,a] (a - 1)
      (computeSubsetMask [148,a]).1 (148+a) (148^2+a^2)
      (computeSubsetMask_correct [148,a]).1
      (fun x hx => hp x (by simp [hx])) hsmall (List.pairwise_cons.mp inner).2 hn
      (by simpa only [List.sum_cons, Nat.add_assoc] using ht)
      (by simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using hm)
    rw [count] at hbase
    have hcap := searchWindowedCap_true_of_completion 511 87381 t [148,a] (a - 1)
      (computeSubsetMask [148,a]).1 (148+a) (148^2+a^2)
      (computeSubsetMask_correct [148,a]).1 (by simp) (by simp)
      (fun x hx => hp x (by simp [hx])) hsmall (List.pairwise_cons.mp inner).2 hn
      (by simpa only [List.sum_cons, Nat.add_assoc] using ht)
      (by simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using hm)
    rw [count] at hcap
    exact ⟨a, ha, hb, hbase, h, hcap⟩

/-- A counterexample to the integer exclusion must have a weight from 105 to 147
as its second-largest weight. The terminal-window search must be true there. -/
theorem counterexample_hits_terminal_window_shard_above_104 (w : Fin 9 → ℤ)
    (positive : ∀ i, 0 < w i) (bounded : ∀ i, w i ≤ 148)
    (last : w (Fin.last 8) = 148)
    (distinct : Function.Injective (fun S : Finset (Fin 9) => ∑ i ∈ S, w i)) :
    ∃ a : ℕ, 105 ≤ a ∧ a ≤ 147 ∧ windowed_cap_second_shard a = true := by
  obtain ⟨a, ha, hb, base, window, cap⟩ := counterexample_hits_all_three_shards w positive bounded last distinct
  have low : ¬ a ≤ 100 := by
    intro h
    have eq := all_shards_through_100 ⟨a, by omega⟩
    change integer_second_shard a = false at eq
    simp [eq] at base
  have h101 : a ≠ 101 := by
    rintro rfl
    simp [shard_101_checked] at base
  have h102 : a ≠ 102 := by
    rintro rfl
    simp [windowedShard_102_checked] at window
  have h103 : a ≠ 103 := by
    rintro rfl
    simp [windowedShard_103_checked] at window
  have h104 : a ≠ 104 := by
    rintro rfl
    simp [capShard_104_checked] at cap
  exact ⟨a, by omega, hb, cap⟩

/-- To verify the 149 bound it now suffices to close the explicitly stated remaining Bool checks. -/
theorem separated_nine_at_least_149_of_remaining_terminal_window_shards
    (checks : ∀ a : ℕ, 105 ≤ a → a ≤ 147 → windowed_cap_second_shard a = false)
    (w : Fin 9 → ℝ) (hpos : ∀ i, 0 < w i)
    (sep : ∀ A B : Finset (Fin 9), A ≠ B →
      1 ≤ |(∑ i ∈ A, w i) - (∑ i ∈ B, w i)|) :
    ∃ i, 149 ≤ w i := by
  apply separated_nine_at_least_149_of_integer_exclusion _ w hpos sep
  intro a ha hmax hi
  obtain ⟨j, hlo, hhi, hc⟩ := counterexample_hits_terminal_window_shard_above_104 a
    (fun i => by have := (ha i).1; omega) (fun i => (ha i).2) hmax hi
  rw [checks j hlo hhi] at hc
  exact Bool.false_ne_true hc

#print axioms separated_nine_at_least_149_of_remaining_terminal_window_shards
#print axioms counterexample_hits_all_three_shards
#print axioms counterexample_hits_terminal_window_shard_above_104

end NineSeparatedSubsetSums
