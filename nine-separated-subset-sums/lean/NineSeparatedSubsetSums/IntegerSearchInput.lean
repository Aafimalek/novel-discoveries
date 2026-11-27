import NineSeparatedSubsetSums.ConstructDifferenceMask
import NineSeparatedSubsetSums.IntegerMomentBridge
import NineSeparatedSubsetSums.IntegerSearchSound
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

namespace NineSeparatedSubsetSums

private theorem coe_natListSum (l : List ℕ) :
    (l.sum : ℤ) = (l.map Int.ofNat).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.sum_cons, List.map_cons, Nat.cast_add, ih]
    rfl

private theorem coe_natSubsetSums (l : List ℕ) :
    (natSubsetSums l).map Int.ofNat = (l.map Int.ofNat).sublists.map List.sum := by
  simp only [natSubsetSums, List.sublists_map, List.map_map]
  congr 1
  funext s
  exact coe_natListSum s

theorem nat_moment_bound_of_distinct_subset_sums (l : List ℕ) (len : l.length = 9)
    (distinct : (natSubsetSums l).Nodup) : 87381 ≤ (l.map (· ^ 2)).sum := by
  have hi : ((natSubsetSums l).map Int.ofNat).Nodup := distinct.map
    (fun _ _ eq => Int.ofNat_inj.mp eq)
  rw [coe_natSubsetSums] at hi
  have bound := integerMomentBoundOfDistinctSublists (l.map Int.ofNat)
    (by simpa only [List.length_map] using len) hi
  have eq : (((l.map (· ^ 2)).sum : ℕ) : ℤ) = ((l.map Int.ofNat).map (· ^ 2)).sum := by
    rw [coe_natListSum]
    simp only [List.map_map]
    congr 1
  rw [← eq] at bound
  exact Int.ofNat_le.mp bound

theorem nat_total_bound_of_distinct_subset_sums (l : List ℕ) (len : l.length = 9)
    (distinct : (natSubsetSums l).Nodup) : 511 ≤ l.sum := by
  have cnt : (natSubsetSums l).toFinset.card = 512 := by
    rw [List.toFinset_card_of_nodup distinct]
    simp [natSubsetSums, List.length_sublists, len]
  have inside : (natSubsetSums l).toFinset ⊆ Finset.range (l.sum + 1) := by
    intro x hx
    apply Finset.mem_range.mpr
    have hx' := natSubsetSums_le_sum (List.mem_toFinset.mp hx)
    omega
  have cle := Finset.card_le_card inside
  rw [cnt, Finset.card_range] at cle
  omega

/-- Distinct Finset subset sums stay distinct when obtained from a
duplicate-free list of indices, provided the list is sorted by the
injective natural weight values. -/
private theorem natSubsetSums_nodup_of_sorted_indices {ι : Type*} [DecidableEq ι]
    (idx : List ι) (w : ι → ℕ) (nd : idx.Nodup)
    (sorted : idx.Pairwise (fun i j => w j ≤ w i))
    (sep : Function.Injective (fun S : Finset ι => ∑ i ∈ S, w i))
    (inj : Function.Injective w) : (natSubsetSums (idx.map w)).Nodup := by
  simp only [natSubsetSums, List.sublists_map, List.map_map]
  apply nd.sublists.map_on
  intro s hs t ht eq
  have subS := List.mem_sublists.mp hs
  have subT := List.mem_sublists.mp ht
  have ns := subS.nodup nd
  have nt := subT.nodup nd
  change (s.map w).sum = (t.map w).sum at eq
  rw [← List.sum_toFinset w ns, ← List.sum_toFinset w nt] at eq
  have same := sep eq
  have pr : s.Perm t := (List.perm_ext_iff_of_nodup ns nt).mpr (fun i => by
    rw [← List.mem_toFinset, same, List.mem_toFinset])
  exact List.Perm.eq_of_pairwise (le := fun i j => w j ≤ w i)
    (fun i j _ _ h₁ h₂ => inj (le_antisymm h₂ h₁)) (sorted.sublist subS) (sorted.sublist subT) pr

/-- Convert the actual nine-weight integer problem into the precise
positive descending list and lower bounds expected by the search. -/
theorem integer_max148_to_search_input (w : Fin 9 → ℤ)
    (positive : ∀ i, 0 < w i) (bounded : ∀ i, w i ≤ 148)
    (last : w (Fin.last 8) = 148)
    (distinct : Function.Injective (fun S : Finset (Fin 9) => ∑ i ∈ S, w i)) :
    ∃ t : List ℕ, t.length = 8 ∧
      (148 :: t).Pairwise (· > ·) ∧
      (∀ x ∈ 148 :: t, 0 < x) ∧
      (natSubsetSums (148 :: t)).Nodup ∧
      511 ≤ (148 :: t).sum ∧
      87381 ≤ ((148 :: t).map (· ^ 2)).sum := by
  let wn (i : Fin 9) : ℕ := (w i).toNat
  have lift (i : Fin 9) : (wn i : ℤ) = w i := Int.toNat_of_nonneg (le_of_lt (positive i))
  have natsep : Function.Injective (fun S : Finset (Fin 9) => ∑ i ∈ S, wn i) := by
    intro A B eq
    apply distinct
    have h := congrArg (fun n : ℕ => (n : ℤ)) eq
    simpa only [Nat.cast_sum, lift] using h
  have inj : Function.Injective wn := by
    intro i j e
    apply Finset.singleton_injective
    apply natsep
    simpa only [Finset.sum_singleton] using e
  let le (i j : Fin 9) : Bool := decide (wn j ≤ wn i)
  let idx : List (Fin 9) := (List.finRange 9).mergeSort le
  have ps : idx.Perm (List.finRange 9) := List.mergeSort_perm _ _
  have ni : idx.Nodup := ps.nodup_iff.mpr (List.nodup_finRange 9)
  have pl : idx.Pairwise (fun i j => wn j ≤ wn i) := by
    have tr (i j k : Fin 9) : le i j → le j k → le i k := by
      dsimp [le]
      simp only [decide_eq_true_eq]
      exact fun hij hjk => le_trans hjk hij
    have totalLE (i j : Fin 9) : le i j || le j i := by
      dsimp [le]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total (wn j) (wn i)
    have hs := List.pairwise_mergeSort tr totalLE (List.finRange 9)
    exact hs.imp (by simp [le])
  let L : List ℕ := idx.map wn
  have lc : L.length = 9 := by
    dsimp [L]
    rw [List.length_map, ps.length_eq, List.length_finRange]
  have dp : L.Pairwise (· > ·) := by
    change (idx.map wn).Pairwise (· > ·)
    rw [List.pairwise_map]
    have hn : idx.Pairwise (· ≠ ·) := List.nodup_iff_pairwise_ne.mp ni
    refine (List.pairwise_and_iff.mpr ⟨pl,hn⟩).imp ?_
    intro i j h
    exact lt_of_le_of_ne h.1 (fun e => h.2 (inj e.symm))
  have nsub : (natSubsetSums L).Nodup :=
    natSubsetSums_nodup_of_sorted_indices idx wn ni pl natsep inj
  have mn : 87381 ≤ (L.map (· ^ 2)).sum := nat_moment_bound_of_distinct_subset_sums L lc nsub
  have tt : 511 ≤ L.sum := nat_total_bound_of_distinct_subset_sums L lc nsub
  have pos : ∀ x ∈ L, 0 < x := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    have hp := positive i
    have hh := lift i
    omega
  have upper : ∀ x ∈ L, x ≤ 148 := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    have hb := bounded i
    have hh := lift i
    omega
  have q : 148 ∈ L := by
    apply List.mem_map.mpr
    refine ⟨Fin.last 8, ps.mem_iff.mpr (List.mem_finRange _), ?_⟩
    have h := lift (Fin.last 8)
    omega
  have nonempty : L ≠ [] := by
    intro h
    simp [h] at lc
  obtain ⟨a,t,hL⟩ := List.exists_cons_of_ne_nil nonempty
  have haHi := upper a (by simp [hL])
  rw [hL] at q dp
  have ha : a = 148 := by
    rcases List.mem_cons.mp q with h | h
    · omega
    · have hl := (List.pairwise_cons.mp dp).1 148 h
      omega
  refine ⟨t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hL] at lc
    omega
  · simpa [ha] using dp
  · simpa [hL, ha] using pos
  · simpa [hL, ha] using nsub
  · simpa [hL, ha] using tt
  · simpa [hL, ha] using mn

/-- A counterexample would force the verified finite integer search
to return true at its actual initial state. No evaluation is assumed. -/
theorem integer_max148_forces_search_true (w : Fin 9 → ℤ)
    (positive : ∀ i, 0 < w i) (bounded : ∀ i, w i ≤ 148)
    (last : w (Fin.last 8) = 148)
    (distinct : Function.Injective (fun S : Finset (Fin 9) => ∑ i ∈ S, w i)) :
    searchIntegerWeights 511 87381 8 147 (computeSubsetMask [148]).1 148 (148^2) = true := by
  obtain ⟨t, hlen, hd, hp, hn, ht, hm⟩ :=
    integer_max148_to_search_input w positive bounded last distinct
  have hu : ∀ x ∈ t, x ≤ 147 := by
    intro x hx
    have hh := (List.pairwise_cons.mp hd).1 x hx
    omega
  have h' := search_true_of_completion 511 87381 t [148] 147
    (computeSubsetMask [148]).1 148 (148^2) (computeSubsetMask_correct [148]).1
    (fun x hx => hp x (List.mem_cons_of_mem _ hx)) hu (List.pairwise_cons.mp hd).2 hn
    (by simpa only [List.sum_cons] using ht)
    (by simpa only [List.map_cons, List.sum_cons] using hm)
  rwa [hlen] at h'

#print axioms nat_moment_bound_of_distinct_subset_sums
#print axioms nat_total_bound_of_distinct_subset_sums
#print axioms integer_max148_to_search_input
#print axioms integer_max148_forces_search_true

end NineSeparatedSubsetSums
