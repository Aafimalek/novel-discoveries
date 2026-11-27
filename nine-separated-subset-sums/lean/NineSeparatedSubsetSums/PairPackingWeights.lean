import NineSeparatedSubsetSums.PairPackingDual
import NineSeparatedSubsetSums.IntegerSearchInput

namespace NineSeparatedSubsetSums

private theorem pair_coe_listSum (xs : List ℕ) : (xs.sum : ℤ) = (xs.map Int.ofNat).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.sum_cons, List.map_cons, Nat.cast_add, ih]
    rfl

private theorem pair_coe_natSubsetSums (l : List ℕ) :
    (natSubsetSums l).map Int.ofNat = (l.map Int.ofNat).sublists.map List.sum := by
  simp only [natSubsetSums, List.sublists_map, List.map_map]
  congr 1
  funext s
  exact pair_coe_listSum s

/-- Exact max-148 packing strengthens the ordinary square-moment lower
bound from 87381 to 101691. Uses only distinct sums and the weight 148. -/
theorem max148_nat_moment_bound (tail : List ℕ) (len : tail.length = 8)
    (distinct : (natSubsetSums (148 :: tail)).Nodup) :
    101691 ≤ ((148 :: tail).map (· ^ 2)).sum := by
  let xs : List ℤ := (148 :: tail : List ℕ).map Int.ofNat
  let tailI : List ℤ := tail.map Int.ofNat
  let scores := signedSums tailI
  have nd : (xs.sublists.map List.sum).Nodup := by
    change (((148 :: tail : List ℕ).map Int.ofNat).sublists.map List.sum).Nodup
    rw [← pair_coe_natSubsetSums]
    exact distinct.map (fun _ _ e => Int.ofNat_inj.mp e)
  have he : signedSums xs =
      (xs.sublists.map List.sum).map (fun z => 2*z-xs.sum) := by
    simp only [signedSums_eq_centered_sublists, List.map_map, Function.comp_def]
  have ns : (signedSums xs).Nodup := by
    rw [he]
    exact nd.map (fun _ _ e => by omega)
  let p := (-xs.sum)%2
  have hp : p=0 ∨ p=1 := by
    dsimp [p]
    omega
  have par : ∀ z ∈ signedSums xs, z%2=p := by
    rw [he]
    intro z hz
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hz
    dsimp [p]
    omega
  have ls : scores.length=256 := by
    simp [scores, tailI, signedSums_length, len]
  have lhs : signedSums xs = spread 148 scores := rfl
  rw [lhs] at ns par
  have hs := pairPackingSquareLower scores ls ns p hp par
  rw [← lhs, signedSums_sum_sq] at hs
  have nine : xs.length=9 := by
    simp [xs, len]
  rw [nine] at hs
  rw [show (2 : ℤ)^9 = 512 by decide] at hs
  have sq : ((((148 :: tail : List ℕ).map (· ^ 2)).sum : ℕ) : ℤ) =
      (xs.map (· ^ 2)).sum := by
    rw [pair_coe_listSum]
    simp only [xs, List.map_map]
    congr 1
  rw [← sq] at hs
  have final : (101691 : ℤ) ≤ (((148 :: tail : List ℕ).map (· ^ 2)).sum : ℕ) := by

    omega
  exact Int.ofNat_le.mp final

/-- The actual Finset integer assumptions force a success in the checked
search at the strengthened square-moment threshold, before evaluation. -/
theorem integer_max148_forces_stronger_search_true (w : Fin 9 → ℤ)
    (positive : ∀ i, 0 < w i) (bounded : ∀ i, w i ≤ 148)
    (last : w (Fin.last 8) = 148)
    (distinct : Function.Injective (fun S : Finset (Fin 9) => ∑ i ∈ S, w i)) :
    searchIntegerWeights 511 101691 8 147 (computeSubsetMask [148]).1 148 (148^2) = true := by
  obtain ⟨t, hlen, hd, hp, hn, ht, _⟩ :=
    integer_max148_to_search_input w positive bounded last distinct
  have hm := max148_nat_moment_bound t hlen hn
  have hu : ∀ x ∈ t, x ≤ 147 := by
    intro x hx
    have h := (List.pairwise_cons.mp hd).1 x hx
    omega
  have h' := search_true_of_completion 511 101691 t [148] 147
    (computeSubsetMask [148]).1 148 (148^2) (computeSubsetMask_correct [148]).1
    (fun x hx => hp x (List.mem_cons_of_mem _ hx)) hu (List.pairwise_cons.mp hd).2 hn
    (by simpa only [List.sum_cons] using ht)
    (by simpa only [List.map_cons, List.sum_cons] using hm)
  rwa [hlen] at h'

#print axioms max148_nat_moment_bound
#print axioms integer_max148_forces_stronger_search_true

end NineSeparatedSubsetSums
