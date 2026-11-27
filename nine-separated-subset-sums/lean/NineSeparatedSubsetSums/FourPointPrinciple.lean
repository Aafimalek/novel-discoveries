import NineSeparatedSubsetSums.PairPackingDual

open scoped BigOperators

namespace NineSeparatedSubsetSums

def blockCharge (a : ℤ) (charge : ℤ → ℤ) (c : ℤ) : ℤ :=
  charge (c-a-148) + charge (c-a+148) + charge (c+a-148) + charge (c+a+148)

theorem blockSquare_identity (a c : ℤ) :
    blockCharge a (· ^ 2) c = 4*(c^2 + 148^2 + a^2) := by
  unfold blockCharge
  ring

theorem blockCharge_sum_lower (a lam : ℤ) (charge : ℤ → ℤ) (centers : List ℤ)
    (each : ∀ c ∈ centers, lam ≤ blockCharge a charge c) :
    lam * (centers.length : ℤ) ≤ ((spread 148 (spread a centers)).map charge).sum := by
  induction centers with
  | nil => simp [spread]
  | cons c centers ih =>
    have ev := each c List.mem_cons_self
    have rest := ih (fun k hk => each k (List.mem_cons_of_mem _ hk))
    unfold blockCharge at ev
    simp only [spread, List.flatMap_cons, List.cons_append, List.nil_append,
      List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one] at *
    linarith

/-- Every square-plus-penalty block check on the finite anchor range
extends to all centers of the chosen score parity. -/
theorem blockCharge_check_extends (a lam p : ℤ) (penalty : ℤ → ℤ)
    (positive : ∀ z, 0 ≤ penalty z)
    (cap : lam ≤ 4*(801^2 + 148^2 + a^2))
    (localCheck : ∀ j : Fin 1601, (((j.val : ℤ)-800)+a)%2=p →
      lam ≤ blockCharge a (fun z => z^2 + penalty z) ((j.val : ℤ)-800))
    (c : ℤ) (parity : (c+a)%2=p) :
    lam ≤ blockCharge a (fun z => z^2 + penalty z) c := by
  by_cases bound : -800 ≤ c ∧ c ≤ 800
  · let j : Fin 1601 := ⟨(c+800).toNat, by omega⟩
    have hej : (j.val : ℤ)-800 = c := by dsimp [j]; omega
    have hpar : (((j.val : ℤ)-800)+a)%2=p := by rwa [hej]
    simpa only [hej] using localCheck j hpar
  · have sq : (801 : ℤ)^2 ≤ c^2 := by
      by_cases h : c < -800
      · have h' := mul_nonneg (show 0 ≤ -c-801 by omega) (show 0 ≤ -c+801 by omega)
        nlinarith only [h']
      · have h' := mul_nonneg (show 0 ≤ c-801 by omega) (show 0 ≤ c+801 by omega)
        nlinarith only [h']
    have pure := blockSquare_identity a c
    unfold blockCharge at pure ⊢
    linarith [positive (c-a-148), positive (c-a+148), positive (c+a-148), positive (c+a+148)]

theorem selectedPenalty_le_budget (L : List ℤ) (nd : L.Nodup)
    (penalty : ℤ → ℤ) (B : Finset ℤ)
    (positive : ∀ z, 0 ≤ penalty z)
    (support : ∀ z, z ∉ B → penalty z = 0) :
    (L.map penalty).sum ≤ ∑ z ∈ B, penalty z := by
  let S := L.toFinset
  let T := S.filter (fun z => z ∈ B)
  have agree : (∑ z ∈ T, penalty z) = ∑ z ∈ S, penalty z := by
    change (∑ z ∈ S.filter (fun z => z ∈ B), penalty z) = _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases h : z ∈ B <;> simp [h, support]
  have sub : T ⊆ B := fun z hz => (Finset.mem_filter.mp hz).2
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (f := penalty) sub (fun z _ _ => positive z)
  rw [agree, List.sum_toFinset penalty nd] at h
  exact h

/-- Soundness of a four-point packing certificate. Costs are integers, so
a finite table checked in the kernel can be obtained by any untrusted finder. -/
theorem fourPointPacking_lower (a lam : ℤ) (centers : List ℤ)
    (nd : (spread 148 (spread a centers)).Nodup)
    (penalty : ℤ → ℤ) (B : Finset ℤ)
    (positive : ∀ z, 0 ≤ penalty z)
    (support : ∀ z, z ∉ B → penalty z = 0)
    (hblock : ∀ c ∈ centers, lam ≤ blockCharge a (fun z => z^2+penalty z) c) :
    lam * (centers.length : ℤ) - (∑ z ∈ B, penalty z) ≤
      ((spread 148 (spread a centers)).map (· ^ 2)).sum := by
  have h := blockCharge_sum_lower a lam (fun z => z^2+penalty z) centers hblock
  have hb := selectedPenalty_le_budget (spread 148 (spread a centers)) nd penalty B positive support
  rw [List.sum_map_add] at h
  omega

#print axioms blockCharge_check_extends
#print axioms fourPointPacking_lower

end NineSeparatedSubsetSums
