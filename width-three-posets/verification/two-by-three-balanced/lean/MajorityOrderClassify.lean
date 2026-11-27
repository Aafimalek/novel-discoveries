import TwoByThreeReplay
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases

namespace TwoByThreeReplay

private def tag23 (r : Fin 7 → ℕ) : Fin 10 :=
  if r 1 < r 3 then
    if r 2 < r 3 then 0
    else if r 2 < r 4 then 1
    else if r 2 < r 5 then 2 else 3
  else if r 1 < r 4 then
    if r 2 < r 4 then 4
    else if r 2 < r 5 then 5 else 6
  else if r 1 < r 5 then
    if r 2 < r 5 then 7 else 8
  else 9

set_option maxHeartbeats 1600000 in
private theorem tag23_classifies (r : Fin 7 → ℕ) (hinj : Function.Injective r)
    (h01 : r 0 < r 1) (h03 : r 0 < r 3) (h12 : r 1 < r 2) (h34 : r 3 < r 4)
    (h45 : r 4 < r 5) (i j : Fin 7) (hi : i ≠ 6) (hj : j ≠ 6) :
    r i < r j ↔ branchRank (tag23 r) i < branchRank (tag23 r) j := by
  have h13 : r 1 ≠ r 3 := fun h => (by decide : (1 : Fin 7) ≠ 3) (hinj h)
  have h23 : r 2 ≠ r 3 := fun h => (by decide : (2 : Fin 7) ≠ 3) (hinj h)
  have h14 : r 1 ≠ r 4 := fun h => (by decide : (1 : Fin 7) ≠ 4) (hinj h)
  have h24 : r 2 ≠ r 4 := fun h => (by decide : (2 : Fin 7) ≠ 4) (hinj h)
  have h15 : r 1 ≠ r 5 := fun h => (by decide : (1 : Fin 7) ≠ 5) (hinj h)
  have h25 : r 2 ≠ r 5 := fun h => (by decide : (2 : Fin 7) ≠ 5) (hinj h)
  unfold tag23
  repeat' split
  all_goals fin_cases i <;> fin_cases j <;> simp [branchRank] at * <;> omega

private theorem table_filter_card :
    ∀ (p : Fin 10) (i : Fin 7), i ≠ 6 →
      (Finset.univ.filter fun j => j ≠ 6 ∧ branchRank p j < branchRank p i).card =
        branchRank p i := by decide


/-- Classify any distinct rank labels with the six branch labels and root first. -/
theorem classify_rank_permutation_analytic (r : Fin 7 → Fin 7)
    (hinj : Function.Injective r) (hb : r 0 = 0)
    (hx : r 1 < r 2) (hy : r 3 < r 4) (hY : r 4 < r 5) :
    ∃ p : Fin 10, ∃ j : Fin 6, ∀ u : Fin 7, (r u).val = rank p j.succ u := by
  classical
  have hrs : Function.Surjective r := Finite.injective_iff_surjective.mp hinj
  let R (u : Fin 7) := (r u).val
  have hRi : Function.Injective R := fun u v h => hinj (Fin.ext h)
  have h01 : R 0 < R 1 := by
    have hne : r 1 ≠ r 0 := fun h => (by decide : (1 : Fin 7) ≠ 0) (hinj h)
    simp only [hb] at hne
    change (r 0).val < (r 1).val
    rw [hb]
    exact Fin.pos_iff_ne_zero.mpr hne
  have h03 : R 0 < R 3 := by
    have hne : r 3 ≠ r 0 := fun h => (by decide : (3 : Fin 7) ≠ 0) (hinj h)
    simp only [hb] at hne
    change (r 0).val < (r 3).val
    rw [hb]
    exact Fin.pos_iff_ne_zero.mpr hne
  have h6 : r 6 ≠ 0 := fun h => (by decide : (6 : Fin 7) ≠ 0) (hinj (h.trans hb.symm))
  let p := tag23 R
  let j : Fin 6 := (r 6).pred h6
  have hj : j.succ = r 6 := Fin.succ_pred _ _
  refine ⟨p,j,fun u => ?_⟩
  rw [hj]
  by_cases hu : u = 6
  · subst u
    simp [rank]
  have cmp (x : Fin 7) (hn : x ≠ 6) :
      r x < r u ↔ branchRank p x < branchRank p u :=
    tag23_classifies R hRi h01 h03 hx hy hY x u hn hu
  let P : Finset (Fin 7) := Finset.univ.filter fun x => r x < r u
  have he : P.image r = Finset.univ.filter (fun x => x < r u) := by
    ext x
    constructor
    · intro hx'
      obtain ⟨y,hy',rfl⟩ := Finset.mem_image.mp hx'
      simpa only [P, Finset.mem_filter, Finset.mem_univ, true_and] using hy'
    · intro hx'
      obtain ⟨y,rfl⟩ := hrs x
      exact Finset.mem_image.mpr ⟨y,by simpa only [P, Finset.mem_filter, Finset.mem_univ, true_and] using hx',rfl⟩
  have hc : P.card = R u := by
    have aux : ∀ z : Fin 7, (Finset.univ.filter (fun x : Fin 7 => x < z)).card = z.val := by decide
    rw [← Finset.card_image_of_injective P hinj, he]
    exact aux _
  have hErase : P.erase 6 =
      Finset.univ.filter (fun x => x ≠ 6 ∧ branchRank p x < branchRank p u) := by
    ext x
    by_cases h : x = 6
    · simp [h]
    · simp [P,h,cmp x h]
  have hBranch : (P.erase 6).card = branchRank p u := by rw [hErase]; exact table_filter_card p u hu
  have hne : R u ≠ R 6 := fun e => hu (hRi e)
  by_cases h : r 6 < r u
  · have hm : (6 : Fin 7) ∈ P := by simp [P,h]
    have hh : (P.erase 6).card + 1 = P.card := Finset.card_erase_add_one hm
    rw [hc,hBranch] at hh
    change R u = rank p (r 6) u
    have hlt : R 6 < R u := h
    have hle : (r 6).val ≤ branchRank p u := by
      change R 6 ≤ branchRank p u
      omega
    simp [rank,hu,hle,hh]
  · have hn : (6 : Fin 7) ∉ P := by simp [P,h]
    rw [Finset.erase_eq_of_notMem hn,hc] at hBranch
    change R u = rank p (r 6) u
    have hle : R u ≤ R 6 := le_of_not_gt h
    have hn' : ¬ (r 6).val ≤ branchRank p u := by
      change ¬ R 6 ≤ branchRank p u
      omega
    simp [rank,hu,hn',hBranch]

/-- A strict total relation with b first and the known two arms has an order
from the certificate table. This statement contains no probability assumptions. -/
theorem classify_strict_total_order
    (P : Fin 7 → Fin 7 → Prop)
    (hirr : ∀ x, ¬ P x x)
    (htrans : ∀ {x y z}, P x y → P y z → P x z)
    (htot : ∀ {x y}, x ≠ y → P x y ∨ P y x)
    (hb : ∀ x, x ≠ 0 → P 0 x)
    (hx : P 1 2) (hy : P 3 4) (hY : P 4 5) :
    ∃ p : Fin 10, ∃ j : Fin 6, ∀ u v : Fin 7,
      P u v ↔ rank p j.succ u < rank p j.succ v := by
  classical
  let D (x : Fin 7) : Finset (Fin 7) := Finset.univ.filter (fun y => P y x)
  have memD (x y : Fin 7) : y ∈ D x ↔ P y x := by simp [D]
  have hbound (x : Fin 7) : (D x).card < 7 := by
    have hs : D x ⊆ Finset.univ.erase x := by
      intro y hy'
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact fun e => hirr x (e ▸ (memD x y).mp hy')
    have hc := Finset.card_le_card hs
    rw [Finset.card_erase_of_mem (Finset.mem_univ x)] at hc
    simpa using lt_of_le_of_lt hc (by decide : (Fintype.card (Fin 7)) - 1 < 7)
  let r (x : Fin 7) : Fin 7 := ⟨(D x).card, hbound x⟩
  have hlt (x y : Fin 7) (hxy : P x y) : r x < r y := by
    have hs : D x ⊆ D y := fun z hz => (memD y z).mpr (htrans ((memD x z).mp hz) hxy)
    have hstrict : D x ⊂ D y := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hs, fun he => ?_⟩
      have hmem := (memD y x).mpr hxy
      rw [← he] at hmem
      exact hirr x ((memD x x).mp hmem)
    exact Finset.card_lt_card hstrict
  have hI : Function.Injective r := by
    intro x y hEq
    by_contra hne
    rcases htot hne with h | h
    · exact (ne_of_lt (hlt x y h)) hEq
    · exact (ne_of_lt (hlt y x h)) hEq.symm
  have hz : r 0 = 0 := by
    apply Fin.ext
    change (D 0).card = 0
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx'
    have hm := (memD 0 x).mp hx'
    by_cases h : x = 0
    · subst x; exact hirr 0 hm
    · exact hirr 0 (htrans (hb x h) hm)
  obtain ⟨p,j,hr⟩ := classify_rank_permutation_analytic r hI hz (hlt _ _ hx) (hlt _ _ hy) (hlt _ _ hY)
  refine ⟨p,j, fun u v => ?_⟩
  rw [← hr u, ← hr v]
  change P u v ↔ r u < r v
  constructor
  · exact hlt u v
  · intro h
    have hn : u ≠ v := fun e => lt_irrefl _ (e ▸ h)
    rcases htot hn with ho | ho
    · exact ho
    · exact (lt_asymm h (hlt v u ho)).elim

#print axioms classify_rank_permutation_analytic
#print axioms classify_strict_total_order
end TwoByThreeReplay
