import TwoByThreeWeights
import MajorityOrderClassify

namespace TwoByThreeReplay

private theorem branchRank_inj :
    ∀ p : Fin 10, ∀ u v : Fin 7, u ≠ 6 → v ≠ 6 → u ≠ v →
      branchRank p u ≠ branchRank p v := by decide

private theorem component_complement (p : Fin 10) (k u v : Fin 7) (hne : u ≠ v) :
    component p k u v + component p k v u = k.val+1 := by
  by_cases hu : u = 6
  · subst u
    have hv : v ≠ 6 := hne.symm
    simp only [component, ite_true, ite_eq_right hv]
    have hm := min_le_left (k.val+1) (branchRank p v+1)
    omega
  · by_cases hv : v = 6
    · subst v
      simp only [component, ite_true, ite_eq_right hu]
      have hm := min_le_left (k.val+1) (branchRank p u+1)
      omega
    · simp only [component, ite_eq_right hu, ite_eq_right hv]
      rcases lt_or_gt_of_ne (branchRank_inj p u v hu hv hne) with h | h
      · simp [h,not_lt_of_ge h.le]
      · simp [h,not_lt_of_ge h.le]

private theorem modelCount_complement (w : Profiles) {u v : Fin 7} (hne : u ≠ v) :
    modelCount w u v + modelCount w v u = modelMass w := by
  unfold modelCount modelMass
  simp only [← Finset.sum_add_distrib, ← Nat.add_mul, component_complement _ _ _ _ hne]

private theorem modelCount_diag (w : Profiles) (u : Fin 7) : modelCount w u u = 0 := by
  unfold modelCount
  simp [component_as_sum]

private theorem component_triangle (p : Fin 10) (k x y z : Fin 7) :
    component p k x y + component p k y z + component p k z x ≤ 2 * (k.val+1) := by
  have hsize : k.val+1 = ∑ j : Fin 7, if j ≤ k then 1 else 0 := by
    have h : ∀ k : Fin 7, k.val+1 = ∑ j : Fin 7, if j ≤ k then 1 else 0 := by decide
    exact h k
  rw [component_as_sum p k x y, component_as_sum p k y z, component_as_sum p k z x,
    hsize, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j ≤ k
  · simp only [hj,true_and,ite_true]
    split <;> split <;> split <;> omega
  · simp [hj]

private theorem modelCount_triangle (w : Profiles) (x y z : Fin 7) :
    modelCount w x y + modelCount w y z + modelCount w z x ≤ 2 * modelMass w := by
  unfold modelCount modelMass
  simp only [← Finset.sum_add_distrib, ← Nat.add_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  apply Finset.sum_le_sum
  intro k _
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (w p k) (component_triangle p k x y z)

def Strong (w : Profiles) (u v : Fin 7) : Prop := 2 * modelMass w < 3 * modelCount w u v

def HasBalanced (w : Profiles) : Prop := ∃ u v : Fin 7, u ≠ v ∧
  modelMass w ≤ 3 * modelCount w u v ∧ 3 * modelCount w u v ≤ 2 * modelMass w

private theorem strong_irrefl (w : Profiles) (u : Fin 7) : ¬ Strong w u u := by
  unfold Strong
  rw [modelCount_diag]
  omega

private theorem strong_asymm (w : Profiles) {u v : Fin 7}
    (h : Strong w u v) (h' : Strong w v u) : False := by
  have hne : u ≠ v := by
    intro e
    subst v
    exact strong_irrefl w u h
  have hc := modelCount_complement w hne
  simp only [Strong] at h h'
  omega

private theorem strong_total (w : Profiles) (hn : ¬ HasBalanced w) {u v : Fin 7}
    (hne : u ≠ v) : Strong w u v ∨ Strong w v u := by
  have hsum := modelCount_complement w hne
  have hnot : ¬ (modelMass w ≤ 3 * modelCount w u v ∧
      3 * modelCount w u v ≤ 2 * modelMass w) := fun he => hn ⟨u,v,hne,he⟩
  simp only [Strong]
  omega

private theorem strong_trans (w : Profiles) (hn : ¬ HasBalanced w) {u v z : Fin 7}
    (huv : Strong w u v) (hvz : Strong w v z) : Strong w u z := by
  have hne : u ≠ z := by
    intro h
    subst z
    exact strong_asymm w huv hvz
  rcases strong_total w hn hne with h | h
  · exact h
  · have ht := modelCount_triangle w u v z
    simp only [Strong] at huv hvz h
    omega

private theorem always_count (w : Profiles) {u v : Fin 7}
    (hu : u ≠ 6) (hv : v ≠ 6) (h : ∀ p : Fin 10, branchRank p u < branchRank p v) :
    modelCount w u v = modelMass w := by
  unfold modelCount modelMass
  simp only [component, ite_eq_right hu, ite_eq_right hv, ite_eq_left (h _)]

/-- Without a balanced comparison and with root-first probability ≤1/2, the
strict majorities of a cutoff mixture form a classified majority order. -/
theorem exists_classified_strong_order (w : Profiles)
    (hn : ¬ HasBalanced w) (cap : 2 * modelCount w 6 0 ≤ modelMass w) :
    ∃ p : Fin 10, ∃ j : Fin 6,
      ∀ u v : Fin 7, Strong w u v ↔ rank p j.succ u < rank p j.succ v := by
  have hN : 0 < modelMass w := by
    by_contra! h
    have hc := modelCount_complement w (by decide : (0 : Fin 7) ≠ 1)
    exact hn ⟨0,1,by decide,by omega⟩
  have hb (u : Fin 7) (hne : u ≠ 0) : Strong w 0 u := by
    by_cases h6 : u = 6
    · subst u
      rcases strong_total w hn (by decide : (0 : Fin 7) ≠ 6) with h | h
      · exact h
      · simp only [Strong] at h
        omega
    · have hl : ∀ p : Fin 10, ∀ u : Fin 7, u ≠ 0 → u ≠ 6 →
          branchRank p 0 < branchRank p u := by decide
      have C := always_count w (by decide : (0 : Fin 7) ≠ 6) h6 (fun p => hl p u hne h6)
      unfold Strong
      omega
  have hx : Strong w 1 2 := by
    have C := always_count w (u:=1) (v:=2) (by decide) (by decide) (by decide)
    unfold Strong
    omega
  have hy : Strong w 3 4 := by
    have C := always_count w (u:=3) (v:=4) (by decide) (by decide) (by decide)
    unfold Strong
    omega
  have hY : Strong w 4 5 := by
    have C := always_count w (u:=4) (v:=5) (by decide) (by decide) (by decide)
    unfold Strong
    omega
  exact classify_strict_total_order (Strong w) (strong_irrefl w)
    (strong_trans w hn) (strong_total w hn) hb hx hy hY

#print axioms exists_classified_strong_order
end TwoByThreeReplay
