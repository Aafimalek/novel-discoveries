import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card

namespace NineSeparatedSubsetSums

open scoped BigOperators

variable {ι β : Type*} [DecidableEq ι]

def slabScore (w : ι → ℝ) (P : Finset ι) : ℝ := ∑ i ∈ P, w i

def IsWeightSlab (w : ι → ℝ) (c M : ℝ) (P : Finset ι) : Prop :=
  c - M ≤ slabScore w P ∧ slabScore w P ≤ c + M

private def slabDistance (P Q : Finset ι) : ℕ :=
  (P \ Q).card + (Q \ P).card

private theorem slabDistance_pos {P Q : Finset ι} (hne : P ≠ Q) : 0 < slabDistance P Q := by
  by_contra h
  have hh : (P \ Q).card + (Q \ P).card = 0 := by
    change ¬ 0 < (P \ Q).card + (Q \ P).card at h
    omega
  have h₁ : (P \ Q).card = 0 := by omega
  have h₂ : (Q \ P).card = 0 := by omega
  have hp := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp h₁)
  have hq := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp h₂)
  exact hne (Finset.Subset.antisymm hp hq)

private theorem slabDistance_insert {P Q : Finset ι} {a : ι} (ha : a ∈ Q \ P) :
    slabDistance (insert a P) Q < slabDistance P Q := by
  dsimp [slabDistance]
  rw [Finset.insert_sdiff_of_mem P (Finset.mem_sdiff.mp ha).1, Finset.sdiff_insert]
  have h := Finset.card_erase_add_one ha
  omega

private theorem slabDistance_erase {P Q : Finset ι} {a : ι} (ha : a ∈ P \ Q) :
    slabDistance (P.erase a) Q < slabDistance P Q := by
  have haQ := (Finset.mem_sdiff.mp ha).2
  have he : Q \ P.erase a = Q \ P := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_erase]
    constructor
    · rintro ⟨hxQ, hn⟩
      have hne : x ≠ a := fun h => haQ (h ▸ hxQ)
      exact ⟨hxQ, fun hxP => hn ⟨hne, hxP⟩⟩
    · rintro ⟨hxQ, hn⟩
      exact ⟨hxQ, fun hx => hn hx.2⟩
  dsimp [slabDistance]
  rw [Finset.erase_sdiff_comm, he]
  have h := Finset.card_erase_add_one ha
  omega

private theorem slabScore_mono (w : ι → ℝ) {U P Q : Finset ι}
    (hw : ∀ i ∈ U, 0 ≤ w i ∧ w i ≤ M) (hPQ : P ⊆ Q) (hQU : Q ⊆ U) :
    slabScore w P ≤ slabScore w Q := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hPQ (fun i hi _ => (hw i (hQU hi)).1)

private theorem slabScore_insert (w : ι → ℝ) {P : Finset ι} {a : ι} (ha : a ∉ P) :
    slabScore w (insert a P) = slabScore w P + w a := by
  simp [slabScore, Finset.sum_insert ha, add_comm]

private theorem slabScore_erase (w : ι → ℝ) {P : Finset ι} {a : ι} (ha : a ∈ P) :
    slabScore w (P.erase a) = slabScore w P - w a := by
  have h := Finset.sum_erase_add P w ha
  change (∑ i ∈ P.erase a, w i) = (∑ i ∈ P, w i) - w a
  exact eq_sub_iff_add_eq.mpr h

/-- A label invariant under each one-coordinate step between slab vertices
is constant on the slab. The ambient hypercube consists of all subsets of
the finite set U, and every coordinate weight must lie in [0,M].

The induction corrects one disagreement with Q at each step. When both
additions and deletions remain, add in the lower half of the slab and
delete in the upper half. When only one kind remains, use monotonicity
between the endpoints. -/
theorem slab_constancy (U : Finset ι) (w : ι → ℝ) (c M : ℝ) (label : Finset ι → β)
    (hw : ∀ i ∈ U, 0 ≤ w i ∧ w i ≤ M)
    (hstep : ∀ (S : Finset ι) (a : ι), S ⊆ U → a ∈ U → a ∉ S →
      IsWeightSlab w c M S → IsWeightSlab w c M (insert a S) →
      label S = label (insert a S))
    {P Q : Finset ι} (hPU : P ⊆ U) (hQU : Q ⊆ U)
    (hP : IsWeightSlab w c M P) (hQ : IsWeightSlab w c M Q) :
    label P = label Q := by
  suffices hfuel : ∀ k (S : Finset ι), S ⊆ U → IsWeightSlab w c M S →
      slabDistance S Q ≤ k → label S = label Q from
    hfuel (slabDistance P Q) P hPU hP le_rfl
  intro k
  induction k with
  | zero =>
      intro S hSU hS hk
      by_cases heq : S = Q
      · rw [heq]
      · have hpos := slabDistance_pos heq
        omega
  | succ k ih =>
      intro S hSU hS hk
      by_cases heq : S = Q
      · rw [heq]
      have add_step (a : ι) (ha : a ∈ Q \ S)
          (hNew : IsWeightSlab w c M (insert a S)) : label S = label Q := by
        obtain ⟨haQ, haS⟩ := Finset.mem_sdiff.mp ha
        have haU := hQU haQ
        have hInsU : insert a S ⊆ U := Finset.insert_subset_iff.mpr ⟨haU, hSU⟩
        have hd := slabDistance_insert ha
        exact (hstep S a hSU haU haS hS hNew).trans
          (ih (insert a S) hInsU hNew (by omega))
      have del_step (a : ι) (ha : a ∈ S \ Q)
          (hNew : IsWeightSlab w c M (S.erase a)) : label S = label Q := by
        have haS := (Finset.mem_sdiff.mp ha).1
        have hEraseU : S.erase a ⊆ U := (Finset.erase_subset _ _).trans hSU
        have hAdj := hstep (S.erase a) a hEraseU (hSU haS) (Finset.notMem_erase _ _) hNew
        rw [Finset.insert_erase haS] at hAdj
        have hd := slabDistance_erase ha
        exact (hAdj hS).symm.trans (ih (S.erase a) hEraseU hNew (by omega))
      by_cases hAdd : (Q \ S).Nonempty
      · obtain ⟨a, ha⟩ := hAdd
        obtain ⟨haQ, haS⟩ := Finset.mem_sdiff.mp ha
        by_cases hDel : (S \ Q).Nonempty
        · obtain ⟨b, hb⟩ := hDel
          by_cases hMid : slabScore w S ≤ c
          · apply add_step a ha
            change c - M ≤ slabScore w (insert a S) ∧ slabScore w (insert a S) ≤ c + M
            rw [slabScore_insert w haS]
            obtain ⟨ha0, haM⟩ := hw a (hQU haQ)
            exact ⟨hS.1.trans (le_add_of_nonneg_right ha0), add_le_add hMid haM⟩
          · apply del_step b hb
            have hbS := (Finset.mem_sdiff.mp hb).1
            change c - M ≤ slabScore w (S.erase b) ∧ slabScore w (S.erase b) ≤ c + M
            rw [slabScore_erase w hbS]
            obtain ⟨hb0, hbM⟩ := hw b (hSU hbS)
            exact ⟨sub_le_sub (lt_of_not_ge hMid).le hbM, (sub_le_self _ hb0).trans hS.2⟩
        · have hSQ : S ⊆ Q := Classical.byContradiction fun h => hDel (Finset.sdiff_nonempty.mpr h)
          have hInsQ : insert a S ⊆ Q := Finset.insert_subset_iff.mpr ⟨haQ, hSQ⟩
          have hInsU := hInsQ.trans hQU
          apply add_step a ha
          exact ⟨hS.1.trans (slabScore_mono w hw (Finset.subset_insert _ _) hInsU),
            (slabScore_mono w hw hInsQ hQU).trans hQ.2⟩
      · have hQS : Q ⊆ S := Classical.byContradiction fun h => hAdd (Finset.sdiff_nonempty.mpr h)
        have hDel : (S \ Q).Nonempty := Finset.sdiff_nonempty.mpr
          (fun hSQ => heq (Finset.Subset.antisymm hSQ hQS))
        obtain ⟨b, hb⟩ := hDel
        have hbQ := (Finset.mem_sdiff.mp hb).2
        have hEraseQ : Q ⊆ S.erase b := Finset.subset_erase.mpr ⟨hQS, hbQ⟩
        apply del_step b hb
        exact ⟨hQ.1.trans (slabScore_mono w hw hEraseQ ((Finset.erase_subset _ _).trans hSU)),
          (slabScore_mono w hw (Finset.erase_subset _ _) hSU).trans hS.2⟩

#print axioms NineSeparatedSubsetSums.slab_constancy

end NineSeparatedSubsetSums


namespace NineSeparatedSubsetSums

variable {ι : Type*} [DecidableEq ι]

/-- A symmetric edge of the induced slab subgraph of the subset cube. -/
def WeightSlabStep (U : Finset ι) (w : ι → ℝ) (c M : ℝ) (P Q : Finset ι) : Prop :=
  P ⊆ U ∧ Q ⊆ U ∧ IsWeightSlab w c M P ∧ IsWeightSlab w c M Q ∧
    ∃ a ∈ U, (a ∉ P ∧ Q = insert a P) ∨ (a ∉ Q ∧ P = insert a Q)

/-- Any two vertices in the weighted slab are joined by one-coordinate edges
of the slab subgraph. -/
theorem weight_slab_connected (U : Finset ι) (w : ι → ℝ) (c M : ℝ)
    (hw : ∀ i ∈ U, 0 ≤ w i ∧ w i ≤ M)
    {P Q : Finset ι} (hPU : P ⊆ U) (hQU : Q ⊆ U)
    (hP : IsWeightSlab w c M P) (hQ : IsWeightSlab w c M Q) :
    Relation.ReflTransGen (WeightSlabStep U w c M) P Q := by
  let label := fun S : Finset ι => Relation.ReflTransGen (WeightSlabStep U w c M) P S
  have hstep (S : Finset ι) (a : ι) (hSU : S ⊆ U) (haU : a ∈ U) (haS : a ∉ S)
      (hS : IsWeightSlab w c M S) (hT : IsWeightSlab w c M (insert a S)) :
      label S = label (insert a S) := by
    have hTU : insert a S ⊆ U := Finset.insert_subset_iff.mpr ⟨haU, hSU⟩
    have hAdd : WeightSlabStep U w c M S (insert a S) :=
      ⟨hSU, hTU, hS, hT, ⟨a, haU, Or.inl ⟨haS, rfl⟩⟩⟩
    have hDel : WeightSlabStep U w c M (insert a S) S :=
      ⟨hTU, hSU, hT, hS, ⟨a, haU, Or.inr ⟨haS, rfl⟩⟩⟩
    exact propext ⟨fun h => h.tail hAdd, fun h => h.tail hDel⟩
  have hEq := slab_constancy U w c M label hw hstep hPU hQU hP hQ
  exact Eq.mp hEq Relation.ReflTransGen.refl

#print axioms NineSeparatedSubsetSums.weight_slab_connected

end NineSeparatedSubsetSums

