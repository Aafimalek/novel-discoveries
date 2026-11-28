import FranklAtLeastThreeIsolates
import FranklTripleDegree

/- Checked by pinned ordinary Lean with warnings as errors. -/
open scoped BigOperators
namespace FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

/-- The size-two-excess of blocks through a point is its exact degree
deficit. This identity works without any restrictions on block sizes. -/
theorem designDegree_add_incident_excess {S : Finset α} {B : Finset (Finset α)} {v : α}
    (hD : PairDesign S B) (hv : v ∈ S) :
    designDegree B v + (∑ A ∈ B.filter (v ∈ ·), (A.card - 2)) + 1 = S.card := by
  classical
  let D := B.filter (v ∈ ·)
  have hU : D.biUnion (fun A => A.erase v) = S.erase v := by
    ext u
    constructor
    · intro hu
      obtain ⟨A,hA,huA⟩ := Finset.mem_biUnion.mp hu
      obtain ⟨hAB,_⟩ := Finset.mem_filter.mp hA
      obtain ⟨hne,h⟩ := Finset.mem_erase.mp huA
      exact Finset.mem_erase.mpr ⟨hne,(hD.1 A hAB).1 h⟩
    · intro hu
      obtain ⟨hvn,huS⟩ := Finset.mem_erase.mp hu
      obtain ⟨A,⟨hAB,hvA,huA⟩,_⟩ := hD.2 v hv u huS hvn.symm
      exact Finset.mem_biUnion.mpr ⟨A,Finset.mem_filter.mpr ⟨hAB,hvA⟩,
        Finset.mem_erase.mpr ⟨hvn,huA⟩⟩
  have hDisj : (D : Set (Finset α)).PairwiseDisjoint (fun A => A.erase v) := by
    intro A hA C hC hne
    apply Finset.disjoint_left.mpr
    intro u huA huC
    obtain ⟨hAB,hvA⟩ := Finset.mem_filter.mp hA
    obtain ⟨hCB,hvC⟩ := Finset.mem_filter.mp hC
    obtain ⟨hvu,huA'⟩ := Finset.mem_erase.mp huA
    obtain ⟨_,huC'⟩ := Finset.mem_erase.mp huC
    obtain ⟨_,_,hUnique⟩ := hD.2 v hv u ((hD.1 A hAB).1 huA') hvu.symm
    exact hne ((hUnique _ ⟨hAB,hvA,huA'⟩).trans (hUnique _ ⟨hCB,hvC,huC'⟩).symm)
  have hCount := Finset.card_biUnion hDisj
  rw [hU] at hCount
  have hSum : (∑ A ∈ D, (A.erase v).card) = ∑ A ∈ D, (1 + (A.card - 2)) := by
    apply Finset.sum_congr rfl
    intro A hA
    obtain ⟨hAB,hvA⟩ := Finset.mem_filter.mp hA
    have hCard := Finset.card_erase_add_one hvA
    have hLower := (hD.1 A hAB).2
    omega
  rw [hSum,Finset.sum_add_distrib,← Finset.card_eq_sum_ones] at hCount
  have hErase := Finset.card_erase_add_one hv
  change D.card + (∑ A ∈ D, (A.card - 2)) + 1 = S.card
  omega

/-- Deficit at most one puts every block at size two or three, and
any triples are vertex-disjoint. The exact pair-budget and disjoint
triple vertex budget are stated for direct downstream use. -/
theorem deficit_le_one_triples_classification {S : Finset α} {B : Finset (Finset α)}
    (hD : PairDesign S B)
    (hDeg : ∀ v ∈ S, S.card ≤ designDegree B v + 2) :
    (∀ A ∈ B, A.card ≤ 3) ∧
    (triples B : Set (Finset α)).PairwiseDisjoint id ∧
    B.card + 2 * (triples B).card = S.card.choose 2 ∧
    3 * (triples B).card ≤ S.card := by
  classical
  have h3 : ∀ A ∈ B, A.card ≤ 3 := by
    intro A hA
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < A.card from
      lt_of_lt_of_le (by decide : 0 < 2) (hD.1 A hA).2)
    have hvS := (hD.1 A hA).1 hv
    have hCap := hDeg v hvS
    have hE := designDegree_add_incident_excess hD hvS
    have hOne : A.card - 2 ≤ ∑ C ∈ B.filter (v ∈ ·), (C.card - 2) :=
      Finset.single_le_sum (f := fun C : Finset α => C.card - 2)
        (fun _ _ => Nat.zero_le _)
        (show A ∈ B.filter (v ∈ ·) from Finset.mem_filter.mpr ⟨hA,hv⟩)
    omega
  have htDeg : ∀ v ∈ S, tripleDegree B v ≤ 1 := by
    intro v hv
    have hCap := hDeg v hv
    have hE := card_containing_add_tripleDegree hD h3 hv
    change designDegree B v + tripleDegree B v + 1 = S.card at hE
    omega
  have hDis : (triples B : Set (Finset α)).PairwiseDisjoint id := by
    intro A hA C hC hne
    apply Finset.disjoint_left.mpr
    intro v hvA hvC
    have hAB : A ∈ B := (Finset.mem_filter.mp (show A ∈ triples B from hA)).1
    have hvS := (hD.1 A hAB).1 hvA
    have hLt : 1 < tripleDegree B v := by
      exact Finset.one_lt_card.mpr ⟨A,Finset.mem_filter.mpr ⟨hA,hvA⟩,
        C,Finset.mem_filter.mpr ⟨hC,hvC⟩,hne⟩
    exact (Nat.not_lt_of_ge (htDeg v hvS)) hLt
  refine ⟨h3,hDis,total_card_of_triples hD h3,?_⟩
  have hSub : (triples B).biUnion id ⊆ S := by
    intro v hv
    obtain ⟨A,hA,hvA⟩ := Finset.mem_biUnion.mp hv
    exact (hD.1 A (Finset.mem_filter.mp hA).1).1 hvA
  have hUpper := Finset.card_le_card hSub
  have hCount := Finset.card_biUnion hDis
  have hSum : (∑ A ∈ triples B, (id A).card) = 3 * (triples B).card := by
    calc
      _ = ∑ _A ∈ triples B, 3 := by
        apply Finset.sum_congr rfl
        intro A hA
        exact (Finset.mem_filter.mp hA).2
      _ = _ := by simp [Finset.sum_const, Nat.mul_comm]
  rw [hCount,hSum] at hUpper
  exact hUpper

/-- Any source in a triple has degree exactly k−2 in the deficit-one
classification. The lower and upper counts are both checked separately. -/
theorem deficit_le_one_degree_of_mem_triple {S : Finset α} {B : Finset (Finset α)}
    {T : Finset α} {v : α} (hD : PairDesign S B)
    (hDeg : ∀ v ∈ S, S.card ≤ designDegree B v + 2)
    (hT : T ∈ triples B) (hv : v ∈ T) :
    designDegree B v + 2 = S.card := by
  have h3 := (deficit_le_one_triples_classification hD hDeg).1
  have hvS := (hD.1 T (Finset.mem_filter.mp hT).1).1 hv
  have hE := card_containing_add_tripleDegree hD h3 hvS
  change designDegree B v + tripleDegree B v + 1 = S.card at hE
  have hPos : 0 < tripleDegree B v :=
    Finset.card_pos.mpr ⟨T,Finset.mem_filter.mpr ⟨hT,hv⟩⟩
  have hMin := hDeg v hvS
  omega

#print axioms designDegree_add_incident_excess
#print axioms deficit_le_one_triples_classification
#print axioms deficit_le_one_degree_of_mem_triple
end FranklBlockIncidence
