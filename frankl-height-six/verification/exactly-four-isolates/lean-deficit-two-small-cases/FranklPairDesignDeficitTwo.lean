import FranklPairDesignDeficitOne

/- Checked by pinned ordinary Lean with warnings as errors. -/
open scoped BigOperators
namespace FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

def quads (B : Finset (Finset α)) : Finset (Finset α) :=
  B.filter (fun A => A.card = 4)

def quadDegree (B : Finset (Finset α)) (v : α) : ℕ :=
  ((quads B).filter (v ∈ ·)).card

theorem designDegree_add_triple_quad {S : Finset α} {B : Finset (Finset α)} {v : α}
    (hD : PairDesign S B) (h4 : ∀ A ∈ B, A.card ≤ 4) (hv : v ∈ S) :
    designDegree B v + tripleDegree B v + 2 * quadDegree B v + 1 = S.card := by
  classical
  let C := B.filter (v ∈ ·)
  have he := designDegree_add_incident_excess hD hv
  have hs : (∑ A ∈ C, (A.card - 2)) =
      (∑ A ∈ C, if A.card = 3 then 1 else 0) +
      2 * (∑ A ∈ C, if A.card = 4 then 1 else 0) := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro A hA
    have hAB := (Finset.mem_filter.mp hA).1
    have hlo := (hD.1 A hAB).2
    have hhi := h4 A hAB
    split <;> split <;> omega
  have h3s : C.filter (fun A => A.card = 3) = (triples B).filter (v ∈ ·) := by
    ext A
    simp only [C,triples,Finset.mem_filter]
    tauto
  have h4s : C.filter (fun A => A.card = 4) = (quads B).filter (v ∈ ·) := by
    ext A
    simp only [C,quads,Finset.mem_filter]
    tauto
  rw [← Finset.card_filter,← Finset.card_filter,h3s,h4s] at hs
  change (∑ A ∈ C, (A.card - 2)) = tripleDegree B v + 2 * quadDegree B v at hs
  have he' : designDegree B v + (∑ A ∈ C, (A.card - 2)) + 1 = S.card := he
  omega

/-- Deficit at most two forces blocks of size at most four, with
each vertex in at most two triples or one quad, never both. -/
theorem deficit_le_two_local_classification {S : Finset α} {B : Finset (Finset α)}
    (hD : PairDesign S B)
    (hDeg : ∀ v ∈ S, S.card ≤ designDegree B v + 3) :
    (∀ A ∈ B, A.card ≤ 4) ∧
    ∀ v ∈ S, tripleDegree B v + 2 * quadDegree B v ≤ 2 := by
  classical
  have h4 : ∀ A ∈ B, A.card ≤ 4 := by
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
  refine ⟨h4,?_⟩
  intro v hv
  have hCap := hDeg v hv
  have hE := designDegree_add_triple_quad hD h4 hv
  omega

/-- A four-block cannot meet any other non-pair block. Every one of
its vertices has deficit exactly two. -/
theorem quad_disjoint_nonpair_and_exact_deficit {S : Finset α} {B : Finset (Finset α)}
    {Q : Finset α} (hD : PairDesign S B)
    (hDeg : ∀ v ∈ S, S.card ≤ designDegree B v + 3)
    (hQ : Q ∈ quads B) :
    (∀ A ∈ B, 3 ≤ A.card → A ≠ Q → Disjoint Q A) ∧
    ∀ v ∈ Q, designDegree B v + 3 = S.card := by
  classical
  obtain ⟨h4,hLocal⟩ := deficit_le_two_local_classification hD hDeg
  have hQB := (Finset.mem_filter.mp hQ).1
  have hQsub := (hD.1 Q hQB).1
  have hOne (v : α) (hv : v ∈ Q) : 0 < quadDegree B v :=
    Finset.card_pos.mpr ⟨Q,Finset.mem_filter.mpr ⟨hQ,hv⟩⟩
  constructor
  · intro A hA hAc hAQ
    apply Finset.disjoint_left.mpr
    intro v hvQ hvA
    have hCap := hLocal v (hQsub hvQ)
    have hPos := hOne v hvQ
    by_cases h3 : A.card = 3
    · have ht : 0 < tripleDegree B v := Finset.card_pos.mpr
        ⟨A,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hA,h3⟩,hvA⟩⟩
      omega
    · have hA4 := h4 A hA
      have he : A.card = 4 := by omega
      have hAA : A ∈ quads B := Finset.mem_filter.mpr ⟨hA,he⟩
      have hTwo : 1 < quadDegree B v := Finset.one_lt_card.mpr
        ⟨Q,Finset.mem_filter.mpr ⟨hQ,hvQ⟩,A,Finset.mem_filter.mpr ⟨hAA,hvA⟩,hAQ.symm⟩
      omega
  · intro v hv
    have hCap := hLocal v (hQsub hv)
    have hPos := hOne v hv
    have hE := designDegree_add_triple_quad hD h4 (hQsub hv)
    omega

theorem sum_quadDegree {S : Finset α} {B : Finset (Finset α)}
    (hD : PairDesign S B) :
    (∑ v ∈ S, quadDegree B v) = 4 * (quads B).card := by
  classical
  let C := quads B
  calc
    (∑ v ∈ S, quadDegree B v) = ∑ v ∈ S, ∑ A ∈ C, if v ∈ A then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      exact Finset.card_filter _ _
    _ = ∑ A ∈ C, ∑ v ∈ S, if v ∈ A then 1 else 0 := Finset.sum_comm
    _ = ∑ A ∈ C, 4 := by
      apply Finset.sum_congr rfl
      intro A hA
      obtain ⟨hAB,hc⟩ := Finset.mem_filter.mp hA
      have he : S.filter (· ∈ A) = A := by
        ext x
        exact ⟨fun h => (Finset.mem_filter.mp h).2,fun h =>
          Finset.mem_filter.mpr ⟨(hD.1 A hAB).1 h,h⟩⟩
      rw [← Finset.card_filter,he,hc]
    _ = _ := by simp [C, Nat.mul_comm]

theorem deficit_le_two_global_budgets {S : Finset α} {B : Finset (Finset α)}
    (hD : PairDesign S B)
    (hDeg : ∀ v ∈ S, S.card ≤ designDegree B v + 3) :
    B.card + 2 * (triples B).card + 5 * (quads B).card = S.card.choose 2 ∧
    3 * (triples B).card + 8 * (quads B).card ≤ 2 * S.card ∧
    3 * (2 * (triples B).card + 5 * (quads B).card) ≤ 4 * S.card := by
  classical
  obtain ⟨h4,hLocal⟩ := deficit_le_two_local_classification hD hDeg
  have hQ := pair_design_sum_choose_eq hD
  have hSum : (∑ A ∈ B, A.card.choose 2) =
      (∑ _A ∈ B, 1) + 2 * (∑ A ∈ B, if A.card = 3 then 1 else 0) +
      5 * (∑ A ∈ B, if A.card = 4 then 1 else 0) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro A hA
    have hlo := (hD.1 A hA).2
    have hhi := h4 A hA
    by_cases h3 : A.card = 3
    · rw [h3]
      decide
    · by_cases hA4 : A.card = 4
      · rw [hA4]
        decide
      · have he : A.card = 2 := by omega
        rw [he]
        decide
  rw [← Finset.card_eq_sum_ones,← Finset.card_filter,← Finset.card_filter] at hSum
  change (∑ A ∈ B, A.card.choose 2) = B.card + 2 * (triples B).card + 5 * (quads B).card at hSum
  have hGlobal : (∑ v ∈ S, (tripleDegree B v + 2 * quadDegree B v)) ≤ ∑ _v ∈ S, 2 :=
    Finset.sum_le_sum hLocal
  rw [Finset.sum_add_distrib,← Finset.mul_sum,sum_tripleDegree hD,sum_quadDegree hD] at hGlobal
  have hCard : (∑ _v ∈ S, (2 : ℕ)) = 2 * S.card := by simp [Nat.mul_comm]
  rw [hCard] at hGlobal
  exact ⟨hSum.symm.trans hQ,by omega,by omega⟩

#print axioms designDegree_add_triple_quad
#print axioms deficit_le_two_local_classification
#print axioms quad_disjoint_nonpair_and_exact_deficit
#print axioms deficit_le_two_global_budgets
end FranklBlockIncidence
