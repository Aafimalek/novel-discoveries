import FranklBlockIncidence
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases

open scoped BigOperators
namespace FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

def triples (B : Finset (Finset α)) : Finset (Finset α) := B.filter (fun A => A.card = 3)

def tripleDegree (B : Finset (Finset α)) (v : α) : ℕ :=
  ((triples B).filter (v ∈ ·)).card

theorem total_card_of_triples {S : Finset α} {B : Finset (Finset α)}
    (hD : PairDesign S B) (h3 : ∀ A ∈ B, A.card ≤ 3) :
    B.card + 2 * (triples B).card = S.card.choose 2 := by
  classical
  have hU : B.biUnion (fun A => A.powersetCard 2) = S.powersetCard 2 := by
    ext R
    constructor
    · intro hR
      obtain ⟨A,hA,hRA⟩ := Finset.mem_biUnion.mp hR
      obtain ⟨hs,hc⟩ := Finset.mem_powersetCard.mp hRA
      exact Finset.mem_powersetCard.mpr ⟨hs.trans (hD.1 A hA).1,hc⟩
    · intro hR
      obtain ⟨hs,hc⟩ := Finset.mem_powersetCard.mp hR
      obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hc
      have ha : a ∈ S := hs (by simp)
      have hb : b ∈ S := hs (by simp)
      obtain ⟨A,⟨hA,haA,hbA⟩,_⟩ := hD.2 a ha b hb hab
      exact Finset.mem_biUnion.mpr ⟨A,hA,Finset.mem_powersetCard.mpr
        ⟨Finset.insert_subset_iff.mpr ⟨haA,Finset.singleton_subset_iff.mpr hbA⟩,by simp [hab]⟩⟩
  have hDisj : (B : Set (Finset α)).PairwiseDisjoint (fun A => A.powersetCard 2) := by
    intro A hA C hC hne
    apply Finset.disjoint_left.mpr
    intro R hRA hRC
    obtain ⟨hs,hc⟩ := Finset.mem_powersetCard.mp hRA
    obtain ⟨hs',_⟩ := Finset.mem_powersetCard.mp hRC
    obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hc
    have ha : a ∈ A := hs (by simp)
    have hb : b ∈ A := hs (by simp)
    have ha' : a ∈ C := hs' (by simp)
    have hb' : b ∈ C := hs' (by simp)
    obtain ⟨_,_,hUnique⟩ := hD.2 a ((hD.1 A hA).1 ha) b ((hD.1 A hA).1 hb) hab
    exact hne ((hUnique _ ⟨hA,ha,hb⟩).trans (hUnique _ ⟨hC,ha',hb'⟩).symm)
  have he := Finset.card_biUnion hDisj
  rw [hU,Finset.card_powersetCard] at he
  have h2 : (∑ A ∈ B, (A.powersetCard 2).card) =
      ∑ A ∈ B, (1 + 2 * if A.card = 3 then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro A hA
    rw [Finset.card_powersetCard]
    have hlo := (hD.1 A hA).2
    have hhi := h3 A hA
    by_cases ha : A.card = 3
    · rw [ha]
      decide
    · have ha2 : A.card = 2 := by omega
      rw [ha2]
      decide
  rw [h2,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.card_filter] at he
  simpa [triples] using he.symm

theorem card_containing_add_tripleDegree {S : Finset α} {B : Finset (Finset α)} {v : α}
    (hD : PairDesign S B) (h3 : ∀ A ∈ B, A.card ≤ 3) (hv : v ∈ S) :
    (B.filter (v ∈ ·)).card + tripleDegree B v + 1 = S.card := by
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
  have he := Finset.card_biUnion hDisj
  rw [hU] at he
  have h2 : (∑ A ∈ D, (A.erase v).card) = ∑ A ∈ D, (1 + if A.card = 3 then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro A hA
    obtain ⟨hAB,hvA⟩ := Finset.mem_filter.mp hA
    have hh := Finset.card_erase_add_one hvA
    have hlo := (hD.1 A hAB).2
    have hhi := h3 A hAB
    split <;> omega
  rw [h2,Finset.sum_add_distrib,← Finset.card_filter] at he
  have hf : D.filter (fun A => A.card = 3) = (triples B).filter (v ∈ ·) := by
    ext A
    simp only [D,triples,Finset.mem_filter]
    tauto
  rw [hf] at he
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at he
  change (S.erase v).card = D.card + tripleDegree B v at he
  exact he ▸ (show (S.erase v).card + 1 = S.card from Finset.card_erase_add_one hv)

theorem away_card_exact_of_triples {S : Finset α} {B : Finset (Finset α)} {p q : α}
    (hD : PairDesign S B) (h3 : ∀ A ∈ B, A.card ≤ 3)
    (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    (away B p q).card + 2*(triples B).card + 2*S.card =
      S.card.choose 2 + 3 + tripleDegree B p + tripleDegree B q := by
  classical
  let P := B.filter (p ∈ ·)
  let Q := B.filter (q ∈ ·)
  obtain ⟨A,⟨hAB,hpA,hqA⟩,hu⟩ := hD.2 p hp q hq hpq
  have hi : P ∩ Q = {A} := by
    ext C
    constructor
    · intro hc
      obtain ⟨hP,hQ⟩ := Finset.mem_inter.mp hc
      exact Finset.mem_singleton.mpr (hu C ⟨(Finset.mem_filter.mp hP).1,
        (Finset.mem_filter.mp hP).2,(Finset.mem_filter.mp hQ).2⟩)
    · intro hc
      have he := Finset.mem_singleton.mp hc
      subst C
      exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨hAB,hpA⟩,Finset.mem_filter.mpr ⟨hAB,hqA⟩⟩
  have hA : away B p q = B \ (P ∪ Q) := by
    ext C
    simp only [mem_away,Finset.mem_sdiff,Finset.mem_union,P,Q,Finset.mem_filter]
    tauto
  have hs : P ∪ Q ⊆ B := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hW := Finset.card_sdiff_add_card_eq_card hs
  rw [← hA] at hW
  have hU := Finset.card_union_add_card_inter P Q
  rw [hi,Finset.card_singleton] at hU
  have hP := card_containing_add_tripleDegree hD h3 hp
  have hQ := card_containing_add_tripleDegree hD h3 hq
  change P.card + tripleDegree B p + 1 = S.card at hP
  change Q.card + tripleDegree B q + 1 = S.card at hQ
  have hT := total_card_of_triples hD h3
  omega

theorem sum_tripleDegree {S : Finset α} {B : Finset (Finset α)}
    (hD : PairDesign S B) :
    (∑ v ∈ S, tripleDegree B v) = 3*(triples B).card := by
  classical
  let T := triples B
  calc
    (∑ v ∈ S, tripleDegree B v) = ∑ v ∈ S, ∑ A ∈ T, if v ∈ A then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      exact Finset.card_filter _ _
    _ = ∑ A ∈ T, ∑ v ∈ S, if v ∈ A then 1 else 0 := Finset.sum_comm
    _ = ∑ A ∈ T, 3 := by
      apply Finset.sum_congr rfl
      intro A hA
      obtain ⟨hAB,hc⟩ := Finset.mem_filter.mp hA
      have he : S.filter (· ∈ A) = A := by
        ext x
        exact ⟨fun h => (Finset.mem_filter.mp h).2,fun h => Finset.mem_filter.mpr ⟨(hD.1 A hAB).1 h,h⟩⟩
      rw [← Finset.card_filter,he,hc]
    _ = 3*T.card := by simp [Nat.mul_comm]

theorem sum_sq_tripleDegree {S : Finset α} {B : Finset (Finset α)}
    (hD : PairDesign S B) :
    (∑ v ∈ S, (tripleDegree B v)^2) = ∑ A ∈ triples B, ∑ v ∈ A, tripleDegree B v := by
  classical
  let T := triples B
  calc
    (∑ v ∈ S, (tripleDegree B v)^2) =
        ∑ v ∈ S, ∑ A ∈ T, if v ∈ A then tripleDegree B v else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,pow_two]
      rfl
    _ = ∑ A ∈ T, ∑ v ∈ S, if v ∈ A then tripleDegree B v else 0 := Finset.sum_comm
    _ = ∑ A ∈ triples B, ∑ v ∈ A, tripleDegree B v := by
      apply Finset.sum_congr rfl
      intro A hA
      have hAB := (Finset.mem_filter.mp hA).1
      have he : S.filter (· ∈ A) = A := by
        ext x
        exact ⟨fun h => (Finset.mem_filter.mp h).2,fun h => Finset.mem_filter.mpr ⟨(hD.1 A hAB).1 h,h⟩⟩
      rw [← Finset.sum_filter,he]

/-- On eleven points, thirteen or more triples force a triple with
degree sum at least ten. -/
theorem exists_high_triple_degree_sum_eleven {S : Finset α} {B : Finset (Finset α)}
    (hD : PairDesign S B) (h3 : ∀ A ∈ B, A.card ≤ 3)
    (hk : S.card = 11) (ht : 13 ≤ (triples B).card) :
    ∃ A ∈ triples B, 10 ≤ ∑ v ∈ A, tripleDegree B v := by
  classical
  by_contra hn
  have hdv : ∀ v ∈ S, tripleDegree B v ≤ 5 := by
    intro v hv
    have h := card_containing_add_tripleDegree hD h3 hv
    have hsub : (triples B).filter (v ∈ ·) ⊆ B.filter (v ∈ ·) :=
      fun A hA => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).1,
        (Finset.mem_filter.mp hA).2⟩
    have hc := Finset.card_le_card hsub
    change tripleDegree B v ≤ _ at hc
    omega
  have hnum (d : ℕ) (hd : d ≤ 5) : 7*d ≤ d^2 + 12 := by interval_cases d <;> decide
  have h := Finset.sum_le_sum (s := S) (fun v hv => hnum (tripleDegree B v) (hdv v hv))
  rw [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,hk,sum_tripleDegree hD] at h
  have h' : (∑ A ∈ triples B, ∑ v ∈ A, tripleDegree B v) ≤ ∑ _A ∈ triples B, 9 := by
    apply Finset.sum_le_sum
    intro A hA
    by_contra! ha
    exact hn ⟨A,hA,by omega⟩
  rw [← sum_sq_tripleDegree hD,Finset.sum_const,nsmul_eq_mul] at h'
  change (∑ v ∈ S, (tripleDegree B v)^2) ≤ (triples B).card * 9 at h'
  omega

#print axioms away_card_exact_of_triples
#print axioms exists_high_triple_degree_sum_eleven

end FranklBlockIncidence
