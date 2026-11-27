import FranklTripleDegree

open scoped BigOperators
namespace FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

theorem distinct_blocks_inter_card_le_one {S : Finset α} {B : Finset (Finset α)} {A C : Finset α}
    (hD : PairDesign S B) (hA : A ∈ B) (hC : C ∈ B) (hne : A ≠ C) :
    (A ∩ C).card ≤ 1 := by
  by_contra! h
  obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp h
  obtain ⟨huA,huC⟩ := Finset.mem_inter.mp hu
  obtain ⟨hvA,hvC⟩ := Finset.mem_inter.mp hv
  obtain ⟨_,_,hU⟩ := hD.2 u ((hD.1 A hA).1 huA) v ((hD.1 A hA).1 hvA) huv
  exact hne ((hU A ⟨hA,huA,hvA⟩).trans (hU C ⟨hC,huC,hvC⟩).symm)

def linkTriples (B : Finset (Finset α)) (A : Finset α) : Finset (Finset α) :=
  ((triples B).erase A).filter (fun T => (A ∩ T).Nonempty)

def linkEdges (B : Finset (Finset α)) (A : Finset α) : Finset (Finset α) :=
  (linkTriples B A).image (fun T => T \ A)

theorem match_triple_degree_sum_to_links {S : Finset α} {B : Finset (Finset α)} {A : Finset α}
    (hD : PairDesign S B) (hA : A ∈ triples B) :
    (∑ v ∈ A, tripleDegree B v) = (linkTriples B A).card + 3 := by
  classical
  obtain ⟨hAB,hA3⟩ := Finset.mem_filter.mp hA
  have he : (∑ v ∈ A, tripleDegree B v) = ∑ T ∈ triples B, (A ∩ T).card := by
    calc
      (∑ v ∈ A, tripleDegree B v) = ∑ v ∈ A, ∑ T ∈ triples B, if v ∈ T then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        exact Finset.card_filter _ _
      _ = ∑ T ∈ triples B, ∑ v ∈ A, if v ∈ T then 1 else 0 := Finset.sum_comm
      _ = ∑ T ∈ triples B, (A ∩ T).card := by
        apply Finset.sum_congr rfl
        intro T _
        rw [← Finset.card_filter]
        congr 1
  have hsplit := Finset.sum_erase_add (triples B) (fun T => (A∩T).card) hA
  rw [Finset.inter_self,hA3] at hsplit
  have hCard : (∑ T ∈ (triples B).erase A, (A∩T).card) = (linkTriples B A).card := by
    rw [linkTriples,Finset.card_filter]
    apply Finset.sum_congr rfl
    intro T hT
    obtain ⟨hTA,hTT⟩ := Finset.mem_erase.mp hT
    have hb := (Finset.mem_filter.mp hTT).1
    have hl := distinct_blocks_inter_card_le_one hD hAB hb hTA.symm
    by_cases hn : (A∩T).Nonempty
    · have hp := Finset.card_pos.mpr hn
      rw [ite_eq_left hn]
      omega
    · have hz := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
      rw [ite_eq_right hn]
      exact hz
  rw [he,← hsplit,hCard]

theorem linkEdges_card_eq_linkTriples {S : Finset α} {B : Finset (Finset α)} {A : Finset α}
    (hD : PairDesign S B) (hA : A ∈ triples B) :
    (linkEdges B A).card = (linkTriples B A).card := by
  apply Finset.card_image_of_injOn
  intro T hT R hR he
  obtain ⟨hTe,hAn⟩ := Finset.mem_filter.mp hT
  obtain ⟨hRT,_⟩ := Finset.mem_filter.mp hR
  obtain ⟨hTA,hTT⟩ := Finset.mem_erase.mp hTe
  have hTB := (Finset.mem_filter.mp hTT).1
  have hRB := (Finset.mem_filter.mp (Finset.mem_erase.mp hRT).2).1
  have hT3 := (Finset.mem_filter.mp hTT).2
  have hInter := distinct_blocks_inter_card_le_one hD (Finset.mem_filter.mp hA).1 hTB hTA.symm
  have hIntPos := Finset.card_pos.mpr hAn
  have hD2 : (T \ A).card = 2 := by
    have h := Finset.card_sdiff_add_card_inter T A
    rw [Finset.inter_comm T A] at h
    omega
  obtain ⟨u,v,huv,hEq⟩ := Finset.card_eq_two.mp hD2
  have hu : u ∈ T \ A := hEq.symm ▸ Finset.mem_insert_self _ _
  have hv : v ∈ T \ A := hEq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  change T \ A = R \ A at he
  have hx := (Finset.mem_sdiff.mp hu).1
  have hy := (Finset.mem_sdiff.mp hv).1
  have huR := (Finset.mem_sdiff.mp (he ▸ hu)).1
  have hvR := (Finset.mem_sdiff.mp (he ▸ hv)).1
  obtain ⟨_,_,hU⟩ := hD.2 u ((hD.1 T hTB).1 hx) v ((hD.1 T hTB).1 hy) huv
  exact (hU T ⟨hTB,hx,hy⟩).trans (hU R ⟨hRB,huR,hvR⟩).symm

theorem linkEdges_card_ge_seven {S : Finset α} {B : Finset (Finset α)} {A : Finset α}
    (hD : PairDesign S B) (hA : A ∈ triples B) (hh : 10 ≤ ∑ v ∈ A,tripleDegree B v) :
    7 ≤ (linkEdges B A).card := by
  rw [linkEdges_card_eq_linkTriples hD hA,match_triple_degree_sum_to_links hD hA] at *
  omega

theorem link_edge_data {S : Finset α} {B : Finset (Finset α)} {A e : Finset α}
    (hD : PairDesign S B) (hA : A ∈ triples B) (he : e ∈ linkEdges B A) :
    e ⊆ S \ A ∧ e.card = 2 ∧ ∃ T ∈ triples B, ∃ v ∈ A ∩ T, e ⊆ T := by
  obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hTe,hAn⟩ := Finset.mem_filter.mp hT
  obtain ⟨hTA,hTT⟩ := Finset.mem_erase.mp hTe
  have hTB := (Finset.mem_filter.mp hTT).1
  have hT3 := (Finset.mem_filter.mp hTT).2
  have hInter := distinct_blocks_inter_card_le_one hD (Finset.mem_filter.mp hA).1 hTB hTA.symm
  have hIntPos := Finset.card_pos.mpr hAn
  have hD2 : (T \ A).card = 2 := by
    have h := Finset.card_sdiff_add_card_inter T A
    rw [Finset.inter_comm T A] at h
    omega
  obtain ⟨v,hv⟩ := hAn
  refine ⟨?_,hD2,T,hTT,v,hv,Finset.sdiff_subset⟩
  intro x hx
  obtain ⟨hxT,hxA⟩ := Finset.mem_sdiff.mp hx
  exact Finset.mem_sdiff.mpr ⟨(hD.1 T hTB).1 hxT,hxA⟩

#print axioms linkEdges_card_ge_seven
#print axioms link_edge_data

end FranklBlockIncidence
