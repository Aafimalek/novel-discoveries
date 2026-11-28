import FranklPairDesignDeficitOne
import FranklDisjointTriplePairLinks

/- Checked by pinned ordinary Lean with warnings as errors. -/
namespace FranklForcingFiber
open FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

/-- Taking one source from each of two different triples in the
deficit-at-most-one classification automatically supplies all inputs
of the checked disjoint-triple quotient theorem. -/
theorem exact_four_deficit_le_one_two_triple_anchors
    {G : Finset (Finset α)} {P Q : Finset α} {p q : α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hI : (isolated G).card = 4)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 2)
    (hP : P ∈ triples (starBlocks G)) (hQ : Q ∈ triples (starBlocks G))
    (hPQ : P ≠ Q) (hp : p ∈ P) (hq : q ∈ Q) :
    isolated G ⊆ starPairMax G p q ∧
      ∀ x ∈ isolated G, starPairMax G p q \ {x} ∈ avoidBoth G (starLeaf G p) (starLeaf G q) := by
  classical
  let B := starBlocks G
  have hD := starBlocks_pairDesign hG hm
  obtain ⟨h3,hDisjoint,hN,h3t⟩ := deficit_le_one_triples_classification hD hDeg
  obtain ⟨hPB,hPc⟩ := Finset.mem_filter.mp hP
  obtain ⟨hQB,hQc⟩ := Finset.mem_filter.mp hQ
  have hpS := (hD.1 P hPB).1 hp
  have hqS := (hD.1 Q hQB).1 hq
  have hDis : Disjoint P Q := hDisjoint hP hQ hPQ
  have hpq : p ≠ q := fun e => (Finset.disjoint_left.mp hDis) hp (e.symm ▸ hq)
  have hdp := deficit_le_one_degree_of_mem_triple hD hDeg hP hp
  have hdq := deficit_le_one_degree_of_mem_triple hD hDeg hQ hq
  let A := omittedStars G (starPairMax G p q)
  have hAB : A ∈ B := Finset.mem_image.mpr ⟨starPairMax G p q,starPairMax_mem hpS hqS hpq,rfl⟩
  obtain ⟨hpA,hqA⟩ := omittedBlock_members hpS hqS
  have hA2 : A.card = 2 := by
    by_contra hn
    have hLo := (hD.1 A hAB).2
    have hHi := h3 A hAB
    have hc : A.card = 3 := by omega
    have hAT : A ∈ triples B := Finset.mem_filter.mpr ⟨hAB,hc⟩
    have hAP : A = P := by
      by_contra hne
      have hh : Disjoint A P := hDisjoint hAT hP hne
      exact (Finset.disjoint_left.mp hh) hpA hp
    have hqP : q ∈ P := by
      rw [← hAP]
      exact hqA
    exact (Finset.disjoint_left.mp hDis) hqP hq
  have hA : A = {p,q} := omittedStars_eq_pair_of_card_two hpS hqS hpq hA2
  have hPE : (P.erase p).card = 2 := by
    have := Finset.card_erase_add_one hp
    omega
  have hQE : (Q.erase q).card = 2 := by
    have := Finset.card_erase_add_one hq
    omega
  obtain ⟨u,v,_,hPpair⟩ := Finset.card_eq_two.mp hPE
  obtain ⟨w,z,_,hQpair⟩ := Finset.card_eq_two.mp hQE
  have hPshape : ({p,u,v} : Finset α) = P := by
    rw [← hPpair,Finset.insert_erase hp]
  have hQshape : ({q,w,z} : Finset α) = Q := by
    rw [← hQpair,Finset.insert_erase hq]
  exact exact_four_disjointTriple_anchors_full_isolate_omissions hG hm hI hpS hqS hpq hdp hdq hA
    (hPshape.symm ▸ hPB) (hQshape.symm ▸ hQB) (hPshape.symm ▸ hPc) (hQshape.symm ▸ hQc)
    (by rw [hPshape,hQshape]; exact hDis) hN h3t

#print axioms exact_four_deficit_le_one_two_triple_anchors
end FranklForcingFiber
