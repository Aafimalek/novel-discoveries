import FranklQuadFourDrops

/- Checked by pinned ordinary Lean with warnings as errors. -/
open scoped BigOperators
namespace FranklForcingFiber
open FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

/-- A quad forces every exterior source to have deficit at most one.
The quad is unique, the triples are disjoint, and they use exterior
sources only. -/
theorem quad_forces_exterior_deficit_le_one_and_triple_budget
    {G : Finset (Finset α)} {Q : Finset α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hI : (isolated G).card = 4)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 3)
    (hQ : Q ∈ quads (starBlocks G)) :
    (∀ q ∈ sources G, q ∉ Q → (sources G).card ≤ designDegree (starBlocks G) q + 2) ∧
    quads (starBlocks G) = {Q} ∧
    3 * (triples (starBlocks G)).card + 4 ≤ (sources G).card := by
  classical
  let B := starBlocks G
  have hD := starBlocks_pairDesign hG hm
  have h4 := (deficit_le_two_local_classification hD hDeg).1
  obtain ⟨hQB,hQc⟩ := Finset.mem_filter.mp hQ
  have hQS := (hD.1 Q hQB).1
  have hDis := (quad_disjoint_nonpair_and_exact_deficit hD hDeg hQ).1
  obtain ⟨p,hpQ⟩ := Finset.card_pos.mp (show 0 < Q.card by omega)
  have hOut : ∀ q ∈ sources G, q ∉ Q → (sources G).card ≤ designDegree B q + 2 := by
    intro q hq hqN
    by_contra hn
    have hCap := hDeg q hq
    have hE : designDegree B q + 3 = (sources G).card := by
      change (sources G).card ≤ designDegree B q + 3 at hCap
      omega
    exact quad_and_outside_deficitTwo_impossible hG hm hI hDeg hQ hpQ hq hqN hE
  have hu : quads B = {Q} := by
    ext R
    constructor
    · intro hR
      apply Finset.mem_singleton.mpr
      by_contra hRQ
      obtain ⟨hRB,hRc⟩ := Finset.mem_filter.mp hR
      have hQR := hDis R hRB (by omega) hRQ
      obtain ⟨r,hr⟩ := Finset.card_pos.mp (show 0 < R.card by omega)
      have hrS := (hD.1 R hRB).1 hr
      have hrN : r ∉ Q := fun h => (Finset.disjoint_left.mp hQR) h hr
      have hDo := hOut r hrS hrN
      have hDq := (quad_disjoint_nonpair_and_exact_deficit hD hDeg hR).2 r hr
      change designDegree B r + 3 = (sources G).card at hDq
      omega
    · intro hR
      have he : R = Q := Finset.mem_singleton.mp hR
      subst R
      exact hQ
  have hTripOut (T : Finset α) (hT : T ∈ triples B) : T ⊆ sources G \ Q := by
    obtain ⟨hTB,hTc⟩ := Finset.mem_filter.mp hT
    have hNe : T ≠ Q := by
      intro he
      rw [he] at hTc
      omega
    have hDT := hDis T hTB hTc.ge hNe
    exact fun _ hx => Finset.mem_sdiff.mpr ⟨(hD.1 T hTB).1 hx,
      fun hn => (Finset.disjoint_left.mp hDT) hn hx⟩
  have hTD : (triples B : Set (Finset α)).PairwiseDisjoint id := by
    intro T hT U hU hne
    apply Finset.disjoint_left.mpr
    intro r hrT hrU
    obtain ⟨hrS,hrQ⟩ := Finset.mem_sdiff.mp (hTripOut T hT hrT)
    have hDegO := hOut r hrS hrQ
    have hDegE := designDegree_add_triple_quad hD h4 hrS
    change designDegree B r + tripleDegree B r + 2 * quadDegree B r + 1 =
      (sources G).card at hDegE
    have ht : 1 < tripleDegree B r := Finset.one_lt_card.mpr
      ⟨T,Finset.mem_filter.mpr ⟨hT,hrT⟩,U,Finset.mem_filter.mpr ⟨hU,hrU⟩,hne⟩
    omega
  have hSup : (triples B).biUnion id ⊆ sources G \ Q := by
    intro r hr
    obtain ⟨T,hT,hrT⟩ := Finset.mem_biUnion.mp hr
    exact hTripOut T hT hrT
  have hLift := Finset.card_le_card hSup
  have hSum : (∑ T ∈ triples B, (id T).card) = 3 * (triples B).card := by
    calc
      _ = ∑ _T ∈ triples B, 3 := Finset.sum_congr rfl (fun _ hT => (Finset.mem_filter.mp hT).2)
      _ = _ := by simp [Nat.mul_comm]
  rw [Finset.card_biUnion hTD,hSum] at hLift
  have hCount := Finset.card_sdiff_add_card_eq_card hQS
  have hBudget : 3 * (triples B).card + 4 ≤ (sources G).card := by omega
  exact ⟨hOut,hu,hBudget⟩

/-- Quad and exterior triple anchors give independent mate groups
of sizes three and two, hence three simultaneous actual deletions. -/
theorem quad_and_triple_three_drops {G : Finset (Finset α)} {Q T : Finset α}
    {p q : α} (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 3)
    (hQ : Q ∈ quads (starBlocks G)) (hT : T ∈ triples (starBlocks G))
    (hp : p ∈ Q) (hq : q ∈ T) :
    omittedStars G (starPairMax G p q) = {p,q} ∧
    ∃ Drop, TransitivelyLinkedDeletion G (omittedStars G (starPairMax G p q)) Drop ∧ Drop.card = 3 := by
  classical
  let B := starBlocks G
  let A := omittedStars G (starPairMax G p q)
  have hD := starBlocks_pairDesign hG hm
  obtain ⟨hQB,hQc⟩ := Finset.mem_filter.mp hQ
  obtain ⟨hTB,hTc⟩ := Finset.mem_filter.mp hT
  have hNe : T ≠ Q := by intro he; rw [he] at hTc; omega
  have hDis := (quad_disjoint_nonpair_and_exact_deficit hD hDeg hQ).1 T hTB (by omega) hNe
  have hqQ : q ∉ Q := fun h => (Finset.disjoint_left.mp hDis) h hq
  have hpT : p ∉ T := (Finset.disjoint_left.mp hDis) hp
  have hqS := (hD.1 T hTB).1 hq
  have hA : A = {p,q} := ordinary_anchor_block_of_quad_and_outside hG hm hDeg hQ hp hqS hqQ
  have mate {U : Finset α} {u v : α} (hU : U ∈ B) (hu : u ∈ U) (hv : v ∉ U)
      (he : A = {u,v}) : BlockLinkClique G A (U.erase u) := by
    apply blockLinkClique_of_incident_block hG hm hU (r := u) (by rw [he]; simp) hu
      (Finset.erase_subset _ _)
    rw [he]
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨hn,hxu⟩ := Finset.mem_erase.mp hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx'
    exact hx'.elim hn (fun e => hv (e ▸ hxu))
  have hQE := mate hQB hp hqQ hA
  have hTE := mate hTB hq hpT (hA.trans (Finset.pair_comm p q))
  have hReg : Disjoint (Q.erase p) (T.erase q) := by
    exact Finset.disjoint_left.mpr (fun _ hx hy =>
      (Finset.disjoint_left.mp hDis) (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy))
  have hc1 := Finset.card_erase_add_one hp
  have hc2 := Finset.card_erase_add_one hq
  have hQNe : (Q.erase p).Nonempty := Finset.card_pos.mp (by omega)
  have hTNe : (T.erase q).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨Drop,hDrop,hc⟩ := transitiveDeletion_of_two_link_cliques hQE hTE hQNe hTNe hReg
  exact ⟨hA,Drop,hDrop,by omega⟩

/-- No quad remains in an actual four-isolate family whose maximum
source deficit is at most two. Triple-only designs are not excluded. -/
theorem exact_four_deficit_le_two_no_quads {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hI : (isolated G).card = 4)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 3) :
    quads (starBlocks G) = ∅ := by
  classical
  by_contra hn
  obtain ⟨Q,hQ⟩ := Finset.nonempty_iff_ne_empty.mpr hn
  let B := starBlocks G
  let k := (sources G).card
  obtain ⟨hExt,hUnique,hTripleBudget⟩ :=
    quad_forces_exterior_deficit_le_one_and_triple_budget hG hm hI hDeg hQ
  by_cases he : triples B = ∅
  · exact exact_four_deficit_le_two_not_sole_quad hG hm hI hDeg hUnique he
  obtain ⟨T,hT⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hD := starBlocks_pairDesign hG hm
  have h4 := (deficit_le_two_local_classification hD hDeg).1
  obtain ⟨hQB,hQc⟩ := Finset.mem_filter.mp hQ
  obtain ⟨hTB,hTc⟩ := Finset.mem_filter.mp hT
  have hTQ : T ≠ Q := by intro h; rw [h] at hTc; omega
  have hQdata := quad_disjoint_nonpair_and_exact_deficit hD hDeg hQ
  have hQT := hQdata.1 T hTB (by omega) hTQ
  obtain ⟨p,hpQ⟩ := Finset.card_pos.mp (show 0 < Q.card by omega)
  obtain ⟨q,hqT⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  have hp := (hD.1 Q hQB).1 hpQ
  have hq := (hD.1 T hTB).1 hqT
  have hqQ : q ∉ Q := fun h => (Finset.disjoint_left.mp hQT) h hqT
  have hpq : p ≠ q := fun e => hqQ (e ▸ hpQ)
  have hdp := hQdata.2 p hpQ
  have hdq : designDegree B q + 2 = k := by
    have hLoc := designDegree_add_triple_quad hD h4 hq
    change designDegree B q + tripleDegree B q + 2 * quadDegree B q + 1 = k at hLoc
    have htq : 0 < tripleDegree B q := Finset.card_pos.mpr ⟨T,Finset.mem_filter.mpr ⟨hT,hqT⟩⟩
    have hqE := hExt q hq hqQ
    change k ≤ designDegree B q + 2 at hqE
    omega
  obtain ⟨hA,Drop,hDrop,hDrop3⟩ := quad_and_triple_three_drops hG hm hDeg hQ hT hpQ hqT
  let A := omittedStars G (starPairMax G p q)
  let V := ((sources G \ A) \ Drop) ∪ isolated G
  have hAs : A ⊆ sources G := fun _ h => (mem_omittedStars.mp h).1
  have hAc : A.card = 2 := by change A = {p,q} at hA; rw [hA]; simp [hpq]
  have hNom := transitive_nominal_quotient_card hAs hDrop
  change V.card + Drop.card + A.card = k + (isolated G).card at hNom
  rw [hDrop3,hAc,hI] at hNom
  have hV : V.card ≤ k - 1 := by omega
  have hUp := transitive_linked_nominal_Sauer_cap hG hm hp hq hpq hDrop hV
  have hLo := pair_lower_with_explicit_deficits (dp := 2) (dq := 1)
    hG hm hI hp hq hpq hdp hdq (∅ : Finset (α × Finset α)) (by simp)
  simp only [Finset.card_empty,Nat.add_zero] at hLo
  have hLoss := (deficit_le_two_global_budgets hD hDeg).1
  rw [hUnique,Finset.card_singleton] at hLoss
  change B.card + 2 * (triples B).card + 5 * 1 = k.choose 2 at hLoss
  change 3 * (triples B).card + 4 ≤ k at hTripleBudget
  change B.card + k + 6 + 2 + 1 ≤ _ at hLo
  change _ ≤ 1 + (k - 1) + (k - 1).choose 2 at hUp
  have hPas : k.choose 2 = (k - 1) + (k - 1).choose 2 := by
    have hn : k - 1 + 1 = k := by omega
    have hh := Nat.choose_succ_succ' (k - 1) 1
    rw [hn] at hh
    simpa using hh
  omega

#print axioms quad_forces_exterior_deficit_le_one_and_triple_budget
#print axioms quad_and_triple_three_drops
#print axioms exact_four_deficit_le_two_no_quads
end FranklForcingFiber
