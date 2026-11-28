import FranklLinkedPairQuotient
import FranklAtLeastThreeIsolates

/- Checked by ordinary pinned Lean with warnings treated as errors. -/
namespace FranklForcingFiber
open FranklBlockIncidence FranklFinsetTwinQuotient
variable {α : Type*} [DecidableEq α]

theorem pair_lower_with_explicit_deficits {G : Finset (Finset α)} {p q : α}
    {dp dq : ℕ} (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hI : (isolated G).card = 4) (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hdp : designDegree (starBlocks G) p + dp + 1 = (sources G).card)
    (hdq : designDegree (starBlocks G) q + dq + 1 = (sources G).card)
    (K : Finset (α × Finset α))
    (hK : ∀ z ∈ K, z.1 ∈ sources G ∧ z.1 ≠ p ∧ z.1 ≠ q ∧
      z.2 ⊆ isolated G ∧ z.2.Nonempty ∧ mixedStarOmission G z.1 z.2 ∈ G) :
    (starBlocks G).card + (sources G).card + 6 + dp + dq + K.card ≤
      (avoidBoth G (starLeaf G p) (starLeaf G q)).card := by
  have hk : 2 ≤ (sources G).card := Finset.one_lt_card.mpr ⟨p,hp,q,hq,hpq⟩
  have hn := exact_four_unary_ground_card hG hm hI hk
  have hAway := away_and_two_designDegrees (starBlocks_pairDesign hG hm) hp hq hpq
  have hBase := leaf_pair_count_with_blocks_and_mixed hG hm hp hq hpq K hK
  omega

theorem nominal_quotient_card_of_pair_anchor {G : Finset (Finset α)} {p q : α}
    {Drop : Finset α}
    (hI : (isolated G).card = 4) (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hA : omittedStars G (starPairMax G p q) = {p,q})
    (hDrop : LinkedDeletion G (omittedStars G (starPairMax G p q)) Drop) :
    (((sources G \ omittedStars G (starPairMax G p q)) \ Drop) ∪ isolated G).card +
      Drop.card = (sources G).card + 2 := by
  classical
  have hk : 2 ≤ (sources G).card := Finset.one_lt_card.mpr ⟨p,hp,q,hq,hpq⟩
  have hsub : Drop ⊆ sources G \ {p,q} := by simpa only [hA] using hDrop.1
  have hs := Finset.card_sdiff_add_card_eq_card hsub
  have hE := sources_sdiff_pair_card hp hq hpq
  have hDis : Disjoint (((sources G \ {p,q}) \ Drop)) (isolated G) := by
    apply Finset.disjoint_left.mpr
    intro x hx hi
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).1
  rw [hA,Finset.card_union_of_disjoint hDis,hI]
  omega

/-- Two source links, with two retained partners not among the discarded
coordinates, provide a simultaneous two-coordinate quotient. -/
theorem linkedDeletion_of_two_disjoint_links {G : Finset (Finset α)} {A : Finset α}
    {u v w z : α} (huv : ({u,v} : Finset α) ∈ blockLinks (sources G) (starBlocks G) A)
    (hwz : ({w,z} : Finset α) ∈ blockLinks (sources G) (starBlocks G) A)
    (huv_wz : Disjoint ({u,v} : Finset α) {w,z}) :
    LinkedDeletion G A {u,w} ∧ ({u,w} : Finset α).card = 2 := by
  classical
  obtain ⟨hUs,hUc,_⟩ := mem_blockLinks.mp huv
  obtain ⟨hWs,hWc,_⟩ := mem_blockLinks.mp hwz
  have hu : u ∈ ({u,v} : Finset α) := Finset.mem_insert_self _ _
  have hv : v ∈ ({u,v} : Finset α) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hw : w ∈ ({w,z} : Finset α) := Finset.mem_insert_self _ _
  have hz : z ∈ ({w,z} : Finset α) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hD := Finset.disjoint_left.mp huv_wz
  have huw : u ≠ w := fun e => hD hu (e.symm ▸ hw)
  have hvw : v ≠ w := fun e => hD hv (e.symm ▸ hw)
  have hzu : z ≠ u := fun e => hD (e.symm ▸ hu) hz
  have hvu : v ≠ u := by
    intro e
    rw [e] at hUc
    simp at hUc
  have hzw : z ≠ w := by
    intro e
    rw [e] at hWc
    simp at hWc
  refine ⟨⟨Finset.insert_subset_iff.mpr ⟨hUs hu,Finset.singleton_subset_iff.mpr (hWs hw)⟩,?_⟩,by simp [huw]⟩
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨v,Finset.mem_sdiff.mpr ⟨hUs hv,by simp [hvu,hvw]⟩,huv⟩
  · exact ⟨z,Finset.mem_sdiff.mpr ⟨hWs hz,by simp [hzu,hzw]⟩,hwz⟩

/-- The actual-family saturation lemma for the distinct-triples anchor
geometry. The incidence identities and the two link choices are explicit
inputs, not a hidden assumption that any pair of triples is suitable. -/
theorem exact_four_two_deficitOne_anchors_full_isolate_omissions
    {G : Finset (Finset α)} {p q : α} {Drop : Finset α} {t : ℕ}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hI : (isolated G).card = 4) (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hdp : designDegree (starBlocks G) p + 2 = (sources G).card)
    (hdq : designDegree (starBlocks G) q + 2 = (sources G).card)
    (hA : omittedStars G (starPairMax G p q) = {p,q})
    (hDrop : LinkedDeletion G (omittedStars G (starPairMax G p q)) Drop)
    (hdc : Drop.card = 2)
    (hN : (starBlocks G).card + 2 * t = (sources G).card.choose 2)
    (htk : 3 * t ≤ (sources G).card) :
    isolated G ⊆ starPairMax G p q ∧
      ∀ x ∈ isolated G, starPairMax G p q \ {x} ∈ avoidBoth G (starLeaf G p) (starLeaf G q) := by
  let k := (sources G).card
  let V := ((sources G \ omittedStars G (starPairMax G p q)) \ Drop) ∪ isolated G
  have hc := nominal_quotient_card_of_pair_anchor hI hp hq hpq hA hDrop
  change V.card + Drop.card = k + 2 at hc
  have hV : V.card = k := by omega
  have hl := pair_lower_with_explicit_deficits (dp := 1) (dq := 1)
    hG hm hI hp hq hpq hdp hdq (∅ : Finset (α × Finset α)) (by simp)
  simp only [Finset.card_empty,Nat.add_zero] at hl
  change (starBlocks G).card + k + 6 + 1 + 1 ≤ _ at hl
  change (starBlocks G).card + 2 * t = k.choose 2 at hN
  change 3 * t ≤ k at htk
  apply linkedDeletion_pair_full_isolate_omissions hG hm hp hq hpq hDrop
  change 1 + V.card + (V.card - 1).choose 2 < _
  rw [hV]
  -- Use the sharp Pascal gap of k−1, rather than monotonicity alone.
  have hk : 2 ≤ k := Finset.one_lt_card.mpr ⟨p,hp,q,hq,hpq⟩
  have hPas : k.choose 2 = (k - 1) + (k - 1).choose 2 := by
    have h := Nat.choose_succ_succ' (k - 1) 1
    have he : k - 1 + 1 = k := by omega
    rw [he] at h
    simpa using h
  omega

#print axioms pair_lower_with_explicit_deficits
#print axioms linkedDeletion_of_two_disjoint_links
#print axioms exact_four_two_deficitOne_anchors_full_isolate_omissions
end FranklForcingFiber
