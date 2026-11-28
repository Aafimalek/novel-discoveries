import FranklTransitivePairQuotient
import FranklRootedLinkRegions

/- Checked by pinned ordinary Lean with warnings as errors. -/
namespace FranklForcingFiber
open FranklBlockIncidence FranklFinsetTwinQuotient
variable {α : Type*} [DecidableEq α]

theorem transitive_nominal_quotient_card {G : Finset (Finset α)} {A Drop : Finset α}
    (hA : A ⊆ sources G) (hDrop : TransitivelyLinkedDeletion G A Drop) :
    (((sources G \ A) \ Drop) ∪ isolated G).card + Drop.card + A.card =
      (sources G).card + (isolated G).card := by
  have hDis : Disjoint ((sources G \ A) \ Drop) (isolated G) := by
    apply Finset.disjoint_left.mpr
    intro x hx hi
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).1
  rw [Finset.card_union_of_disjoint hDis]
  have h₁ := Finset.card_sdiff_add_card_eq_card hA
  have h₂ := Finset.card_sdiff_add_card_eq_card hDrop.1
  omega

theorem transitive_linked_nominal_Sauer_cap {G : Finset (Finset α)} {p q : α} {Drop : Finset α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hDrop : TransitivelyLinkedDeletion G (omittedStars G (starPairMax G p q)) Drop)
    {m : ℕ}
    (hV : (((sources G \ omittedStars G (starPairMax G p q)) \ Drop) ∪ isolated G).card ≤ m) :
    (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤ 1 + m + m.choose 2 := by
  let K := compressedStarPair G p q
  let R := ground K \ Drop
  let L := traceFamily K R
  obtain ⟨_,hRV,_,hcard,hUC,hH,_⟩ := transitiveLinkedDeletion_pair_quotient_geometry hG hm hp hq hpq hDrop
  have hR : R.card ≤ m := (Finset.card_le_card hRV).trans hV
  have hCh := Nat.choose_le_choose 2 hR
  have hSauer := FranklHeightThreeSauer.card_le R hUC hH (fun _ h => traceFamily_subset h)
  change L.card ≤ 1 + R.card + R.card.choose 2 at hSauer
  change L.card = (avoidBoth G (starLeaf G p) (starLeaf G q)).card at hcard
  omega

/-- Reusable contradiction once actual block links certify four
simultaneous deletions at two deficit-two anchors in an ordinary block.
This explicitly assumes the deletion geometry; it does not prove the
four-cycle exception classification. -/
theorem exact_four_deficit_two_ordinary_pair_not_four_linked_drops
    {G : Finset (Finset α)} {p q : α} {Drop : Finset α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hI : (isolated G).card = 4)
    (hDeg : ∀ v ∈ sources G, (sources G).card ≤ designDegree (starBlocks G) v + 3)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hDp : designDegree (starBlocks G) p + 3 = (sources G).card)
    (hDq : designDegree (starBlocks G) q + 3 = (sources G).card)
    (hA : omittedStars G (starPairMax G p q) = {p,q})
    (hDrop : TransitivelyLinkedDeletion G (omittedStars G (starPairMax G p q)) Drop)
    (hDrop4 : 4 ≤ Drop.card) : False := by
  classical
  let k := (sources G).card
  let B := starBlocks G
  let A := omittedStars G (starPairMax G p q)
  let V := ((sources G \ A) \ Drop) ∪ isolated G
  have hAs : A ⊆ sources G := fun _ h => (mem_omittedStars.mp h).1
  have hAc : A.card = 2 := by
    change A = {p,q} at hA
    rw [hA]
    simp [hpq]
  have hV := transitive_nominal_quotient_card hAs hDrop
  change V.card + Drop.card + A.card = k + (isolated G).card at hV
  rw [hAc,hI] at hV
  have hv : V.card ≤ k - 2 := by omega
  have hUp := transitive_linked_nominal_Sauer_cap hG hm hp hq hpq hDrop hv
  have hLow := pair_lower_with_explicit_deficits (dp := 2) (dq := 2) hG hm hI hp hq hpq
    hDp hDq (∅ : Finset (α × Finset α)) (by simp)
  simp only [Finset.card_empty,Nat.add_zero] at hLow
  have hK : 2 ≤ k := Finset.one_lt_card.mpr ⟨p,hp,q,hq,hpq⟩
  have hChoose := choose_two_split_two hK
  obtain ⟨hLoss,_,hLossCap⟩ := deficit_le_two_global_budgets (starBlocks_pairDesign hG hm) hDeg
  change B.card + 2 * (triples B).card + 5 * (quads B).card = k.choose 2 at hLoss
  change 3 * (2 * (triples B).card + 5 * (quads B).card) ≤ 4 * k at hLossCap
  change B.card + k + 6 + 2 + 2 ≤ _ at hLow
  change _ ≤ 1 + (k - 2) + (k - 2).choose 2 at hUp
  omega

#print axioms transitive_nominal_quotient_card
#print axioms transitive_linked_nominal_Sauer_cap
#print axioms exact_four_deficit_two_ordinary_pair_not_four_linked_drops
end FranklForcingFiber
