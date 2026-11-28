import FranklBlockClosureEncoding
import FranklSignatureHeightThree

namespace FranklForcingFiber
open FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

/-- The two-leaf avoidance fiber obeys the sharper height-three Sauer bound on
the number of outside incidence signatures and retained isolated points. -/
theorem pair_fiber_card_le_sauer_block_signatures {G : Finset (Finset α)}
    {A : Finset α} {p q : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hEq : A = omittedStars G (starPairMax G p q)) :
    let K := compressPair G p q (starLeaf G p) (starLeaf G q)
    let m := ((sources G \ A).image (signature K)).card + (isolated G).card
    (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤ 1 + m + m.choose 2 := by
  obtain ⟨hps,hFp⟩ := starLeaf_spec hp
  obtain ⟨hqt,hFq⟩ := starLeaf_spec hq
  have hpG := (mem_sources.mp hp).1
  have hqG := (mem_sources.mp hq).1
  have he := cross_pair_compress_card hG hmin hpG hqG hpq hps hqt hFp hFq
  have h4 := cross_pair_compress_noFourChain hG hmin hpG hqG hpq hps hqt hFp hFq
    (cross_pair_noFourChain hG hmin hpG hqG hpq hps hqt hFp hFq)
  have hS := family_card_le_sauer_signatures (E := sources G \ A) (I := isolated G)
      (compress_pair_unionClosed hG.2.2.1) h4 (fun _ hZ =>
        compressed_pair_subset_outside_block_or_isolates hG hmin hp hq hpq hEq hZ)
  rw [← he]
  exact hS

#print axioms pair_fiber_card_le_sauer_block_signatures
end FranklForcingFiber
