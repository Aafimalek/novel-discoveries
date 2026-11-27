import FranklFewIsolates
import FranklSharedIsolate

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

/-- The members containing both distinct terminals include all their
canonical single-point avoidance maxima except the two corresponding ones. -/
theorem terminal_pair_containing_card {G : Finset (Finset α)} {s t : α}
    (hG : NoStrictMajority G) (hsep : Separated G)
    (hs : s ∈ ground G) (ht : t ∈ ground G) (hts : t ≠ s)
    (hsT : Terminal G s) (htT : Terminal G t) :
    (ground G).card ≤ (G.filter (fun A => s ∈ A ∧ t ∈ A)).card + 1 := by
  classical
  let V := ((ground G).erase s).erase t
  let P := G.filter (fun A => s ∈ A ∧ t ∈ A)
  have hV (v : α) (hv : v ∈ V) : v ∈ ground G ∧ v ≠ s ∧ v ≠ t := by
    obtain ⟨hvt,hv'⟩ := Finset.mem_erase.mp hv
    obtain ⟨hvs,hvg⟩ := Finset.mem_erase.mp hv'
    exact ⟨hvg,hvs,hvt⟩
  have hmaps : Set.MapsTo (avoid G) (V : Set α) (P.erase (ground G) : Set (Finset α)) := by
    intro v hv
    obtain ⟨hvg,hvs,hvt⟩ := hV v hv
    have hsv : s ∈ avoid G v := by
      by_contra hn
      exact hvs (hsT ((notMem_avoid_iff_forces G v s).mp hn))
    have htv : t ∈ avoid G v := by
      by_contra hn
      exact hvt (htT ((notMem_avoid_iff_forces G v t).mp hn))
    refine Finset.mem_erase.mpr ⟨?_,Finset.mem_filter.mpr ⟨avoid_mem_weak hG v,hsv,htv⟩⟩
    intro he
    exact notMem_avoid G v (he.symm ▸ hvg)
  have hVcard := Finset.card_le_card_of_injOn (avoid G) hmaps
    (fun a ha b hb he => avoid_injOn_ground hsep (hV a ha).1 (hV b hb).1 he)
  have hTopP : ground G ∈ P := Finset.mem_filter.mpr ⟨ground_mem_weak hG,hs,ht⟩
  have hPcard := Finset.card_erase_add_one hTopP
  have hV0 := Finset.card_erase_add_one hs
  have hV1 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hts,ht⟩)
  change V.card + 1 = ((ground G).erase s).card at hV1
  change (ground G).card ≤ P.card + 1
  omega

/-- Each point in an all-isolated weak ground-minimal counterexample lies
in at least 2n−1 members, where n is the ground cardinality. -/
theorem all_isolated_frequency_lower {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hI : ∀ x ∈ ground G, x ∈ isolated G) (hp : p ∈ ground G) :
    2 * (ground G).card - 1 ≤ frequency G p := by
  obtain ⟨y,hy,hLow⟩ := exists_low_frequency_in_containing_fiber hG hmin hp
  have hyp : y ≠ p := by
    intro e
    subst y
    have hfil : (G.filter (p ∈ ·)).filter (p ∈ ·) = G.filter (p ∈ ·) := by simp
    change 2 * ((G.filter (p ∈ ·)).filter (p ∈ ·)).card < (G.filter (p ∈ ·)).card at hLow
    rw [hfil] at hLow
    omega
  have hb := terminal_pair_containing_card hG (weakMinimalGround_separated hG hmin) hp hy hyp
    (isolated_avoider_terminal (hI p hp)) (isolated_avoider_terminal (hI y hy))
  have hf : (G.filter (fun A => p ∈ A ∧ y ∈ A)).card = frequency (G.filter (p ∈ ·)) y := by
    unfold frequency
    congr 1
    ext A
    simp only [Finset.mem_filter]
    tauto
  rw [hf] at hb
  change 2 * frequency (G.filter (p ∈ ·)) y < frequency G p at hLow
  omega

/-- Any all-isolated weak ground-minimal counterexample has at least 4n−2
members. This does not depend on a co-pair assumption. -/
theorem all_isolated_card_lower {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hI : ∀ x ∈ ground G, x ∈ isolated G) :
    4 * (ground G).card - 2 ≤ G.card := by
  obtain ⟨A,hA⟩ := hG.1
  obtain ⟨p,hp⟩ := hG.2.1 hA
  have h := all_isolated_frequency_lower hG hmin hI (subset_ground hA hp)
  have hf := hG.2.2.2.2 p
  omega

#print axioms terminal_pair_containing_card
#print axioms all_isolated_frequency_lower
#print axioms all_isolated_card_lower

end FranklForcingFiber
