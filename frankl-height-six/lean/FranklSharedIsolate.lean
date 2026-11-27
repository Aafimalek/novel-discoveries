import FranklTerminalPairGeometry
import FranklIsolatedWitness

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

/-- An isolated witness is missed by a one-point source edge in the all-leaf fiber. -/
def IsolatedWitness (G : Finset (Finset α)) (p x : α) : Prop :=
  x ∈ isolated G ∧ ∃ A ∈ G, x ∉ A ∧ p ∉ A ∧ leaves G ⊆ A ∧ insert p A ∈ G

theorem source_has_isolated_witness {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (hp : p ∈ sources G) :
    ∃ x, IsolatedWitness G p x :=
  source_edge_with_isolated_witness hG hmin hp

theorem canonical_sharedIsolate_edge {G : Finset (Finset α)} {p x : α}
    (hG : NoStrictMajority G) (hw : IsolatedWitness G p x) :
    let T := ground (avoidBoth G p x)
    T ∈ G ∧ p ∉ T ∧ x ∉ T ∧ leaves G ⊆ T ∧ insert p T ∈ G := by
  obtain ⟨_, A, hA, hxA, hpA, hL, hi⟩ := hw
  let T := ground (avoidBoth G p x)
  have ha : A ∈ avoidBoth G p x := Finset.mem_filter.mpr ⟨hA, fun h => h.elim hpA hxA⟩
  have hAT := subset_ground ha
  have hT : T ∈ G := avoidBoth_top_mem hG ⟨A, ha⟩
  refine ⟨hT, notMem_avoidBoth_top_of_forces (Or.inl (forces_refl G p)),
    notMem_avoidBoth_top_of_forces (Or.inr (forces_refl G x)), hL.trans hAT, ?_⟩
  have he : insert p A ∪ T = insert p T := by
    ext y
    simp only [Finset.mem_union, Finset.mem_insert]
    exact ⟨fun h => h.elim (fun h' => h'.elim Or.inl (fun hh => Or.inr (hAT hh))) Or.inr,
      fun h => h.elim (fun hh => Or.inl (Or.inl hh)) Or.inr⟩
  exact he ▸ hG.2.2.1 hi hT

theorem isolated_avoider_terminal {G : Finset (Finset α)} {x : α}
    (hx : x ∈ isolated G) : Terminal G x := by
  intro y hF
  by_contra hne
  have hxG := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).1
  exact (Finset.mem_sdiff.mp hx).2 (mem_sources.mpr ⟨hxG, y, Ne.symm hne, hF⟩)

/-- Maximal sets avoiding a source and a common isolated witness contain
every other source sharing that witness. -/
theorem source_mem_avoider_when_shared_isolated_witness {G : Finset (Finset α)} {p q x : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (hp : p ∈ sources G)
    (hq : q ∈ sources G) (hpq : p ≠ q) (hw : IsolatedWitness G p x) (hz : IsolatedWitness G q x) :
    q ∈ ground (avoidBoth G p x) := by
  have hsep := weakMinimalGround_separated hG hmin
  obtain ⟨hpG, s, hps, hF⟩ := mem_sources.mp hp
  have hs := mem_ground_of_forces hpG hF
  have hsL : s ∈ leaves G := mem_leaves.mpr ⟨hs, p, hpG, hps, hF⟩
  have hxs : x ≠ s := fun e => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hw.1).1).2 (e.symm ▸ hsL)
  have hxG := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hw.1).1).1
  have hxT := isolated_avoider_terminal hw.1
  have hsT : Terminal G s := by
    intro y hf
    by_contra hne
    exact noThreeForcingChain_of_separated hG hsep hpG hps (Ne.symm hne) hF hf
  let P := ground (avoidBoth G p x)
  let Q := ground (avoidBoth G q x)
  let T := ground (avoidBoth G s x)
  obtain ⟨hPG, hPp, hPx, hPL, hinsert⟩ := canonical_sharedIsolate_edge hG hw
  obtain ⟨hQG, hQq, hQx, _, _⟩ := canonical_sharedIsolate_edge hG hz
  have h1 : T ⊂ P := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · apply Finset.sup_le
      intro A hA
      obtain ⟨hAG, hno⟩ := Finset.mem_filter.mp hA
      exact subset_ground (show A ∈ avoidBoth G p x from Finset.mem_filter.mpr
        ⟨hAG, fun h => h.elim (fun h' => hno (Or.inl (hF hAG h'))) (fun h' => hno (Or.inr h'))⟩)
    · intro he
      have hsP : s ∈ P := hPL hsL
      exact notMem_avoidBoth_top_of_forces (Or.inl (forces_refl G s))
        (show s ∈ T from he.symm ▸ hsP)
  have h3 : Q ⊂ avoid G x := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨avoid_subset hQG hQx, ?_⟩
    intro he
    have hqG := (mem_sources.mp hq).1
    have hqx : q ≠ x := fun e => (Finset.mem_sdiff.mp hw.1).2 (e ▸ hq)
    have hqCx : q ∈ avoid G x := by
      by_contra hn
      exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hw.1).1).2
        (mem_leaves.mpr ⟨hxG, q, hqG, hqx, (notMem_avoid_iff_forces G x q).mp hn⟩)
    exact hQq (show q ∈ Q from he.symm ▸ hqCx)
  by_contra hqP
  have hsub : P ⊆ Q := subset_ground (show P ∈ avoidBoth G q x from
    Finset.mem_filter.mpr ⟨hPG, fun h => h.elim hqP hPx⟩)
  have he : P = Q := by
    by_contra hn
    exact terminal_pair_top_noFiveChain_general hG hsep hs hxG hxs hsT hxT
      hPG hQG (avoid_mem_weak hG x) (ground_mem_weak hG)
      h1 (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hn⟩) h3 (avoid_ssubset_ground_weak hG hxG)
  have hiP : insert p P ∈ avoidBoth G q x := by
    refine Finset.mem_filter.mpr ⟨hinsert, ?_⟩
    intro h
    have hxp : x ≠ p := fun e => (Finset.mem_sdiff.mp hw.1).2 (e.symm ▸ hp)
    exact h.elim (fun h' => (Finset.mem_insert.mp h').elim hpq.symm hqP)
      (fun h' => (Finset.mem_insert.mp h').elim hxp hPx)
  have hpQ : p ∈ Q := subset_ground hiP (Finset.mem_insert_self _ _)
  exact hPp (show p ∈ P from he.symm ▸ hpQ)

/-- If x is the unique isolated point, each source has its co-pair with x. -/
theorem source_isolate_coPair_of_unique_isolate {G : Finset (Finset α)} {p x : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hunique : ∀ y ∈ isolated G, y = x) :
    ((ground G).erase p).erase x ∈ G := by
  obtain ⟨y, hy⟩ := source_has_isolated_witness hG hmin hp
  have hwy : IsolatedWitness G p x := (hunique y hy.1) ▸ hy
  obtain ⟨hTG, hpT, hxT, hL, _⟩ := canonical_sharedIsolate_edge hG hwy
  have he : ground (avoidBoth G p x) = ((ground G).erase p).erase x := by
    ext z
    constructor
    · intro hz
      exact Finset.mem_erase.mpr ⟨fun e => hxT (e ▸ hz), Finset.mem_erase.mpr
        ⟨fun e => hpT (e ▸ hz), subset_ground hTG hz⟩⟩
    · intro hz
      obtain ⟨hzx, hz'⟩ := Finset.mem_erase.mp hz
      obtain ⟨hzp, hzG⟩ := Finset.mem_erase.mp hz'
      by_cases hl : z ∈ leaves G
      · exact hL hl
      · by_cases hs : z ∈ sources G
        · obtain ⟨w, hw⟩ := source_has_isolated_witness hG hmin hs
          have hwz : IsolatedWitness G z x := (hunique w hw.1) ▸ hw
          exact source_mem_avoider_when_shared_isolated_witness hG hmin hp hs hzp.symm hwy hwz
        · exact False.elim (hzx (hunique z (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hzG, hl⟩, hs⟩)))
  exact he ▸ hTG

#print axioms canonical_sharedIsolate_edge
#print axioms source_mem_avoider_when_shared_isolated_witness
#print axioms source_isolate_coPair_of_unique_isolate

end FranklForcingFiber
