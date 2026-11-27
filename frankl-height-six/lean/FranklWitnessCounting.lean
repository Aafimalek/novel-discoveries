import FranklOneIsolateCounting
import FranklStarCounting

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

/-- Choose one of the isolated witnesses available for each active source. -/
noncomputable def chosenIsolatedWitness (G : Finset (Finset α))
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (p : α) : α := by
  classical
  exact if hp : p ∈ sources G then Classical.choose (source_has_isolated_witness hG hmin hp) else p

theorem chosenIsolatedWitness_spec {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) {p : α} (hp : p ∈ sources G) :
    IsolatedWitness G p (chosenIsolatedWitness G hG hmin p) := by
  classical
  simpa [chosenIsolatedWitness,hp] using
    Classical.choose_spec (source_has_isolated_witness hG hmin hp)

noncomputable def sourceWitnessTop (G : Finset (Finset α)) (hG : NoStrictMajority G)
    (hmin : WeakMinimalGround G) (p : α) : Finset α :=
  ground (avoidBoth G p (chosenIsolatedWitness G hG hmin p))

theorem sourceWitnessTop_spec {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) {p : α} (hp : p ∈ sources G) :
    let T := sourceWitnessTop G hG hmin p
    T ∈ G ∧ p ∉ T ∧ chosenIsolatedWitness G hG hmin p ∉ T ∧ leaves G ⊆ T ∧ insert p T ∈ G :=
  canonical_sharedIsolate_edge hG (chosenIsolatedWitness_spec hG hmin hp)

/-- Canonical isolated-witness maxima are distinct for distinct sources,
whether or not their chosen witnesses are the same. -/
theorem sourceWitnessTop_injOn {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) :
    Set.InjOn (sourceWitnessTop G hG hmin) (sources G : Set α) := by
  intro p hp q hq he
  by_contra hpq
  let P := sourceWitnessTop G hG hmin p
  let Q := sourceWitnessTop G hG hmin q
  let x := chosenIsolatedWitness G hG hmin q
  change P = Q at he
  obtain ⟨_,hpP,_,_,hiP⟩ := sourceWitnessTop_spec hG hmin hp
  obtain ⟨_,hqQ,hxQ,_,_⟩ := sourceWitnessTop_spec hG hmin hq
  have hxI : x ∈ isolated G := (chosenIsolatedWitness_spec hG hmin hq).1
  have hxp : x ≠ p := fun e => (Finset.mem_sdiff.mp hxI).2 (e.symm ▸ hp)
  have hi : insert p P ∈ avoidBoth G q x := by
    refine Finset.mem_filter.mpr ⟨hiP,?_⟩
    intro h
    rcases h with h | h
    · exact (Finset.mem_insert.mp h).elim (Ne.symm hpq) (fun hqP => hqQ (show q ∈ Q from he ▸ hqP))
    · exact (Finset.mem_insert.mp h).elim hxp (fun hxP => hxQ (show x ∈ Q from he ▸ hxP))
  have hpQ : p ∈ Q := subset_ground hi (Finset.mem_insert_self _ _)
  exact hpP (show p ∈ P from he.symm ▸ hpQ)

theorem nonleaf_coSingleton_mem {G : Finset (Finset α)} {v : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (hv : v ∈ ground G)
    (hn : v ∉ leaves G) :
    (ground G).erase v ∈ G := by
  by_cases hs : v ∈ sources G
  · obtain ⟨hsG,s,hvs,hF⟩ := mem_sources.mp hs
    exact coSingleton_of_outgoing hG (weakMinimalGround_separated hG hmin) hsG hvs hF
  · exact isolated_coSingleton_mem hG (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hv,hn⟩,hs⟩)

theorem sourceWitnessTop_ne_avoid {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) {p v : α}
    (hp : p ∈ sources G) (hv : v ∈ ground G) :
    sourceWitnessTop G hG hmin p ≠ avoid G v := by
  intro he
  obtain ⟨_,hpT,hxT,hLT,_⟩ := sourceWitnessTop_spec hG hmin hp
  let x := chosenIsolatedWitness G hG hmin p
  let T := sourceWitnessTop G hG hmin p
  change T = avoid G v at he
  have hvNL : v ∉ leaves G := fun hl => notMem_avoid G v (he ▸ hLT hl)
  have hCo := nonleaf_coSingleton_mem hG hmin hv hvNL
  have hsub := avoid_subset hCo (Finset.notMem_erase _ _)
  have hpG := (mem_sources.mp hp).1
  by_cases hpv : p = v
  · have hxI : x ∈ isolated G := (chosenIsolatedWitness_spec hG hmin hp).1
    have hxG := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxI).1).1
    have hxv : x ≠ v := fun e => (Finset.mem_sdiff.mp hxI).2 ((e.trans hpv.symm).symm ▸ hp)
    exact hxT (show x ∈ T from he.symm ▸ hsub (Finset.mem_erase.mpr ⟨hxv,hxG⟩))
  · exact hpT (show p ∈ T from he.symm ▸ hsub (Finset.mem_erase.mpr ⟨hpv,hpG⟩))

/-- Every distinct leaf pair gets one extra both-containing member per
source, with no restriction on the number of isolated vertices. -/
theorem leaf_pair_avoidance_extra_witnesses {G : Finset (Finset α)} {s t : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hs : s ∈ leaves G) (ht : t ∈ leaves G) (hts : t ≠ s) :
    (ground G).card + (sources G).card ≤ (avoidBoth G s t).card + 1 := by
  let R := (sources G).image (sourceWitnessTop G hG hmin)
  have hRc : R.card = (sources G).card := Finset.card_image_of_injOn (sourceWitnessTop_injOn hG hmin)
  have hsep := weakMinimalGround_separated hG hmin
  have hleaf_terminal {z : α} (hz : z ∈ leaves G) : Terminal G z := by
    obtain ⟨p,hp,hne,hF⟩ := (mem_leaves.mp hz).2
    intro y hf
    by_contra hny
    exact noThreeForcingChain_of_separated hG hsep hp hne (Ne.symm hny) hF hf
  have hR : ∀ ⦃A⦄, A ∈ R → A ∈ G ∧ s ∈ A ∧ t ∈ A ∧
      A ≠ ground G ∧ ∀ v ∈ ground G, A ≠ avoid G v := by
    intro A hA
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨hT,hpT,_,hLT,_⟩ := sourceWitnessTop_spec hG hmin hp
    refine ⟨hT,hLT hs,hLT ht,?_,fun v hv => sourceWitnessTop_ne_avoid hG hmin hp hv⟩
    intro e
    exact hpT (show p ∈ sourceWitnessTop G hG hmin p from e.symm ▸ (mem_sources.mp hp).1)
  have h := terminal_pair_avoidance_extra_noncanonical hG hsep (mem_leaves.mp hs).1
    (mem_leaves.mp ht).1 hts (hleaf_terminal hs) (hleaf_terminal ht) hR
  rwa [hRc] at h

/-- Universal strengthening of the cross-star leaf bound: the number of
leaves plus the number of sources is bounded by the number of pairs of
retained representatives. -/
theorem forcing_star_leaf_add_sources_bound {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hk : 2 ≤ (sources G).card) :
    (leaves G).card + (sources G).card ≤
      ((isolated G).card + (sources G).card - 2).choose 2 := by
  obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp (show 1 < (sources G).card by omega)
  have hpG := (mem_sources.mp hp).1
  have hqG := (mem_sources.mp hq).1
  obtain ⟨hps,hFp⟩ := starLeaf_spec hp
  obtain ⟨hqt,hFq⟩ := starLeaf_spec hq
  obtain ⟨hs,ht,hts,_,_,_⟩ := cross_pair_terminal_data hG hmin hpG hqG hpq hps hqt hFp hFq
  have hsL : starLeaf G p ∈ leaves G := mem_leaves.mpr ⟨hs,p,hpG,hps,hFp⟩
  have htL : starLeaf G q ∈ leaves G := mem_leaves.mpr ⟨ht,q,hqG,hqt,hFq⟩
  have hlo := leaf_pair_avoidance_extra_witnesses hG hmin hsL htL hts
  have hhi := cross_pair_avoidance_upper hG hmin hpG hqG hpq hps hqt hFp hFq
  rw [pairReps_card_formula hG hmin hp hq hpq] at hhi
  have hpart := partition_card hG hmin
  omega

#print axioms sourceWitnessTop_injOn
#print axioms sourceWitnessTop_ne_avoid
#print axioms leaf_pair_avoidance_extra_witnesses
#print axioms forcing_star_leaf_add_sources_bound

end FranklForcingFiber
