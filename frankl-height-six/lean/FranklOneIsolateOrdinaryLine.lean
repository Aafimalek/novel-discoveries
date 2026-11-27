import FranklAllIsolatedEdges

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

/-- Deleting one active coordinate of a weak ground-minimal counterexample
creates a strict majority at some retained coordinate. -/
theorem exists_majority_after_coordinate_erasure {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (hp : p ∈ ground G) :
    ∃ y ∈ (ground G).erase p, (restrictFamily G ((ground G).erase p)).card <
      2 * frequency (restrictFamily G ((ground G).erase p)) y := by
  classical
  let S := (ground G).erase p
  let F := restrictFamily G S
  have hSF : ground F ⊆ S := restrictFamily_ground_subset
  have hmaj : ∃ y ∈ S, F.card < 2 * frequency F y := by
    by_contra hnone
    have hfreq (y : α) : 2 * frequency F y ≤ F.card := by
      by_cases hyS : y ∈ S
      · exact Nat.le_of_not_gt (fun h => hnone ⟨y,hyS,h⟩)
      · have hz : frequency F y = 0 := by
          apply Finset.card_eq_zero.mpr
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro A ha
          obtain ⟨hAF,hyA⟩ := Finset.mem_filter.mp ha
          exact hyS (hSF (subset_ground hAF hyA))
        rw [hz, Nat.mul_zero]
        exact Nat.zero_le _
    have hF : NoStrictMajority F := by
      refine ⟨hG.1.image _, ?_, restrictFamily_unionClosed hG.2.2.1 S,
        restrictFamily_noSevenChain hG.2.2.1 hG.2.2.2.1 S, hfreq⟩
      intro A ha
      obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp ha
      change (B ∩ (ground G).erase p).Nonempty
      rw [inter_ground_erase_eq_erase hB]
      by_contra hbn
      have he : B = {p} := by
        ext z
        simp only [Finset.mem_singleton]
        constructor
        · intro hz
          by_contra hzp
          exact hbn ⟨z,Finset.mem_erase.mpr ⟨hzp,hz⟩⟩
        · intro e
          obtain ⟨w,hw⟩ := hG.2.1 hB
          by_cases hwp : w = p
          · exact e.symm ▸ hwp ▸ hw
          · exact False.elim (hbn ⟨w,Finset.mem_erase.mpr ⟨hwp,hw⟩⟩)
      exact weak_no_singleton hG p (he ▸ hB)
    have hle := (hmin F hF).trans (Finset.card_le_card hSF)
    exact (Nat.not_lt_of_ge hle) (Finset.card_lt_card (Finset.erase_ssubset hp))
  exact hmaj

theorem coordinate_edge_of_erasure_majority {G : Finset (Finset α)} {p y : α}
    (hG : NoStrictMajority G) (hyS : y ∈ (ground G).erase p)
    (hfreq : (restrictFamily G ((ground G).erase p)).card <
      2 * frequency (restrictFamily G ((ground G).erase p)) y) :
    ∃ A ∈ G, y ∉ A ∧ p ∉ A ∧ insert p A ∈ G := by
  classical
  let S := (ground G).erase p
  have hn : ¬ Set.InjOn (· ∩ S) ((G.filter (y ∉ ·)) : Set (Finset α)) := by
    intro hi
    exact (Nat.not_lt_of_ge (restrictFamily_frequency_le_half hyS hi (hG.2.2.2.2 y))) hfreq
  by_contra hno
  apply hn
  intro A ha B hb he
  obtain ⟨hAG,hAy⟩ := Finset.mem_filter.mp ha
  obtain ⟨hBG,hBy⟩ := Finset.mem_filter.mp hb
  change A ∩ (ground G).erase p = B ∩ (ground G).erase p at he
  have he' := (inter_ground_erase_eq_erase hAG).symm.trans (he.trans (inter_ground_erase_eq_erase hBG))
  have haux {C D : Finset α} (hCG : C ∈ G) (hDG : D ∈ G) (hCy : y ∉ C)
      (hpC : p ∉ C) (hpD : p ∈ D) (hee : C.erase p = D.erase p) : False :=
    hno ⟨C,hCG,hCy,hpC,eq_insert_of_erase_of_mem hee hpD ▸ hDG⟩
  apply equal_of_erase_and_same_membership he'
  exact ⟨fun h => by
    by_contra h'
    exact haux hBG hAG hBy h' h he'.symm,
  fun h => by
    by_contra h'
    exact haux hAG hBG hAy h' h he'⟩

theorem avoidBoth_comm {G : Finset (Finset α)} {s t : α} :
    avoidBoth G s t = avoidBoth G t s := by
  ext A
  simp only [avoidBoth, Finset.mem_filter, or_comm]

theorem canonical_coordinate_edge_of_erasure_majority {G : Finset (Finset α)} {p y : α}
    (hG : NoStrictMajority G) (hyS : y ∈ (ground G).erase p)
    (hfreq : (restrictFamily G ((ground G).erase p)).card <
      2 * frequency (restrictFamily G ((ground G).erase p)) y) :
    insert p (ground (avoidBoth G p y)) ∈ G := by
  obtain ⟨A,hA,hAy,hAp,hi⟩ := coordinate_edge_of_erasure_majority hG hyS hfreq
  let T := ground (avoidBoth G p y)
  have hAF : A ∈ avoidBoth G p y := Finset.mem_filter.mpr ⟨hA,fun h => h.elim hAp hAy⟩
  have hAT := subset_ground hAF
  have hT : T ∈ G := avoidBoth_top_mem hG ⟨A,hAF⟩
  have he : insert p A ∪ T = insert p T := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_union]
    exact ⟨fun h => h.elim (fun h' => h'.elim Or.inl (fun hh => Or.inr (hAT hh))) Or.inr,
      fun h => h.elim (fun hh => Or.inl (Or.inl hh)) Or.inr⟩
  exact he ▸ hG.2.2.1 hi hT

theorem unique_isolate_erasure_has_leaf_majority {G : Finset (Finset α)} {x : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hx : x ∈ isolated G) (hunique : ∀ y ∈ isolated G, y = x) :
    ∃ s ∈ leaves G, (restrictFamily G ((ground G).erase x)).card <
      2 * frequency (restrictFamily G ((ground G).erase x)) s := by
  obtain ⟨hxG,_,hxNL⟩ := mem_isolated.mp hx
  obtain ⟨y,hy,hmaj⟩ := exists_majority_after_coordinate_erasure hG hmin hxG
  by_cases hyL : y ∈ leaves G
  · exact ⟨y,hyL,hmaj⟩
  · have hyG := (Finset.mem_erase.mp hy).2
    have hyS : y ∈ sources G := by
      by_contra hn
      have hyI : y ∈ isolated G := Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hyG,hyL⟩,hn⟩
      exact (Finset.mem_erase.mp hy).1 (hunique _ hyI)
    obtain ⟨hsne, hF⟩ := starLeaf_spec hyS
    have hsG := mem_ground_of_forces hyG hF
    have hsL : starLeaf G y ∈ leaves G := mem_leaves.mpr ⟨hsG,y,hyG,hsne,hF⟩
    have hKeep : starLeaf G y ∈ (ground G).erase x := Finset.mem_erase.mpr
      ⟨fun e => hxNL (e ▸ hsL),hsG⟩
    have hf := frequency_le_of_forces (forces_restrictFamily hKeep hF)
    exact ⟨starLeaf G y,hsL,by omega⟩

/-- The unique isolate and a suitable leaf give an exact co-triple avoidance
maximum. The third omitted point is that leaf's source. -/
theorem unique_isolate_has_exact_coTriple_avoider {G : Finset (Finset α)} {x : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hx : x ∈ isolated G) (hunique : ∀ y ∈ isolated G, y = x) :
    ∃ p ∈ sources G, ∃ s, p ≠ s ∧ Forces G p s ∧
      ground (avoidBoth G s x) = (((ground G).erase p).erase s).erase x := by
  obtain ⟨s,hsL,hmaj⟩ := unique_isolate_erasure_has_leaf_majority hG hmin hx hunique
  obtain ⟨p,hp,hps,hF⟩ := (mem_leaves.mp hsL).2
  obtain ⟨hxG,hxT,hxNL⟩ := mem_isolated.mp hx
  have hs := (mem_leaves.mp hsL).1
  have hsx : s ≠ x := fun e => hxNL (e ▸ hsL)
  have hsep := weakMinimalGround_separated hG hmin
  have hsT : Terminal G s := by
    intro y hsy
    by_contra hny
    exact noThreeForcingChain_of_separated hG hsep hp hps (Ne.symm hny) hF hsy
  let T := ground (avoidBoth G s x)
  have hT : T ∈ G := avoidBoth_top_mem hG
    (terminal_pair_avoidBoth_nonempty hG hsep hs hxG hsx.symm hsT hxT)
  have hEdge : insert x T ∈ G := by
    have hE := canonical_coordinate_edge_of_erasure_majority hG
      (Finset.mem_erase.mpr ⟨hsx,hs⟩) hmaj
    rw [avoidBoth_comm (G := G) (s := x)] at hE
    exact hE
  have hxN : x ∉ T := notMem_avoidBoth_top_of_forces (Or.inr (forces_refl G x))
  have hsN : s ∉ T := notMem_avoidBoth_top_of_forces (Or.inl (forces_refl G s))
  have h1 : T ⊂ insert x T := Finset.ssubset_iff_subset_ne.mpr
    ⟨fun _ => Finset.mem_insert_of_mem, fun e => hxN (e.symm ▸ Finset.mem_insert_self _ _)⟩
  have hEq : insert x T = avoid G s := by
    by_contra he
    have h2 : insert x T ⊂ avoid G s := Finset.ssubset_iff_subset_ne.mpr
      ⟨avoid_subset hEdge (fun h => (Finset.mem_insert.mp h).elim hsx hsN),he⟩
    have h3 : avoid G s ⊂ (ground G).erase p := by
      rw [avoid_eq_coPair_of_edge hG hmin hp hps hF]
      exact Finset.erase_ssubset (Finset.mem_erase.mpr ⟨hps.symm,hs⟩)
    exact terminal_pair_top_noFiveChain_general hG hsep hs hxG hsx.symm hsT hxT
      hEdge (avoid_mem_weak hG s) (coSingleton_of_outgoing hG hsep hp hps hF) (ground_mem_weak hG)
      h1 h2 h3 (Finset.erase_ssubset hp)
  refine ⟨p,mem_sources.mpr ⟨hp,s,hps,hF⟩,s,hps,hF,?_⟩
  have hEq' := congrArg (·.erase x) hEq
  change (insert x T).erase x = (avoid G s).erase x at hEq'
  rwa [Finset.erase_insert hxN,avoid_eq_coPair_of_edge hG hmin hp hps hF] at hEq'

/-- In the same regime there is a center whose pair maximum with every other
center contains the isolate. Thus the exact co-triple does not propagate to
those other pair maxima. -/
theorem unique_isolate_has_center_with_all_pair_maxima_containing_isolate
    {G : Finset (Finset α)} {x : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hx : x ∈ isolated G) (hunique : ∀ y ∈ isolated G, y = x) :
    ∃ p ∈ sources G, ∃ s, p ≠ s ∧ Forces G p s ∧
      ground (avoidBoth G s x) = (((ground G).erase p).erase s).erase x ∧
      ∀ q ∈ sources G, q ≠ p → ∀ t, q ≠ t → Forces G q t → x ∈ ground (avoidBoth G s t) := by
  obtain ⟨p,hpS,s,hps,hFp,hEq⟩ := unique_isolate_has_exact_coTriple_avoider hG hmin hx hunique
  refine ⟨p,hpS,s,hps,hFp,hEq,?_⟩
  intro q hqS hqp t hqt hFq
  have hp := (mem_sources.mp hpS).1
  have hq := (mem_sources.mp hqS).1
  have hsep := weakMinimalGround_separated hG hmin
  obtain ⟨hs,ht,hts,htp,hsT,htT⟩ := cross_pair_terminal_data hG hmin hp hq hqp.symm hps hqt hFp hFq
  have htL : t ∈ leaves G := mem_leaves.mpr ⟨ht,q,hq,hqt,hFq⟩
  have hsL : s ∈ leaves G := mem_leaves.mpr ⟨hs,p,hp,hps,hFp⟩
  obtain ⟨hxG,hxT,hxNL⟩ := mem_isolated.mp hx
  have hxt : x ≠ t := fun e => hxNL (e.symm ▸ htL)
  have hxs : x ≠ s := fun e => hxNL (e.symm ▸ hsL)
  let T := ground (avoidBoth G s t)
  let V := ground (avoidBoth G s x)
  have hT : T ∈ G := avoidBoth_top_mem hG
    (terminal_pair_avoidBoth_nonempty hG hsep hs ht hts hsT htT)
  have hV : V ∈ G := avoidBoth_top_mem hG
    (terminal_pair_avoidBoth_nonempty hG hsep hs hxG hxs hsT hxT)
  by_contra hxN
  have hsN : s ∉ T := notMem_avoidBoth_top_of_forces (Or.inl (forces_refl G s))
  have hsub : T ⊆ V := subset_ground (show T ∈ avoidBoth G s x from Finset.mem_filter.mpr
    ⟨hT,fun h => h.elim hsN hxN⟩)
  have hvlt : V ⊂ avoid G s := terminal_pair_top_ssubset_avoid hsT hxT hxs
  have hmid : avoid G s ⊂ (ground G).erase p := by
    rw [avoid_eq_coPair_of_edge hG hmin hp hps hFp]
    exact Finset.erase_ssubset (Finset.mem_erase.mpr ⟨hps.symm,hs⟩)
  have he : T = V := by
    by_contra hn
    exact terminal_pair_top_noFiveChain_general hG hsep hs ht hts hsT htT
      hV (avoid_mem_weak hG s) (coSingleton_of_outgoing hG hsep hp hps hFp) (ground_mem_weak hG)
      (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,hn⟩) hvlt hmid (Finset.erase_ssubset hp)
  have htV : t ∈ V := by
    change t ∈ ground (avoidBoth G s x)
    rw [hEq]
    exact Finset.mem_erase.mpr ⟨hxt.symm,Finset.mem_erase.mpr ⟨hts,Finset.mem_erase.mpr ⟨htp,ht⟩⟩⟩
  exact notMem_avoidBoth_top_of_forces (Or.inr (forces_refl G t)) (show t ∈ T from he.symm ▸ htV)

#print axioms exists_majority_after_coordinate_erasure
#print axioms unique_isolate_erasure_has_leaf_majority
#print axioms unique_isolate_has_exact_coTriple_avoider
#print axioms unique_isolate_has_center_with_all_pair_maxima_containing_isolate

end FranklForcingFiber
