import FranklSharedIsolate

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

theorem inter_ground_erase_eq_erase {G : Finset (Finset α)} {A : Finset α} {p : α}
    (hA : A ∈ G) : A ∩ (ground G).erase p = A.erase p := by
  ext y
  constructor
  · intro h
    obtain ⟨hy,hyS⟩ := Finset.mem_inter.mp h
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hyS).1, hy⟩
  · intro h
    obtain ⟨hne,hy⟩ := Finset.mem_erase.mp h
    exact Finset.mem_inter.mpr ⟨hy, Finset.mem_erase.mpr ⟨hne,subset_ground hA hy⟩⟩

/-- In any weak ground-minimal counterexample, every coordinate has an erasure
collision on sets avoiding some other active coordinate. -/
theorem coordinate_edge_avoiding_other {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (hp : p ∈ ground G) :
    ∃ y ∈ (ground G).erase p, ∃ A ∈ G, y ∉ A ∧ p ∉ A ∧ insert p A ∈ G := by
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
  obtain ⟨y,hyS,hfreq⟩ := hmaj
  have hn : ¬ Set.InjOn (· ∩ S) ((G.filter (y ∉ ·)) : Set (Finset α)) := by
    intro hi
    exact (Nat.not_lt_of_ge (restrictFamily_frequency_le_half hyS hi (hG.2.2.2.2 y))) hfreq
  refine ⟨y,hyS,?_⟩
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

theorem canonical_coordinate_edge_avoiding_other {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (hp : p ∈ ground G) :
    ∃ y ∈ (ground G).erase p, insert p (ground (avoidBoth G p y)) ∈ G := by
  obtain ⟨y,hy,A,hA,hAy,hAp,hi⟩ := coordinate_edge_avoiding_other hG hmin hp
  let T := ground (avoidBoth G p y)
  have hAF : A ∈ avoidBoth G p y := Finset.mem_filter.mpr ⟨hA,fun h => h.elim hAp hAy⟩
  have hAT := subset_ground hAF
  have hT : T ∈ G := avoidBoth_top_mem hG ⟨A,hAF⟩
  have he : insert p A ∪ T = insert p T := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_union]
    exact ⟨fun h => h.elim (fun h' => h'.elim Or.inl (fun hh => Or.inr (hAT hh))) Or.inr,
      fun h => h.elim (fun hh => Or.inl (Or.inl hh)) Or.inr⟩
  exact ⟨y,hy,he ▸ hG.2.2.1 hi hT⟩

/-- In an all-isolated weak minimal counterexample, every point has a
partner such that their co-pair is present or their avoidance fiber has height
at most three, with its corresponding quadratic support bound. -/
theorem all_isolated_structured_pair_per_point {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (hp : p ∈ ground G)
    (hI : ∀ x ∈ ground G, x ∈ isolated G) :
    ∃ y ∈ (ground G).erase p, ((ground G).erase y).erase p ∈ G ∨
      (NoFourChain (avoidBoth G p y) ∧
        (ground G).card ≤ 2 + (ground (avoidBoth G p y)).card +
          Nat.choose (ground (avoidBoth G p y)).card 2) := by
  obtain ⟨y,hy,hEdge⟩ := canonical_coordinate_edge_avoiding_other hG hmin hp
  obtain ⟨hne,hyG⟩ := Finset.mem_erase.mp hy
  let T := ground (avoidBoth G p y)
  have hT : T ∈ G := avoidBoth_top_mem hG
    (terminal_pair_avoidBoth_nonempty hG (weakMinimalGround_separated hG hmin) hp hyG hne
      (isolated_avoider_terminal (hI p hp)) (isolated_avoider_terminal (hI y hyG)))
  have hnp : p ∉ T := notMem_avoidBoth_top_of_forces (Or.inl (forces_refl G p))
  have hny : y ∉ T := notMem_avoidBoth_top_of_forces (Or.inr (forces_refl G y))
  have heq : avoid G y = (ground G).erase y := by
    apply Finset.Subset.antisymm
    · intro z hz
      exact Finset.mem_erase.mpr ⟨fun e => notMem_avoid G y (e ▸ hz),subset_ground (avoid_mem_weak hG y) hz⟩
    · intro z hz
      exact avoid_subset (isolated_coSingleton_mem hG (hI y hyG)) (Finset.notMem_erase _ _) hz
  refine ⟨y,hy,?_⟩
  by_cases hfull : insert p T = avoid G y
  · left
    have he := congrArg (·.erase p) hfull
    change (insert p T).erase p = (avoid G y).erase p at he
    rw [heq, Finset.erase_insert hnp] at he
    exact he ▸ hT
  · right
    have h1 : T ⊂ insert p T := Finset.ssubset_iff_subset_ne.mpr
      ⟨fun _ => Finset.mem_insert_of_mem, fun h => hnp (h.symm ▸ Finset.mem_insert_self _ _)⟩
    have h2 : insert p T ⊂ avoid G y := Finset.ssubset_iff_subset_ne.mpr
      ⟨avoid_subset hEdge (fun h => (Finset.mem_insert.mp h).elim hne hny), hfull⟩
    have h4 := terminal_pair_fiber_noFourChain_of_intermediate hG hyG hEdge h1 h2
    have hn := terminal_pair_avoidance_card hG (weakMinimalGround_separated hG hmin) hp hyG hne
      (isolated_avoider_terminal (hI p hp)) (isolated_avoider_terminal (hI y hyG))
    have hb := FranklHeightThreeSauer.card_le T (cross_pair_unionClosed hG.2.2.1) h4
      (fun _ hA => subset_ground hA)
    change (avoidBoth G p y).card ≤ 1 + (ground (avoidBoth G p y)).card +
      (ground (avoidBoth G p y)).card.choose 2 at hb
    refine ⟨h4,?_⟩
    omega

#print axioms coordinate_edge_avoiding_other
#print axioms canonical_coordinate_edge_avoiding_other
#print axioms all_isolated_structured_pair_per_point

end FranklForcingFiber
