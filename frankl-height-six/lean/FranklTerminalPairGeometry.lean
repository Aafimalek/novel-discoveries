import FranklMultiLeafPair

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

theorem terminal_pair_avoidBoth_nonempty {G : Finset (Finset α)} {s t : α}
    (hG : NoStrictMajority G) (hsep : Separated G)
    (hs : s ∈ ground G) (ht : t ∈ ground G) (hts : t ≠ s)
    (hsT : Terminal G s) (htT : Terminal G t) :
    (avoidBoth G s t).Nonempty := by
  have hn := terminal_pair_avoidance_card hG hsep hs ht hts hsT htT
  have hC1 := Finset.card_erase_add_one hs
  have hC2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hts, ht⟩)
  exact Finset.card_pos.mp (by omega)

/-- No maximum of a terminal-pair avoidance fiber can begin a five-member chain.
No point is required to force either terminal. -/
theorem terminal_pair_top_noFiveChain_general {G : Finset (Finset α)} {s t : α}
    (hG : NoStrictMajority G) (hsep : Separated G)
    (hs : s ∈ ground G) (ht : t ∈ ground G) (hts : t ≠ s)
    (hsT : Terminal G s) (htT : Terminal G t)
    {A B C D : Finset α} (hA : A ∈ G) (hB : B ∈ G) (hC : C ∈ G) (hD : D ∈ G)
    (h1 : ground (avoidBoth G s t) ⊂ A) (h2 : A ⊂ B) (h3 : B ⊂ C) (h4 : C ⊂ D) : False := by
  let N := avoidBoth G s t
  let T := ground N
  have hN : (ground G).card ≤ N.card + 1 := terminal_pair_avoidance_card hG hsep hs ht hts hsT htT
  have hT : T ∈ G := avoidBoth_top_mem hG (terminal_pair_avoidBoth_nonempty hG hsep hs ht hts hsT htT)
  have hcap := FranklFiberHeightSix.card_subsets_le_of_four_extensions
    hG.2.2.1 hG.2.2.2.1 hT hA hB hC hD h1 h2 h3 h4
  have hsub : N.card ≤ (G.filter (fun X => X ⊆ T)).card := by
    apply Finset.card_le_card
    intro X hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, subset_ground hx⟩
  have hTA : T.card < A.card := Finset.card_lt_card h1
  have hAB := Finset.card_lt_card h2
  have hBC := Finset.card_lt_card h3
  have hCD := Finset.card_lt_card h4
  have hDU := Finset.card_le_card (subset_ground hD)
  omega

theorem terminal_pair_top_ssubset_avoid {G : Finset (Finset α)} {s t : α}
    (_hsT : Terminal G s) (htT : Terminal G t) (hts : t ≠ s) :
    ground (avoidBoth G s t) ⊂ avoid G s := by
  have hsT' : t ∈ avoid G s := by
    by_contra h
    exact hts.symm (htT ((notMem_avoid_iff_forces G s t).mp h))
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, fun he => notMem_avoidBoth_top_of_forces (Or.inr (forces_refl G t)) (he.symm ▸ hsT')⟩
  apply Finset.sup_le
  intro A hA
  obtain ⟨hAG, hn⟩ := Finset.mem_filter.mp hA
  exact avoid_subset hAG (fun h => hn (Or.inl h))

/-- Terminal pair fibers have height at most four, without restrictions on the
forcing graph. This is useful in the all-isolated case. -/
def NoFiveChain (L : Finset (Finset α)) : Prop :=
  ∀ ⦃A B C D E⦄, A ∈ L → B ∈ L → C ∈ L → D ∈ L → E ∈ L →
    A ⊂ B → B ⊂ C → C ⊂ D → D ⊂ E → False

theorem terminal_pair_fiber_noFiveChain {G : Finset (Finset α)} {s t : α}
    (hG : NoStrictMajority G) (hs : s ∈ ground G) (hts : t ≠ s)
    (hsT : Terminal G s) (htT : Terminal G t) :
    NoFiveChain (avoidBoth G s t) := by
  intro A B C D E hA hB hC hD hE hAB hBC hCD hDE
  have hEt : E ⊂ avoid G s := Finset.ssubset_of_subset_of_ssubset (subset_ground hE)
    (terminal_pair_top_ssubset_avoid hsT htT hts)
  exact hG.2.2.2.1 (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hB).1
    (Finset.mem_filter.mp hC).1 (Finset.mem_filter.mp hD).1 (Finset.mem_filter.mp hE).1
    (avoid_mem_weak hG s) (ground_mem_weak hG) hAB hBC hCD hDE hEt (avoid_ssubset_ground_weak hG hs)

/-- For a star center held fixed, the pair closure obeys exchange: if its
pair maximum also misses a second partner's leaf, both pair maxima agree. -/
theorem cross_pair_top_exchange {G : Finset (Finset α)} {p q r s t v : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hr : r ∈ ground G)
    (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hqt : q ≠ t) (hrv : r ≠ v)
    (hf : Forces G p s) (hg : Forces G q t) (hk : Forces G r v)
    (hv : v ∉ ground (avoidBoth G s t)) :
    ground (avoidBoth G s t) = ground (avoidBoth G s v) := by
  have hsep := weakMinimalGround_separated hG hmin
  obtain ⟨hs, ht, hts, _, hsT, htT⟩ := cross_pair_terminal_data hG hmin hp hq hpq hps hqt hf hg
  obtain ⟨_, _, hvs, _, _, hvT⟩ := cross_pair_terminal_data hG hmin hp hr hpr hps hrv hf hk
  let T := ground (avoidBoth G s t)
  let V := ground (avoidBoth G s v)
  have hT : T ∈ G := avoidBoth_top_mem hG (terminal_pair_avoidBoth_nonempty hG hsep hs ht hts hsT htT)
  have hV : V ∈ G := avoidBoth_top_mem hG (cross_pair_avoidBoth_nonempty hG hmin hp hr hpr hps hrv hf hk)
  have hsnot : s ∉ T := notMem_avoidBoth_top_of_forces (Or.inl (forces_refl G s))
  have hsub : T ⊆ V := subset_ground (show T ∈ avoidBoth G s v from Finset.mem_filter.mpr
    ⟨hT, fun h => h.elim hsnot hv⟩)
  have hVlt : V ⊂ avoid G s := terminal_pair_top_ssubset_avoid hsT hvT hvs
  have hmid : avoid G s ⊂ (ground G).erase p := by
    rw [avoid_eq_coPair_of_edge hG hmin hp hps hf]
    exact Finset.erase_ssubset (Finset.mem_erase.mpr ⟨hps.symm, hs⟩)
  by_contra hn
  exact terminal_pair_top_noFiveChain_general hG hsep hs ht hts hsT htT
    hV (avoid_mem_weak hG s) (coSingleton_of_outgoing hG hsep hp hps hf) (ground_mem_weak hG)
    (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hn⟩) hVlt hmid (Finset.erase_ssubset hp)

/-- All isolated points have their co-singletons in the family, even under
the weak (allows exact half) threshold. -/
theorem isolated_coSingleton_mem {G : Finset (Finset α)} {x : α}
    (hG : NoStrictMajority G) (hx : x ∈ isolated G) :
    (ground G).erase x ∈ G := by
  obtain ⟨_, _, hn⟩ := mem_isolated.mp hx
  have ha := avoid_mem_weak hG x
  have he : avoid G x = (ground G).erase x := by
    ext y
    constructor
    · intro hy
      exact Finset.mem_erase.mpr ⟨fun e => notMem_avoid G x (e ▸ hy), subset_ground ha hy⟩
    · intro hy
      obtain ⟨hyn, hyG⟩ := Finset.mem_erase.mp hy
      by_contra hny
      have hf := (notMem_avoid_iff_forces G x y).mp hny
      exact hn (mem_leaves.mpr ⟨(mem_isolated.mp hx).1, y, hyG, hyn, hf⟩)
  exact he ▸ ha

/-- A strict family member between a pair-avoiding maximum and a
single-terminal maximum leaves at most three ranks in the pair fiber. -/
theorem terminal_pair_fiber_noFourChain_of_intermediate {G : Finset (Finset α)} {s t a : α}
    (hG : NoStrictMajority G) (ha : a ∈ ground G)
    {B : Finset α} (hB : B ∈ G)
    (h1 : ground (avoidBoth G s t) ⊂ B) (h2 : B ⊂ avoid G a) :
    NoFourChain (avoidBoth G s t) := by
  intro A₁ A₂ A₃ A₄ hA₁ hA₂ hA₃ hA₄ h12 h23 h34
  have h4B := Finset.ssubset_of_subset_of_ssubset (subset_ground hA₄) h1
  exact hG.2.2.2.1 (Finset.mem_filter.mp hA₁).1 (Finset.mem_filter.mp hA₂).1
    (Finset.mem_filter.mp hA₃).1 (Finset.mem_filter.mp hA₄).1 hB
    (avoid_mem_weak hG a) (ground_mem_weak hG) h12 h23 h34 h4B h2 (avoid_ssubset_ground_weak hG ha)

/-- If a pair fiber is too large for height three on its support, every
distinct pair of terminal points outside its maximum generates the same maximum.
This statement covers the all-isolated regime without assuming any co-pairs. -/
theorem terminal_pair_top_exchange_of_large_fiber {G : Finset (Finset α)} {s t a b : α}
    (hG : NoStrictMajority G) (hsep : Separated G)
    (hs : s ∈ ground G) (ht : t ∈ ground G) (hts : t ≠ s)
    (hsT : Terminal G s) (htT : Terminal G t)
    (ha : a ∈ ground G) (hb : b ∈ ground G) (hba : b ≠ a)
    (haT : Terminal G a) (hbT : Terminal G b)
    (ha0 : a ∉ ground (avoidBoth G s t)) (hb0 : b ∉ ground (avoidBoth G s t))
    (hlarge : 1 + (ground (avoidBoth G s t)).card + Nat.choose (ground (avoidBoth G s t)).card 2 <
      (avoidBoth G s t).card) :
    ground (avoidBoth G s t) = ground (avoidBoth G a b) := by
  let T := ground (avoidBoth G s t)
  let V := ground (avoidBoth G a b)
  have hT : T ∈ G := avoidBoth_top_mem hG (terminal_pair_avoidBoth_nonempty hG hsep hs ht hts hsT htT)
  have hV : V ∈ G := avoidBoth_top_mem hG (terminal_pair_avoidBoth_nonempty hG hsep ha hb hba haT hbT)
  have hsub : T ⊆ V := subset_ground (show T ∈ avoidBoth G a b from Finset.mem_filter.mpr
    ⟨hT, fun h => h.elim ha0 hb0⟩)
  by_contra hne
  have h1 : T ⊂ V := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
  have h2 : V ⊂ avoid G a := terminal_pair_top_ssubset_avoid haT hbT hba
  have h4 := terminal_pair_fiber_noFourChain_of_intermediate hG ha hV h1 h2
  exact (Nat.not_lt_of_ge (FranklHeightThreeSauer.card_le T
    (cross_pair_unionClosed hG.2.2.1) h4 (fun _ hX => subset_ground hX))) hlarge

#print axioms terminal_pair_top_noFiveChain_general
#print axioms terminal_pair_fiber_noFiveChain
#print axioms cross_pair_top_exchange
#print axioms isolated_coSingleton_mem
#print axioms terminal_pair_fiber_noFourChain_of_intermediate
#print axioms terminal_pair_top_exchange_of_large_fiber

end FranklForcingFiber
