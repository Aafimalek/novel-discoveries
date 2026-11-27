import FranklLowFrequency

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

/-- In a weak ground-minimal counterexample the subfamily containing each
point has another active coordinate strictly below half. Otherwise deleting
that containing subfamily preserves the weak half bound. -/
theorem exists_low_frequency_in_containing_fiber {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (hp : p ∈ ground G) :
    ∃ y ∈ ground G, 2 * frequency (G.filter (p ∈ ·)) y < (G.filter (p ∈ ·)).card := by
  classical
  by_contra hn
  let P := G.filter (p ∈ ·)
  let F := G.filter (p ∉ ·)
  have hcard : P.card + F.card = G.card := Finset.card_filter_add_card_filter_not (p ∈ ·)
  have hGF : ground F ⊆ (ground G).erase p := by
    apply Finset.sup_le
    intro A hA
    obtain ⟨hAG,hnA⟩ := Finset.mem_filter.mp hA
    intro y hy
    exact Finset.mem_erase.mpr ⟨fun e => hnA (e ▸ hy), subset_ground hAG hy⟩
  have hF : NoStrictMajority F := by
    have hne : F.Nonempty := ⟨avoid G p, Finset.mem_filter.mpr ⟨avoid_mem_weak hG p, notMem_avoid G p⟩⟩
    refine ⟨hne, ?_, ?_, ?_, ?_⟩
    · intro A hA
      exact hG.2.1 (Finset.mem_filter.mp hA).1
    · intro A B hA hB
      obtain ⟨hA',hnA⟩ := Finset.mem_filter.mp hA
      obtain ⟨hB',hnB⟩ := Finset.mem_filter.mp hB
      exact Finset.mem_filter.mpr ⟨hG.2.2.1 hA' hB',
        fun h => (Finset.mem_union.mp h).elim hnA hnB⟩
    · intro A B C D E F' H ha hb hc hd he hf' hh
      exact hG.2.2.2.1 (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
        (Finset.mem_filter.mp hc).1 (Finset.mem_filter.mp hd).1 (Finset.mem_filter.mp he).1
        (Finset.mem_filter.mp hf').1 (Finset.mem_filter.mp hh).1
    · intro y
      by_cases hy : y ∈ ground G
      · have hP : P.card ≤ 2 * frequency P y := Nat.le_of_not_gt (fun h => hn ⟨y, hy, h⟩)
        have he := frequency_partition_by_point G p y
        change frequency P y + frequency F y = frequency G y at he
        have hfG := hG.2.2.2.2 y
        omega
      · have hny : y ∉ ground F := fun h => hy (Finset.mem_of_mem_erase (hGF h))
        rw [frequency_eq_zero_of_notMem_ground hny, Nat.mul_zero]
        exact Nat.zero_le _
  have hmin' := hmin F hF
  have hle := Finset.card_le_card hGF
  exact (Nat.not_lt_of_ge (hmin'.trans hle)) (Finset.card_lt_card (Finset.erase_ssubset hp))

theorem unique_source_all_nonisolates_present {G : Finset (Finset α)} {p : α}
    (hp : p ∈ sources G) (hpUnique : ∀ q ∈ sources G, q = p)
    {A : Finset α} (hA : A ∈ G) (hpA : p ∈ A)
    {y : α} (hy : y ∈ ground G) (hI : y ∉ isolated G) : y ∈ A := by
  by_cases hl : y ∈ leaves G
  · obtain ⟨q,hq,hqy,hF⟩ := (mem_leaves.mp hl).2
    have hqS : q ∈ sources G := mem_sources.mpr ⟨hq,y,hqy,hF⟩
    exact hF hA ((hpUnique q hqS).symm ▸ hpA)
  · by_cases hs : y ∈ sources G
    · exact (hpUnique y hs).symm ▸ hpA
    · exact False.elim (hI (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hy, hl⟩, hs⟩))

/-- A single nontrivial star in a weak ground-minimal counterexample needs at
least three isolated coordinates. -/
theorem unique_source_isolated_card_ge_three {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hpUnique : ∀ q ∈ sources G, q = p) :
    3 ≤ (isolated G).card := by
  classical
  by_contra! hSmall
  let P := G.filter (p ∈ ·)
  obtain ⟨y,hy,hLow⟩ := exists_low_frequency_in_containing_fiber hG hmin (mem_sources.mp hp).1
  change 2 * frequency P y < P.card at hLow
  have hIy : y ∈ isolated G := by
    by_contra hN
    have hf : P.filter (y ∈ ·) = P := Finset.filter_eq_self.mpr (fun A hA => by
      obtain ⟨hAG,hpA⟩ := Finset.mem_filter.mp hA
      exact unique_source_all_nonisolates_present hp hpUnique hAG hpA hy hN)
    change 2 * (P.filter (y ∈ ·)).card < P.card at hLow
    rw [hf] at hLow
    omega
  let X := P.filter (y ∈ ·)
  let Y := P.filter (y ∉ ·)
  have hmap : Set.MapsTo (insert y) (Y : Set (Finset α)) (X : Set (Finset α)) := by
    intro A ha
    obtain ⟨hAP,hAy⟩ := Finset.mem_filter.mp (show A ∈ Y from ha)
    obtain ⟨hAG,hpA⟩ := Finset.mem_filter.mp hAP
    let B := insert y A
    have hBU : B ⊆ ground G := Finset.insert_subset_iff.mpr ⟨hy,subset_ground hAG⟩
    have hmissing : ground G \ B ⊆ (isolated G).erase y := by
      intro z hz
      obtain ⟨hzG,hzB⟩ := Finset.mem_sdiff.mp hz
      have hzA : z ∉ A := fun h => hzB (Finset.mem_insert_of_mem h)
      refine Finset.mem_erase.mpr ⟨fun e => hzB (e ▸ Finset.mem_insert_self _ _), ?_⟩
      by_contra hn
      exact hzA (unique_source_all_nonisolates_present hp hpUnique hAG hpA hzG hn)
    have hI := Finset.card_erase_add_one hIy
    have hC := Finset.card_le_card hmissing
    have hC' : (ground G \ B).card ≤ 1 := by omega
    have hBmem : B ∈ G := by
      by_cases hzero : (ground G \ B).card = 0
      · have hUB : ground G ⊆ B := by
          intro z hz
          by_contra hn
          have h := Finset.mem_sdiff.mpr ⟨hz,hn⟩
          rw [Finset.card_eq_zero.mp hzero] at h
          exact Finset.notMem_empty _ h
        exact (Finset.Subset.antisymm hBU hUB).symm ▸ ground_mem_weak hG
      · have hOne : (ground G \ B).card = 1 := by omega
        obtain ⟨z,hz⟩ := Finset.card_eq_one.mp hOne
        have hz0 : z ∈ ground G \ B := hz.symm ▸ Finset.mem_singleton_self z
        have hzI : z ∈ isolated G := Finset.mem_of_mem_erase (hmissing hz0)
        have he : B = (ground G).erase z := by
          ext w
          constructor
          · intro hw
            exact Finset.mem_erase.mpr ⟨fun e => (Finset.mem_sdiff.mp hz0).2 (e ▸ hw),hBU hw⟩
          · intro hw
            obtain ⟨hne,hwG⟩ := Finset.mem_erase.mp hw
            by_contra hn
            have hh := Finset.mem_sdiff.mpr ⟨hwG,hn⟩
            rw [hz] at hh
            exact hne (Finset.mem_singleton.mp hh)
        exact he.symm ▸ isolated_coSingleton_mem hG hzI
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hBmem,Finset.mem_insert_of_mem hpA⟩,
      Finset.mem_insert_self _ _⟩
  have hinj : Set.InjOn (insert y) (Y : Set (Finset α)) := by
    intro A ha B hb he
    have hAy := (Finset.mem_filter.mp (show A ∈ Y from ha)).2
    have hBy := (Finset.mem_filter.mp (show B ∈ Y from hb)).2
    have he' := congrArg (·.erase y) he
    simpa only [Finset.erase_insert hAy,Finset.erase_insert hBy] using he'
  have hle := Finset.card_le_card_of_injOn (insert y) hmap hinj
  have hCard : X.card + Y.card = P.card := Finset.card_filter_add_card_filter_not (y ∈ ·)
  change 2 * X.card < P.card at hLow
  omega

#print axioms exists_low_frequency_in_containing_fiber
#print axioms unique_source_isolated_card_ge_three

end FranklForcingFiber
