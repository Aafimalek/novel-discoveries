import FranklOneIsolateCounting
import FranklFewIsolates
import FranklStarCounting

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

theorem all_pair_maxima_full_of_one_isolate_count {G : Finset (Finset α)} {x : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hx : x ∈ isolated G) (hunique : ∀ y ∈ isolated G, y = x)
    (hLarge : let m := (isolated G).card + (sources G).card - 2
      1 + (m-1) + (m-1).choose 2 < (ground G).card + (sources G).card - 1) :
    ∀ ⦃C⦄, C ⊆ sources G → C.card = 2 → outsideStars G C ∈ G := by
  classical
  intro C hC h2
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp h2
  have ha : a ∈ sources G := hC (by simp)
  have hb : b ∈ sources G := hC (by simp)
  have haG := (mem_sources.mp ha).1
  have hbG := (mem_sources.mp hb).1
  obtain ⟨has,hFas⟩ := starLeaf_spec ha
  obtain ⟨hbt,hFbt⟩ := starLeaf_spec hb
  obtain ⟨hs,ht,hts,_,hsT,htT⟩ := cross_pair_terminal_data hG hmin haG hbG hab has hbt hFas hFbt
  have hsL : starLeaf G a ∈ leaves G := mem_leaves.mpr ⟨hs,a,haG,has,hFas⟩
  have htL : starLeaf G b ∈ leaves G := mem_leaves.mpr ⟨ht,b,hbG,hbt,hFbt⟩
  have hLow := one_isolate_leaf_pair_avoidance_extra hG hmin hsL htL hts hx hunique
  have hn := terminal_pair_avoidBoth_nonempty hG (weakMinimalGround_separated hG hmin) hs ht hts hsT htT
  have hlarge' : 1 + ((pairReps G a b).card - 1) + ((pairReps G a b).card - 1).choose 2 <
      (avoidBoth G (starLeaf G a) (starLeaf G b)).card := by
    rw [pairReps_card_formula hG hmin ha hb hab]
    dsimp at hLarge
    omega
  have hSat := cross_pair_support_saturated hG hmin haG hbG hab has hbt hFas hFbt hlarge'
  have hEq : outsideStars G {a,b} = ground (avoidBoth G (starLeaf G a) (starLeaf G b)) := by
    ext y
    rw [cross_pair_top_exact_of_support hG hmin haG hbG hab has hbt hFas hFbt hSat]
    simp only [mem_outsideStars,Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
    constructor
    · rintro ⟨hyG,hyA,hyB⟩
      exact ⟨hyG,fun e => hyA (e.symm ▸ forces_refl G a),
        fun e => hyB (e.symm ▸ forces_refl G b),hyA,hyB⟩
    · rintro ⟨hyG,_,_,hyA,hyB⟩
      exact ⟨hyG,hyA,hyB⟩
  rw [hEq]
  exact avoidBoth_top_mem hG hn

/-- With exactly one isolated point and any forcing edges, there must be
at least nine star centers. -/
theorem one_isolate_nonzero_sources_ge_nine {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hI : (isolated G).card = 1) (hk0 : 0 < (sources G).card) :
    9 ≤ (sources G).card := by
  obtain ⟨x,hxEq⟩ := Finset.card_eq_one.mp hI
  have hx : x ∈ isolated G := hxEq.symm ▸ Finset.mem_singleton_self x
  have hUnique : ∀ y ∈ isolated G, y = x := by
    intro y hy
    rw [hxEq] at hy
    exact Finset.mem_singleton.mp hy
  by_contra! hkBad
  let k := (sources G).card
  have h2 : 2 ≤ k := by
    by_contra! hf
    have he : (sources G).card = 1 := by omega
    obtain ⟨p,hpEq⟩ := Finset.card_eq_one.mp he
    have hp : p ∈ sources G := hpEq.symm ▸ Finset.mem_singleton_self p
    have hi := unique_source_isolated_card_ge_three hG hmin hp (fun y hy => by
      rw [hpEq] at hy
      exact Finset.mem_singleton.mp hy)
    omega
  obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp (show 1 < (sources G).card by omega)
  obtain ⟨hs,hFs⟩ := starLeaf_spec hp
  obtain ⟨ht,hFt⟩ := starLeaf_spec hq
  have hpG := (mem_sources.mp hp).1
  have hqG := (mem_sources.mp hq).1
  obtain ⟨hsG,htG,hts,_,_,_⟩ := cross_pair_terminal_data hG hmin hpG hqG hpq hs ht hFs hFt
  have hsL : starLeaf G p ∈ leaves G := mem_leaves.mpr ⟨hsG,p,hpG,hs,hFs⟩
  have htL : starLeaf G q ∈ leaves G := mem_leaves.mpr ⟨htG,q,hqG,ht,hFt⟩
  have hlo := one_isolate_leaf_pair_avoidance_extra hG hmin hsL htL hts hx hUnique
  have hhi := cross_pair_avoidance_upper hG hmin hpG hqG hpq hs ht hFs hFt
  rw [pairReps_card_formula hG hmin hp hq hpq,hI] at hhi
  have hLen := sources_card_le_leaves hG hmin
  have hPart := partition_card hG hmin
  have hN : 2*k+1 ≤ (ground G).card := by omega
  have hLower : 3*k ≤ (avoidBoth G (starLeaf G p) (starLeaf G q)).card := by omega
  have hRep : 1 + (isolated G).card + (sources G).card - 2 = k := by omega
  have hUp : (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤ 1+(k-1)+(k-1).choose 2 := by
    have he : 1 + (sources G).card - 2 = k-1 := by omega
    rwa [he] at hhi
  by_cases hk6 : k ≤ 6
  · have hNum : 1+(k-1)+(k-1).choose 2 < 3*k := by
      interval_cases k <;> decide
    omega
  · have h7 : 7 ≤ k := by omega
    have h8 : k ≤ 8 := by omega
    have hSaturation : 1+(k-2)+(k-2).choose 2 < 3*k := by
      interval_cases k <;> decide
    have hLarge : let m := (isolated G).card + (sources G).card - 2
        1 + (m-1) + (m-1).choose 2 < (ground G).card + (sources G).card - 1 := by
      dsimp
      have he : (isolated G).card + (sources G).card - 2 - 1 = k-2 := by omega
      rw [he]
      omega
    have hfull := all_pair_maxima_full_of_one_isolate_count hG hmin hx hUnique hLarge
    have hExtra := extra_from_full_pair_maxima hG hmin hp hq hpq hfull
    change (ground G).card + (k-2).choose 2 ≤ (avoidBoth G (starLeaf G p) (starLeaf G q)).card+1 at hExtra
    have hImpossible : 1+(k-1)+(k-1).choose 2 < 2*k+(k-2).choose 2 := by
      interval_cases k <;> decide
    omega

#print axioms all_pair_maxima_full_of_one_isolate_count
#print axioms one_isolate_nonzero_sources_ge_nine

end FranklForcingFiber
