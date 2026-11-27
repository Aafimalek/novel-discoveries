import FranklBlockIncidence
import FranklWitnessCounting
import FranklOneIsolateOrdinaryLine

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

noncomputable def starPairMax (G : Finset (Finset α)) (a b : α) : Finset α :=
  ground (avoidBoth G (starLeaf G a) (starLeaf G b))

noncomputable def starPairMaxima (G : Finset (Finset α)) : Finset (Finset α) := by
  classical
  exact (((sources G).product (sources G)).filter (fun ab => ab.1 ≠ ab.2)).image
    (fun ab => starPairMax G ab.1 ab.2)

theorem mem_starPairMaxima {G : Finset (Finset α)} {T : Finset α} :
    T ∈ starPairMaxima G ↔ ∃ a ∈ sources G, ∃ b ∈ sources G, a ≠ b ∧ starPairMax G a b = T := by
  classical
  constructor
  · intro ht
    obtain ⟨⟨a,b⟩,ha,he⟩ := Finset.mem_image.mp ht
    obtain ⟨hm,hne⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hm
    exact ⟨a,ha,b,hb,hne,he⟩
  · rintro ⟨a,ha,b,hb,hne,he⟩
    exact Finset.mem_image.mpr ⟨(a,b),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩,hne⟩,he⟩

noncomputable def omittedStars (G : Finset (Finset α)) (T : Finset α) : Finset α := by
  classical
  exact (sources G).filter (fun a => starLeaf G a ∉ T)

theorem mem_omittedStars {G : Finset (Finset α)} {T : Finset α} {a : α} :
    a ∈ omittedStars G T ↔ a ∈ sources G ∧ starLeaf G a ∉ T := by
  classical
  exact Finset.mem_filter

noncomputable def starBlocks (G : Finset (Finset α)) : Finset (Finset α) :=
  (starPairMaxima G).image (omittedStars G)

theorem starPairMax_comm (G : Finset (Finset α)) (a b : α) :
    starPairMax G a b = starPairMax G b a :=
  congrArg ground avoidBoth_comm

theorem starPairMax_mem {G : Finset (Finset α)} {a b : α}
    (ha : a ∈ sources G) (hb : b ∈ sources G) (hne : a ≠ b) :
    starPairMax G a b ∈ starPairMaxima G :=
  mem_starPairMaxima.mpr ⟨a,ha,b,hb,hne,rfl⟩

theorem starPairMax_mem_family {G : Finset (Finset α)} {a b : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (ha : a ∈ sources G) (hb : b ∈ sources G) (hne : a ≠ b) :
    starPairMax G a b ∈ G := by
  obtain ⟨has,hFa⟩ := starLeaf_spec ha
  obtain ⟨hbs,hFb⟩ := starLeaf_spec hb
  exact avoidBoth_top_mem hG (cross_pair_avoidBoth_nonempty hG hmin (mem_sources.mp ha).1
    (mem_sources.mp hb).1 hne has hbs hFa hFb)

theorem starPairMax_omit_left (G : Finset (Finset α)) (a b : α) :
    starLeaf G a ∉ starPairMax G a b :=
  notMem_avoidBoth_top_of_forces (Or.inl (forces_refl G _))

theorem starPairMax_omit_right (G : Finset (Finset α)) (a b : α) :
    starLeaf G b ∉ starPairMax G a b :=
  notMem_avoidBoth_top_of_forces (Or.inr (forces_refl G _))

theorem starPairMax_eq_of_omits_pair {G : Finset (Finset α)} {T : Finset α} {a b : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hT : T ∈ starPairMaxima G) (ha : a ∈ omittedStars G T) (hb : b ∈ omittedStars G T)
    (hab : a ≠ b) :
    T = starPairMax G a b := by
  obtain ⟨p,hp,q,hq,hpq,rfl⟩ := mem_starPairMaxima.mp hT
  obtain ⟨haS,haN⟩ := mem_omittedStars.mp ha
  obtain ⟨hbS,hbN⟩ := mem_omittedStars.mp hb
  have hex {x y z : α} (hx : x ∈ sources G) (hy : y ∈ sources G) (hz : z ∈ sources G)
      (hxy : x ≠ y) (hxz : x ≠ z) (hN : starLeaf G z ∉ starPairMax G x y) :
      starPairMax G x y = starPairMax G x z := by
    obtain ⟨hx',hFx⟩ := starLeaf_spec hx
    obtain ⟨hy',hFy⟩ := starLeaf_spec hy
    obtain ⟨hz',hFz⟩ := starLeaf_spec hz
    exact cross_pair_top_exchange hG hmin (mem_sources.mp hx).1 (mem_sources.mp hy).1
      (mem_sources.mp hz).1 hxy hxz hx' hy' hz' hFx hFy hFz hN
  by_cases he : p = a
  · subst p
    exact hex haS hq hbS hpq hab hbN
  · have h1 := hex hp hq haS hpq he haN
    have h2 := h1.trans (starPairMax_comm G p a)
    have hbn : starLeaf G b ∉ starPairMax G a p := fun hb' => hbN (h2.symm ▸ hb')
    exact h2.trans (hex haS hp hbS (Ne.symm he) hab hbn)

theorem omittedStars_injOn_pairMaxima {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) :
    Set.InjOn (omittedStars G) (starPairMaxima G : Set (Finset α)) := by
  intro T hT V hV he
  obtain ⟨a,ha,b,hb,hab,heT⟩ := mem_starPairMaxima.mp hT
  have haT : a ∈ omittedStars G T := mem_omittedStars.mpr ⟨ha, heT ▸ starPairMax_omit_left G a b⟩
  have hbT : b ∈ omittedStars G T := mem_omittedStars.mpr ⟨hb, heT ▸ starPairMax_omit_right G a b⟩
  exact heT.symm.trans (starPairMax_eq_of_omits_pair hG hmin hV (he ▸ haT) (he ▸ hbT) hab).symm

theorem starBlocks_pairDesign {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) :
    FranklBlockIncidence.PairDesign (sources G) (starBlocks G) := by
  constructor
  · intro A hA
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨a,ha,b,hb,hab,rfl⟩ := mem_starPairMaxima.mp hT
    exact ⟨fun _ h => (mem_omittedStars.mp h).1, Finset.one_lt_card.mpr
      ⟨a,mem_omittedStars.mpr ⟨ha,starPairMax_omit_left G a b⟩,b,
        mem_omittedStars.mpr ⟨hb,starPairMax_omit_right G a b⟩,hab⟩⟩
  · intro a ha b hb hab
    let T := starPairMax G a b
    refine ⟨omittedStars G T,⟨Finset.mem_image.mpr ⟨T,starPairMax_mem ha hb hab,rfl⟩,
      mem_omittedStars.mpr ⟨ha,starPairMax_omit_left G a b⟩,
      mem_omittedStars.mpr ⟨hb,starPairMax_omit_right G a b⟩⟩,?_⟩
    intro A hA
    obtain ⟨V,hV,rfl⟩ := Finset.mem_image.mp hA.1
    exact congrArg (omittedStars G) (starPairMax_eq_of_omits_pair hG hmin hV hA.2.1 hA.2.2 hab)

theorem compressed_support_le_omit_block {G : Finset (Finset α)} {a b : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (ha : a ∈ sources G) (hb : b ∈ sources G) (hne : a ≠ b) :
    (ground (compressPair G a b (starLeaf G a) (starLeaf G b))).card ≤
      (isolated G).card + ((sources G).card - (omittedStars G (starPairMax G a b)).card) := by
  let T := starPairMax G a b
  let R := omittedStars G T
  let C := ground (compressPair G a b (starLeaf G a) (starLeaf G b))
  have hT := starPairMax_mem_family hG hmin ha hb hne
  have hsub : C ⊆ isolated G ∪ (sources G \ R) := by
    intro v hv
    have hvR := mem_pairReps.mp (compressPair_ground_subset_reps hv)
    have hvT : v ∈ T := mem_raw_ground_of_mem_compress_ground hv
    by_cases hvS : v ∈ sources G
    · have hvN : v ∉ R := by
        intro h
        exact (mem_omittedStars.mp h).2 ((starLeaf_spec hvS).2 hT hvT)
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hvS,hvN⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr
        ⟨Finset.mem_sdiff.mpr ⟨hvR.1,hvR.2.1⟩,hvS⟩))
  have hRsub : R ⊆ sources G := fun _ h => (mem_omittedStars.mp h).1
  have hEq := Finset.card_sdiff_add_card_eq_card hRsub
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le (isolated G) (sources G \ R)
  change C.card ≤ (isolated G).card + ((sources G).card - R.card)
  omega

theorem cross_pair_actual_upper_of_omitted {G : Finset (Finset α)} {a b : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (ha : a ∈ sources G) (hb : b ∈ sources G) (hne : a ≠ b) :
    let m := (isolated G).card + ((sources G).card - (omittedStars G (starPairMax G a b)).card)
    (avoidBoth G (starLeaf G a) (starLeaf G b)).card ≤ 1 + m + m.choose 2 := by
  have haG := (mem_sources.mp ha).1
  have hbG := (mem_sources.mp hb).1
  obtain ⟨has,hFa⟩ := starLeaf_spec ha
  obtain ⟨hbs,hFb⟩ := starLeaf_spec hb
  have hc := compressed_support_le_omit_block hG hmin ha hb hne
  have hch := Nat.choose_le_choose 2 hc
  have hCard := cross_pair_compress_card hG hmin haG hbG hne has hbs hFa hFb
  have h4 := cross_pair_compress_noFourChain hG hmin haG hbG hne has hbs hFa hFb
    (cross_pair_noFourChain hG hmin haG hbG hne has hbs hFa hFb)
  have hu := FranklHeightThreeSauer.card_le (ground (compressPair G a b (starLeaf G a) (starLeaf G b)))
    (compress_pair_unionClosed hG.2.2.1) h4 (fun _ hA => subset_ground hA)
  dsimp
  omega

#print axioms starBlocks_pairDesign
#print axioms compressed_support_le_omit_block
#print axioms cross_pair_actual_upper_of_omitted

end FranklForcingFiber
