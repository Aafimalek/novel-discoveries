import FranklStarIndex

namespace FranklForcingFiber

variable {α : Type*} [DecidableEq α]

def restrictFamily (G : Finset (Finset α)) (S : Finset α) : Finset (Finset α) :=
  G.image (· ∩ S)

private theorem intersect_union (A B S : Finset α) : (A ∪ B) ∩ S = (A ∩ S) ∪ (B ∩ S) := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  tauto

theorem restrictFamily_unionClosed {G : Finset (Finset α)} (hU : UnionClosed G) (S : Finset α) :
    UnionClosed (restrictFamily G S) := by
  intro A B ha hb
  obtain ⟨a,haG,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b,hbG,rfl⟩ := Finset.mem_image.mp hb
  exact Finset.mem_image.mpr ⟨a∪b,hU haG hbG,intersect_union a b S⟩

private theorem restrict_lift_step {G : Finset (Finset α)} {S A B : Finset α}
    (hU : UnionClosed G) (ha : A ∈ G) (hb : B ∈ restrictFamily G S)
    (hlt : A ∩ S ⊂ B) : ∃ C ∈ G, A ⊂ C ∧ C ∩ S = B := by
  obtain ⟨B',hb',he⟩ := Finset.mem_image.mp hb
  have hsub := (Finset.ssubset_iff_subset_ne.mp hlt).1
  have heq : (A ∪ B') ∩ S = B := by
    rw [intersect_union,he,Finset.union_eq_right.mpr hsub]
  refine ⟨A∪B',hU ha hb',Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left,?_⟩,heq⟩
  intro h
  exact (Finset.ssubset_iff_subset_ne.mp hlt).2 ((congrArg (· ∩ S) h).trans heq)

theorem restrictFamily_noSevenChain {G : Finset (Finset α)} (hU : UnionClosed G)
    (hH : NoSevenChain G) (S : Finset α) : NoSevenChain (restrictFamily G S) := by
  intro A B C D E F H ha hb hc hd he hf hh hab hbc hcd hde hef hfh
  obtain ⟨A',ha',hA'⟩ := Finset.mem_image.mp ha
  obtain ⟨B',hb',hab',hB'⟩ := restrict_lift_step hU ha' hb (hA' ▸ hab)
  obtain ⟨C',hc',hbc',hC'⟩ := restrict_lift_step hU hb' hc (hB' ▸ hbc)
  obtain ⟨D',hd',hcd',hD'⟩ := restrict_lift_step hU hc' hd (hC' ▸ hcd)
  obtain ⟨E',he',hde',hE'⟩ := restrict_lift_step hU hd' he (hD' ▸ hde)
  obtain ⟨F',hf',hef',hF'⟩ := restrict_lift_step hU he' hf (hE' ▸ hef)
  obtain ⟨H',hh',hfh',_⟩ := restrict_lift_step hU hf' hh (hF' ▸ hfh)
  exact hH ha' hb' hc' hd' he' hf' hh' hab' hbc' hcd' hde' hef' hfh'

theorem restrictFamily_ground_subset {G : Finset (Finset α)} {S : Finset α} :
    ground (restrictFamily G S) ⊆ S := by
  apply Finset.sup_le
  intro A ha
  obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp ha
  exact Finset.inter_subset_right

/-- Projection preserves the half bound for a retained point if no two
sets avoiding that point become indistinguishable. -/
theorem restrictFamily_frequency_le_half {G : Finset (Finset α)} {S : Finset α} {x : α}
    (hx : x ∈ S)
    (hi : Set.InjOn (· ∩ S) ((G.filter (x ∉ ·)) : Set (Finset α)))
    (hfreq : 2 * frequency G x ≤ G.card) :
    2 * frequency (restrictFamily G S) x ≤ (restrictFamily G S).card := by
  let p : Finset α → Finset α := (· ∩ S)
  let L := restrictFamily G S
  have eq₁ : L.filter (x ∈ ·) = (G.filter (x ∈ ·)).image p := by
    ext A
    constructor
    · intro h
      obtain ⟨hA,hxA⟩ := Finset.mem_filter.mp h
      obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
      exact Finset.mem_image.mpr ⟨B,Finset.mem_filter.mpr ⟨hB,(Finset.mem_inter.mp hxA).1⟩,rfl⟩
    · intro h
      obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hBG,hBx⟩ := Finset.mem_filter.mp hB
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨B,hBG,rfl⟩,Finset.mem_inter.mpr ⟨hBx,hx⟩⟩
  have eq₂ : L.filter (x ∉ ·) = (G.filter (x ∉ ·)).image p := by
    ext A
    constructor
    · intro h
      obtain ⟨hA,hxA⟩ := Finset.mem_filter.mp h
      obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hA
      exact Finset.mem_image.mpr ⟨B,Finset.mem_filter.mpr
        ⟨hB,fun hh => hxA (Finset.mem_inter.mpr ⟨hh,hx⟩)⟩,rfl⟩
    · intro h
      obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hBG,hBx⟩ := Finset.mem_filter.mp hB
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨B,hBG,rfl⟩,
        fun hh => hBx (Finset.mem_inter.mp hh).1⟩
  have hle : (L.filter (x ∈ ·)).card ≤ (G.filter (x ∈ ·)).card := by
    rw [eq₁]
    exact Finset.card_image_le
  have he : (L.filter (x ∉ ·)).card = (G.filter (x ∉ ·)).card := by
    rw [eq₂,Finset.card_image_of_injOn hi]
  have hg := Finset.card_filter_add_card_filter_not (x ∈ ·) (s := G)
  have hl := Finset.card_filter_add_card_filter_not (x ∈ ·) (s := L)
  change 2 * (G.filter (x ∈ ·)).card ≤ G.card at hfreq
  change 2 * (L.filter (x ∈ ·)).card ≤ L.card
  omega

theorem ground_point_is_leaf_or_source {G : Finset (Finset α)}
    (hi : isolated G = ∅) {y : α} (hy : y ∈ ground G) :
    y ∈ leaves G ∨ y ∈ sources G := by
  by_cases hl : y ∈ leaves G
  · exact Or.inl hl
  · refine Or.inr ?_
    by_contra hs
    have hn : y ∈ isolated G :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hy,hl⟩,hs⟩
    simp [hi] at hn

/-- When all ground points lie in nontrivial stars, a projection to the
leaves is injective on sets avoiding any particular leaf. Its parent's
own absence is forced; other centers are coded by their chosen leaves. -/
theorem restrict_leaves_injOn_avoiders {G : Finset (Finset α)} {x : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hi : isolated G = ∅) (hx : x ∈ leaves G) :
    Set.InjOn (· ∩ leaves G) ((G.filter (x ∉ ·)) : Set (Finset α)) := by
  obtain ⟨p,hp,hpx,hf⟩ := (mem_leaves.mp hx).2
  intro A ha B hb he
  obtain ⟨haG,hax⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbG,hbx⟩ := Finset.mem_filter.mp hb
  change A ∩ leaves G = B ∩ leaves G at he
  have heq (z : α) (hz : z ∈ leaves G) : z ∈ A ↔ z ∈ B := by
    constructor
    · intro h
      exact (Finset.mem_inter.mp (he ▸ Finset.mem_inter.mpr ⟨h,hz⟩)).1
    · intro h
      exact (Finset.mem_inter.mp (he.symm ▸ Finset.mem_inter.mpr ⟨h,hz⟩)).1
  ext q
  by_cases hg : q ∈ ground G
  · rcases ground_point_is_leaf_or_source hi hg with hl | hs
    · exact heq q hl
    · by_cases hqp : q = p
      · subst q
        have haP : p ∉ A := fun h => hax (hf haG h)
        have hbP : p ∉ B := fun h => hbx (hf hbG h)
        simp [haP,hbP]
      · obtain ⟨hqn,hFq⟩ := starLeaf_spec hs
        have hL : starLeaf G q ∈ leaves G := mem_leaves.mpr
          ⟨mem_ground_of_forces hg hFq,q,hg,hqn,hFq⟩
        have hA := local_twins_across_stars hG hmin hp hg hpx hqn (fun h => hqp h.symm) hf hFq haG hax
        have hB := local_twins_across_stars hG hmin hp hg hpx hqn (fun h => hqp h.symm) hf hFq hbG hbx
        exact hA.trans ((heq _ hL).trans hB.symm)
  · have haQ : q ∉ A := fun h => hg (subset_ground haG h)
    have hbQ : q ∉ B := fun h => hg (subset_ground hbG h)
    simp [haQ,hbQ]

/-- A ground-minimal weak height-six counterexample has an isolated point.
If every point belongs to a nontrivial forcing star, restricting the
family to the leaves preserves the half bound and shrinks the ground. -/
theorem isolated_nonempty_of_weakMinimalGround {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) : (isolated G).Nonempty := by
  by_contra hI
  have hi : isolated G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
  let H := restrictFamily G (leaves G)
  have hN (A : Finset α) (ha : A ∈ G) : (A ∩ leaves G).Nonempty := by
    obtain ⟨x,hx⟩ := hG.2.1 ha
    rcases ground_point_is_leaf_or_source hi (subset_ground ha hx) with hl | hs
    · exact ⟨x,Finset.mem_inter.mpr ⟨hx,hl⟩⟩
    · obtain ⟨hn,hf⟩ := starLeaf_spec hs
      have hg := (mem_sources.mp hs).1
      have hL : starLeaf G x ∈ leaves G := mem_leaves.mpr
        ⟨mem_ground_of_forces hg hf,x,hg,hn,hf⟩
      exact ⟨starLeaf G x,Finset.mem_inter.mpr ⟨hf ha hx,hL⟩⟩
  have hweak : NoStrictMajority H := by
    refine ⟨hG.1.image _,?_,restrictFamily_unionClosed hG.2.2.1 _,
      restrictFamily_noSevenChain hG.2.2.1 hG.2.2.2.1 _,?_⟩
    · intro A ha
      obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp ha
      exact hN B hB
    · intro x
      by_cases hx : x ∈ leaves G
      · exact restrictFamily_frequency_le_half hx
          (restrict_leaves_injOn_avoiders hG hmin hi hx) (hG.2.2.2.2 x)
      · have hzero : frequency H x = 0 := by
          apply Finset.card_eq_zero.mpr
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro A ha
          obtain ⟨hA,hxA⟩ := Finset.mem_filter.mp ha
          exact hx (restrictFamily_ground_subset (subset_ground hA hxA))
        simp [hzero]
  have hsub : leaves G ⊆ ground G := fun _ h => (mem_leaves.mp h).1
  have hn : (leaves G).Nonempty := by
    obtain ⟨A,hA⟩ := hG.1
    obtain ⟨x,hx⟩ := hN A hA
    exact ⟨x,(Finset.mem_inter.mp hx).2⟩
  obtain ⟨x,hx⟩ := hn
  obtain ⟨p,hp,hpn,hf⟩ := (mem_leaves.mp hx).2
  have hpN := outgoing_not_leaf hG (weakMinimalGround_separated hG hmin) hpn hf
  have hlt : (leaves G).card < (ground G).card := Finset.card_lt_card <|
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub,fun eq => hpN (eq.symm ▸ hp)⟩
  have hcard : (ground H).card ≤ (leaves G).card :=
    Finset.card_le_card restrictFamily_ground_subset
  exact (Nat.not_lt_of_ge ((hmin H hweak).trans hcard)) hlt

/-- Any weak height-six counterexample has a ground-minimal reduction
whose proper forcing graph contains an isolated point. -/
theorem exists_isolated_reduction {G : Finset (Finset α)} (hG : NoStrictMajority G) :
    ∃ H : Finset (Finset α), NoStrictMajority H ∧ WeakMinimalGround H ∧ (isolated H).Nonempty := by
  obtain ⟨H,hH,hmin⟩ := exists_weakMinimalGround_of_noStrictMajority hG
  exact ⟨H,hH,hmin,isolated_nonempty_of_weakMinimalGround hH hmin⟩

#print axioms restrictFamily_noSevenChain
#print axioms restrictFamily_frequency_le_half
#print axioms restrict_leaves_injOn_avoiders
#print axioms isolated_nonempty_of_weakMinimalGround
#print axioms exists_isolated_reduction

end FranklForcingFiber
