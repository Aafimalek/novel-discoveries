import FranklFourAmbientClassification

/- Kernel-checked on pinned Lean 4.36 and Mathlib. -/
namespace FranklForcingFiber
open FranklFourTraceCertificate

variable {α : Type*} [DecidableEq α]

def sourceAvoiders (G : Finset (Finset α)) (p : α) : Finset (Finset α) :=
  G.filter (p ∉ ·)

def sourcePairAvoiders (G : Finset (Finset α)) (p y z : α) : Finset (Finset α) :=
  (sourceAvoiders G p).filter (fun A => ¬ (y ∈ A ∨ z ∈ A))

theorem mem_sourcePairAvoiders {G : Finset (Finset α)} {p y z : α} {A : Finset α} :
    A ∈ sourcePairAvoiders G p y z ↔ A ∈ G ∧ p ∉ A ∧ y ∉ A ∧ z ∉ A := by
  simp [sourcePairAvoiders,sourceAvoiders,not_or,and_assoc]

theorem sourcePairAvoiders_unionClosed {G : Finset (Finset α)} {p y z : α}
    (hU : UnionClosed G) : FranklFiberHeightSix.UnionClosed (sourcePairAvoiders G p y z) := by
  intro A D ha hd
  obtain ⟨haG,hap,hay,haz⟩ := mem_sourcePairAvoiders.mp ha
  obtain ⟨hdG,hdp,hdy,hdz⟩ := mem_sourcePairAvoiders.mp hd
  exact mem_sourcePairAvoiders.mpr
    ⟨hU haG hdG,fun h => (Finset.mem_union.mp h).elim hap hdp,
      fun h => (Finset.mem_union.mp h).elim hay hdy,
      fun h => (Finset.mem_union.mp h).elim haz hdz⟩

noncomputable def actualContainingMask (G : Finset (Finset α)) (p : α)
    (lab : FourTraceLabels (isolated G)) : Nat :=
  familyMask (containingTraces G p lab)

/-- An entry of the numeric list has an actual source-containing lift. -/
theorem containing_member_of_profile {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hp : p ∈ sources G)
    (lab : FourTraceLabels (isolated G)) {t : Nat}
    (ht : t ∈ profile (actualContainingMask G p lab)) :
    ∃ D ∈ G, p ∈ D ∧ lab.trace D = decode t := by
  have htF : decode t ∈ containingTraces G p lab :=
    (mem_profile_familyMask_iff (containingTraces_mandatory hG hp lab) (profile_lt_16 ht)).mp ht
  obtain ⟨D,hD,he⟩ := Finset.mem_image.mp htF
  obtain ⟨hDG,hpD⟩ := Finset.mem_filter.mp hD
  exact ⟨D,hDG,hpD,he⟩

/-- The mask of an actual family member avoiding the two labels passes
the exact checked compatibility test. Its union with a containing
member remains in the containing fiber. -/
theorem actual_trace_is_safeAvoiding {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hp : p ∈ sources G)
    (lab : FourTraceLabels (isolated G)) {i j : Label}
    {A : Finset α} (hAG : A ∈ G)
    (hi : lab.point i ∉ A) (hj : lab.point j ∉ A) :
    encode (lab.trace A) ∈ safeAvoiding (actualContainingMask G p lab) i.val j.val := by
  let t := encode (lab.trace A)
  have h' (k : Label) (hk : lab.point k ∉ A) : k ∉ decode t := by
    intro h
    exact hk (lab.mem_trace.mp (by simpa [t] using h))
  apply mem_safeAvoiding_of_bits (encode_lt_16 _) (h' i hi) (h' j hj)
  intro u hu
  obtain ⟨D,hDG,hpD,hDu⟩ := containing_member_of_profile hG hp lab hu
  have hlt : (t ||| u) < 16 :=
    Nat.or_lt_two_pow (n := 4) (encode_lt_16 _) (profile_lt_16 hu)
  apply (mem_profile_familyMask_iff (containingTraces_mandatory hG hp lab) hlt).mpr
  have htrace : decode (t ||| u) = lab.trace (A ∪ D) := by
    rw [decode_union, ← hDu, lab.trace_union]
    simp [t]
  rw [htrace]
  exact Finset.mem_image.mpr ⟨A ∪ D,Finset.mem_filter.mpr
    ⟨hG.2.2.1 hAG hDG,Finset.mem_union_right _ hpD⟩,rfl⟩

theorem trace_subset_decodedSupport_of_actual {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hp : p ∈ sources G)
    (lab : FourTraceLabels (isolated G)) {i j : Label}
    {A : Finset α} (hAG : A ∈ G)
    (hi : lab.point i ∉ A) (hj : lab.point j ∉ A) :
    lab.trace A ⊆ decodedSupport (actualContainingMask G p lab) i.val j.val := by
  simpa only [decode_encode] using
    (decode_subset_decodedSupport (actual_trace_is_safeAvoiding hG hp lab hAG hi hj))

private theorem nonisolated_nonsource_is_leaf {G : Finset (Finset α)} {p a : α}
    (hunique : ∀ q ∈ sources G, q = p)
    (haG : a ∈ ground G) (haI : a ∉ isolated G) (hap : a ≠ p) : a ∈ leaves G := by
  by_contra hn
  have haS : a ∈ sources G := by
    by_contra hnS
    exact haI (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨haG,hn⟩,hnS⟩)
  exact hap (hunique a haS)

/-- Physical support equals leaves plus the realized safe isolate labels
as an upper bound, not as an equality claim about the avoiding family. -/
theorem actual_avoidance_subset_safeSupport {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hp : p ∈ sources G)
    (hunique : ∀ q ∈ sources G, q = p)
    (lab : FourTraceLabels (isolated G)) {i j : Label} {A : Finset α}
    (hA : A ∈ sourcePairAvoiders G p (lab.point i) (lab.point j)) :
    A ⊆ leaves G ∪ lab.realize (decodedSupport (actualContainingMask G p lab) i.val j.val) := by
  obtain ⟨hAG,hpA,hi,hj⟩ := mem_sourcePairAvoiders.mp hA
  have hs := trace_subset_decodedSupport_of_actual hG hp lab hAG hi hj
  intro a ha
  by_cases hI : a ∈ isolated G
  · obtain ⟨k,rfl⟩ := (lab.range_iff a).mp hI
    exact Finset.mem_union_right _ ((lab.mem_realize _ _).mpr
      ⟨k,hs (lab.mem_trace.mpr ha),rfl⟩)
  · exact Finset.mem_union_left _ (nonisolated_nonsource_is_leaf hunique
      (subset_ground hAG ha) hI (fun e => hpA (e ▸ ha)))

private theorem containing_core_subset {G : Finset (Finset α)} {p : α}
    (hp : p ∈ sources G) (hunique : ∀ q ∈ sources G, q = p)
    {D : Finset α} (hD : D ∈ G) (hpD : p ∈ D) :
    ground G \ isolated G ⊆ D := by
  intro a ha
  obtain ⟨haU,haI⟩ := Finset.mem_sdiff.mp ha
  exact unique_source_all_nonisolates_present hp hunique hD hpD haU haI

/-- Safe support and four containing trace ranks force a height-two
capacity bound in the actual pair-avoiding family. -/
theorem actual_pairAvoidance_upper_of_profile_chain {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hp : p ∈ sources G)
    (hunique : ∀ q ∈ sources G, q = p)
    (lab : FourTraceLabels (isolated G)) (i j : Label)
    {c0 c1 c2 c3 : Nat}
    (h0 : c0 ∈ profile (actualContainingMask G p lab))
    (h1 : c1 ∈ profile (actualContainingMask G p lab))
    (h2 : c2 ∈ profile (actualContainingMask G p lab))
    (h3 : c3 ∈ profile (actualContainingMask G p lab))
    (h01 : StrictBitSubset c0 c1) (h12 : StrictBitSubset c1 c2) (h23 : StrictBitSubset c2 c3)
    (hcover : (safeAvoiding (actualContainingMask G p lab) i.val j.val).all
      (fun t => (t &&& c0) == t) = true) :
    (sourcePairAvoiders G p (lab.point i) (lab.point j)).card ≤
      (leaves G).card + (supportBits (actualContainingMask G p lab) i.val j.val).length + 1 := by
  classical
  let m := actualContainingMask G p lab
  let E := sourcePairAvoiders G p (lab.point i) (lab.point j)
  let S := leaves G ∪ lab.realize (decodedSupport m i.val j.val)
  obtain ⟨D0,hd0,hp0,ht0⟩ := containing_member_of_profile hG hp lab h0
  obtain ⟨D1,hd1,hp1,ht1⟩ := containing_member_of_profile hG hp lab h1
  obtain ⟨D2,hd2,hp2,ht2⟩ := containing_member_of_profile hG hp lab h2
  obtain ⟨D3,hd3,hp3,ht3⟩ := containing_member_of_profile hG hp lab h3
  have ht01 : lab.trace D0 ⊂ lab.trace D1 := by
    rw [ht0,ht1]; exact decode_ssubset_of_strictBitSubset (profile_lt_16 h0) (profile_lt_16 h1) h01
  have ht12 : lab.trace D1 ⊂ lab.trace D2 := by
    rw [ht1,ht2]; exact decode_ssubset_of_strictBitSubset (profile_lt_16 h1) (profile_lt_16 h2) h12
  have ht23 : lab.trace D2 ⊂ lab.trace D3 := by
    rw [ht2,ht3]; exact decode_ssubset_of_strictBitSubset (profile_lt_16 h2) (profile_lt_16 h3) h23
  have hD01 := lab.ssubset_of_trace_ssubset (subset_ground hd0)
    (containing_core_subset hp hunique hd1 hp1) ht01
  have hD12 := lab.ssubset_of_trace_ssubset (subset_ground hd1)
    (containing_core_subset hp hunique hd2 hp2) ht12
  have hD23 := lab.ssubset_of_trace_ssubset (subset_ground hd2)
    (containing_core_subset hp hunique hd3 hp3) ht23
  have hbelow : ∀ ⦃A⦄, A ∈ E → A ⊂ D0 := by
    intro A ha
    obtain ⟨hAG,hpA,hi,hj⟩ := mem_sourcePairAvoiders.mp ha
    have ht : lab.trace A ⊆ lab.trace D0 := by
      rw [ht0]
      exact (trace_subset_decodedSupport_of_actual hG hp lab hAG hi hj).trans
        (decodedSupport_subset_bottom hcover)
    exact Finset.ssubset_iff_subset_ne.mpr
      ⟨lab.subset_of_trace_subset (subset_ground hAG) (containing_core_subset hp hunique hd0 hp0) ht,
        fun he => hpA (he.symm ▸ hp0)⟩
  have hH : FranklFiberHeightSix.NoThreeChain E := by
    intro A B C ha hb hc hab hbc
    exact hG.2.2.2.1 (mem_sourcePairAvoiders.mp ha).1 (mem_sourcePairAvoiders.mp hb).1
      (mem_sourcePairAvoiders.mp hc).1 hd0 hd1 hd2 hd3 hab hbc (hbelow hc) hD01 hD12 hD23
  have hU : FranklFiberHeightSix.UnionClosed E := sourcePairAvoiders_unionClosed hG.2.2.1
  have hS : S.card ≤ (leaves G).card + (supportBits m i.val j.val).length := by
    have h := Finset.card_union_le (leaves G) (lab.realize (decodedSupport m i.val j.val))
    rw [lab.realize_card,decodedSupport_card] at h
    exact h
  change E.card ≤ (leaves G).card + (supportBits m i.val j.val).length + 1
  by_cases hne : E.Nonempty
  · obtain ⟨T,hT,hTop⟩ := FranklFiberHeightSix.exists_top hU hne
    have hTC : T.card ≤ S.card :=
      Finset.card_le_card (actual_avoidance_subset_safeSupport hG hp hunique lab hT)
    have hEC := FranklFiberHeightSix.card_le_top_card_add_one hU hH hT hTop
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
    omega

#print axioms actual_trace_is_safeAvoiding
#print axioms trace_subset_decodedSupport_of_actual
#print axioms actual_avoidance_subset_safeSupport
#print axioms actual_pairAvoidance_upper_of_profile_chain
end FranklForcingFiber
