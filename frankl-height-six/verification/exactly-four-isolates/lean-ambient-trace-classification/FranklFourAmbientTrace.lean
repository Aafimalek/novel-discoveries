import FranklFourTraceMaskBridge
import FranklFewIsolates
import Mathlib.Logic.Equiv.Basic

/- Kernel-checked with pinned Lean 4.36 and Mathlib. -/
namespace FranklForcingFiber
open FranklFourTraceCertificate

variable {α : Type*} [DecidableEq α]

/-- A labeled four-point subset of an arbitrary ambient type. -/
structure FourTraceLabels (I : Finset α) where
  point : Label ↪ α
  range_iff : ∀ a : α, a ∈ I ↔ ∃ i : Label, point i = a

namespace FourTraceLabels
variable {I : Finset α} (lab : FourTraceLabels I)

omit [DecidableEq α] in
theorem point_mem (i : Label) : lab.point i ∈ I :=
  (lab.range_iff _).mpr ⟨i,rfl⟩

omit [DecidableEq α] in
/-- A prescribed point goes at label zero. No ambient ordering is needed. -/
theorem exists_zero_label {x : α} (hx : x ∈ I) (hI : I.card = 4) :
    ∃ lab : FourTraceLabels I, lab.point 0 = x := by
  classical
  have hcard : Fintype.card (↥I) = 4 := by simpa using hI
  let e : (↥I) ≃ Label := Fintype.equivFinOfCardEq hcard
  let xI : ↥I := ⟨x,hx⟩
  let g : Label ≃ (↥I) := (Equiv.swap 0 (e xI)).trans e.symm
  let emb : Label ↪ α := g.toEmbedding.trans (Function.Embedding.subtype (· ∈ I))
  have hzero : g 0 = xI := by
    change e.symm ((Equiv.swap 0 (e xI)) 0) = xI
    rw [Equiv.swap_apply_left]
    exact e.symm_apply_apply xI
  refine ⟨⟨emb,?_⟩,?_⟩
  · intro a
    constructor
    · intro ha
      refine ⟨g.symm ⟨a,ha⟩,?_⟩
      change (g (g.symm ⟨a,ha⟩)).val = a
      rw [g.apply_symm_apply]
    · rintro ⟨i,hi⟩
      change (g i).val = a at hi
      exact hi ▸ (g i).property
  · change (g 0).val = x
    rw [hzero]

/-- Keep just isolate membership, indexed by the four coordinate labels. -/
def trace (A : Finset α) : Trace :=
  Finset.univ.filter (fun i : Label => lab.point i ∈ A)

@[simp] theorem mem_trace {i : Label} {A : Finset α} :
    i ∈ lab.trace A ↔ lab.point i ∈ A := by
  simp [trace]

@[simp] theorem trace_union (A B : Finset α) :
    lab.trace (A ∪ B) = lab.trace A ∪ lab.trace B := by
  ext i
  simp [Finset.mem_union]

theorem trace_mono {A B : Finset α} (h : A ⊆ B) :
    lab.trace A ⊆ lab.trace B :=
  fun _ hi => lab.mem_trace.mpr (h (lab.mem_trace.mp hi))

@[simp] theorem trace_eq_univ_of_subset {A : Finset α} (h : I ⊆ A) :
    lab.trace A = Finset.univ := by
  ext i
  simp [h (lab.point_mem i)]

@[simp] theorem trace_erase_point (A : Finset α) (i : Label) :
    lab.trace (A.erase (lab.point i)) = (lab.trace A).erase i := by
  ext j
  simp only [mem_trace,Finset.mem_erase]
  exact and_congr (not_congr lab.point.injective.eq_iff) Iff.rfl

/-- Given a full common core in the upper set, inclusion of the
remaining labeled coordinates suffices to lift inclusion. -/
theorem subset_of_trace_subset {U A D : Finset α}
    (hAU : A ⊆ U) (hDcore : U \ I ⊆ D)
    (htr : lab.trace A ⊆ lab.trace D) : A ⊆ D := by
  intro a ha
  by_cases hI : a ∈ I
  · obtain ⟨i,rfl⟩ := (lab.range_iff _).mp hI
    exact lab.mem_trace.mp (htr (lab.mem_trace.mpr ha))
  · exact hDcore (Finset.mem_sdiff.mpr ⟨hAU ha,hI⟩)

theorem ssubset_of_trace_ssubset {U A D : Finset α}
    (hAU : A ⊆ U) (hDcore : U \ I ⊆ D)
    (htr : lab.trace A ⊂ lab.trace D) : A ⊂ D := by
  obtain ⟨hs,hn⟩ := Finset.ssubset_iff_subset_ne.mp htr
  exact Finset.ssubset_iff_subset_ne.mpr
    ⟨lab.subset_of_trace_subset hAU hDcore hs,fun he => hn (congrArg lab.trace he)⟩

/-- Trace is injective whenever the ambient domain and the outside core
are fixed. -/
theorem trace_injOn_of_core {Q : Finset (Finset α)} {U : Finset α}
    (hU : ∀ ⦃A⦄, A ∈ Q → A ⊆ U)
    (hcore : ∀ ⦃A⦄, A ∈ Q → U \ I ⊆ A) :
    Set.InjOn lab.trace (Q : Set (Finset α)) := by
  intro A ha D hd he
  have hAQ : A ∈ Q := ha
  have hDQ : D ∈ Q := hd
  have hAD : lab.trace A ⊆ lab.trace D := by simp [he]
  have hDA : lab.trace D ⊆ lab.trace A := by simp [he]
  exact Finset.Subset.antisymm
    (lab.subset_of_trace_subset (hU hAQ) (hcore hDQ) hAD)
    (lab.subset_of_trace_subset (hU hDQ) (hcore hAQ) hDA)

theorem traceImage_filter (Q : Finset (Finset α)) (i : Label) :
    (Q.image lab.trace).filter (i ∈ ·) =
      (Q.filter (lab.point i ∈ ·)).image lab.trace := by
  ext R
  constructor
  · intro h
    obtain ⟨ht,hi⟩ := Finset.mem_filter.mp h
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_image.mpr ⟨A,Finset.mem_filter.mpr ⟨hA,lab.mem_trace.mp hi⟩,rfl⟩
  · intro h
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hA',hi⟩ := Finset.mem_filter.mp hA
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨A,hA',rfl⟩,lab.mem_trace.mpr hi⟩

theorem traceImage_frequency {Q : Finset (Finset α)}
    (hinj : Set.InjOn lab.trace (Q : Set (Finset α))) (i : Label) :
    ((Q.image lab.trace).filter (i ∈ ·)).card = frequency Q (lab.point i) := by
  have hf : Set.InjOn lab.trace ((Q.filter (lab.point i ∈ ·)) : Set (Finset α)) := by
    intro A ha D hd he
    have hA : A ∈ Q.filter (lab.point i ∈ ·) := ha
    have hD : D ∈ Q.filter (lab.point i ∈ ·) := hd
    exact hinj (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hD).1 he
  change ((Q.image lab.trace).filter (i ∈ ·)).card = (Q.filter (lab.point i ∈ ·)).card
  rw [lab.traceImage_filter,Finset.card_image_of_injOn hf]

/-- Physical support corresponding to a set of labels. -/
def realize (R : Trace) : Finset α := R.map lab.point

omit [DecidableEq α] in
theorem realize_card (R : Trace) : (lab.realize R).card = R.card := by
  simp [realize]

omit [DecidableEq α] in
theorem mem_realize (R : Trace) (a : α) :
    a ∈ lab.realize R ↔ ∃ i ∈ R, lab.point i = a := Finset.mem_map

omit [DecidableEq α] in
theorem realize_subset_isolates (R : Trace) : lab.realize R ⊆ I := by
  intro a ha
  obtain ⟨i,_,rfl⟩ := (lab.mem_realize _ _).mp ha
  exact lab.point_mem i

theorem mem_realize_of_mem_isolates {A : Finset α} {a : α}
    (haI : a ∈ I) (haA : a ∈ A) :
    a ∈ lab.realize (lab.trace A) := by
  obtain ⟨i,rfl⟩ := (lab.range_iff _).mp haI
  exact (lab.mem_realize _ _).mpr ⟨i,lab.mem_trace.mpr haA,rfl⟩

end FourTraceLabels

/-- The actual containing fiber's image on labeled isolate traces. -/
noncomputable def containingTraces (G : Finset (Finset α)) (p : α)
    (lab : FourTraceLabels (isolated G)) : Finset Trace :=
  (G.filter (p ∈ ·)).image lab.trace

theorem containing_trace_injOn {G : Finset (Finset α)} {p : α}
    (hp : p ∈ sources G) (hunique : ∀ q ∈ sources G, q = p)
    (lab : FourTraceLabels (isolated G)) :
    Set.InjOn lab.trace ((G.filter (p ∈ ·)) : Set (Finset α)) := by
  apply lab.trace_injOn_of_core (U := ground G)
  · intro A ha
    exact subset_ground (Finset.mem_filter.mp ha).1
  · intro A ha a haCore
    obtain ⟨haG,hpA⟩ := Finset.mem_filter.mp ha
    obtain ⟨haU,haI⟩ := Finset.mem_sdiff.mp haCore
    exact unique_source_all_nonisolates_present hp hunique haG hpA haU haI

theorem containingTraces_card {G : Finset (Finset α)} {p : α}
    (hp : p ∈ sources G) (hunique : ∀ q ∈ sources G, q = p)
    (lab : FourTraceLabels (isolated G)) :
    (containingTraces G p lab).card = (G.filter (p ∈ ·)).card :=
  Finset.card_image_of_injOn (containing_trace_injOn hp hunique lab)

theorem containingTraces_frequency {G : Finset (Finset α)} {p : α}
    (hp : p ∈ sources G) (hunique : ∀ q ∈ sources G, q = p)
    (lab : FourTraceLabels (isolated G)) (i : Label) :
    ((containingTraces G p lab).filter (i ∈ ·)).card =
      frequency (G.filter (p ∈ ·)) (lab.point i) :=
  lab.traceImage_frequency (containing_trace_injOn hp hunique lab) i

theorem containingTraces_unionClosed {G : Finset (Finset α)} {p : α}
    (hU : UnionClosed G) (lab : FourTraceLabels (isolated G)) :
    ∀ ⦃R S⦄, R ∈ containingTraces G p lab → S ∈ containingTraces G p lab →
      R ∪ S ∈ containingTraces G p lab := by
  intro R S hr hs
  obtain ⟨A,ha,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨B,hb,rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨haG,hpA⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbG,_⟩ := Finset.mem_filter.mp hb
  exact Finset.mem_image.mpr ⟨A ∪ B,Finset.mem_filter.mpr
    ⟨hU haG hbG,Finset.mem_union_left _ hpA⟩,lab.trace_union _ _⟩

private theorem card_three_trace_cases :
    ∀ R : Trace, 3 ≤ R.card →
      R = Finset.univ ∨ ∃ i : Label, R = (Finset.univ : Trace).erase i := by
  decide

theorem containingTraces_mandatory {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hp : p ∈ sources G)
    (lab : FourTraceLabels (isolated G)) :
    ∀ R : Trace, 3 ≤ R.card → R ∈ containingTraces G p lab := by
  intro R hR
  have hpU := (mem_sources.mp hp).1
  have hI : isolated G ⊆ ground G := fun _ h => (mem_isolated.mp h).1
  have htop : lab.trace (ground G) = Finset.univ := lab.trace_eq_univ_of_subset hI
  rcases card_three_trace_cases R hR with rfl | ⟨i,rfl⟩
  · exact Finset.mem_image.mpr ⟨ground G,Finset.mem_filter.mpr ⟨ground_mem_weak hG,hpU⟩,htop⟩
  · have hi := lab.point_mem i
    have hne : p ≠ lab.point i := by
      intro he
      have hpI : p ∈ isolated G := he.symm ▸ hi
      exact (Finset.mem_sdiff.mp hpI).2 hp
    refine Finset.mem_image.mpr ⟨(ground G).erase (lab.point i),
      Finset.mem_filter.mpr ⟨isolated_coSingleton_mem hG hi,Finset.mem_erase.mpr ⟨hne,hpU⟩⟩,?_⟩
    rw [lab.trace_erase_point,htop]

theorem exists_low_isolate_for_unique_source {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hunique : ∀ q ∈ sources G, q = p) :
    ∃ x ∈ isolated G, 2 * frequency (G.filter (p ∈ ·)) x < (G.filter (p ∈ ·)).card := by
  classical
  obtain ⟨x,hx,hLow⟩ := exists_low_frequency_in_containing_fiber hG hmin (mem_sources.mp hp).1
  refine ⟨x,?_,hLow⟩
  by_contra hn
  have he : (G.filter (p ∈ ·)).filter (x ∈ ·) = G.filter (p ∈ ·) := by
    apply Finset.filter_eq_self.mpr
    intro A ha
    obtain ⟨haG,hpa⟩ := Finset.mem_filter.mp ha
    exact unique_source_all_nonisolates_present hp hunique haG hpa hx hn
  change 2 * ((G.filter (p ∈ ·)).filter (x ∈ ·)).card < (G.filter (p ∈ ·)).card at hLow
  rw [he] at hLow
  omega

/-- End of the arbitrary-ambient eligibility transfer. The mask is
the canonical symbolic pack of the actual containing trace family. -/
theorem exists_eligible_containingTraceMask {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hunique : ∀ q ∈ sources G, q = p)
    (hI : (isolated G).card = 4) :
    ∃ lab : FourTraceLabels (isolated G),
      eligibleB (familyMask (containingTraces G p lab)) = true := by
  obtain ⟨x,hx,hLow⟩ := exists_low_isolate_for_unique_source hG hmin hp hunique
  obtain ⟨lab,h0⟩ := FourTraceLabels.exists_zero_label hx hI
  refine ⟨lab,familyMask_eligible (containingTraces_mandatory hG hp lab)
    (containingTraces_unionClosed hG.2.2.1 lab) ?_⟩
  rw [containingTraces_frequency hp hunique lab, containingTraces_card hp hunique lab,h0]
  exact hLow

#print axioms FourTraceLabels.exists_zero_label
#print axioms FourTraceLabels.trace_union
#print axioms FourTraceLabels.ssubset_of_trace_ssubset
#print axioms FourTraceLabels.traceImage_frequency
#print axioms containingTraces_card
#print axioms containingTraces_frequency
#print axioms containingTraces_mandatory
#print axioms exists_eligible_containingTraceMask
end FranklForcingFiber
