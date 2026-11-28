import FranklFourAvoidanceGeometry

/- Kernel-checked on pinned Lean 4.36 and Mathlib. -/
namespace FranklForcingFiber
open FranklFourTraceCertificate

variable {α : Type*} [DecidableEq α]

def sourcePairContainers (G : Finset (Finset α)) (p y z : α) : Finset (Finset α) :=
  (sourceAvoiders G p).filter (fun A => y ∈ A ∧ z ∈ A)

/-- The source and each leaf index different avoidance maxima, each
of which avoids the source and contains both isolated anchors. -/
theorem coLeaf_sourcePairContainers_lower
    {G : Finset (Finset α)} {p y z : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hunique : ∀ q ∈ sources G, q = p)
    (hy : y ∈ isolated G) (hz : z ∈ isolated G) :
    (leaves G).card + 1 ≤ (sourcePairContainers G p y z).card := by
  classical
  let K := insert p (leaves G)
  have hpL : p ∉ leaves G :=
    (Finset.mem_sdiff.mp (sources_subset_nonleaf hG hmin hp)).2
  have hKcard : K.card = (leaves G).card + 1 :=
    Finset.card_insert_of_notMem hpL
  have hKsub : K ⊆ ground G := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hl
    · exact (mem_sources.mp hp).1
    · exact (mem_leaves.mp hl).1
  have hKnotIso {v : α} (hI : v ∈ isolated G) : v ∉ K := by
    intro h
    rcases Finset.mem_insert.mp h with hvp | hvL
    · have hpI : p ∈ isolated G := hvp ▸ hI
      exact (Finset.mem_sdiff.mp hpI).2 hp
    · exact (mem_isolated.mp hI).2.2 hvL
  have hmap : Set.MapsTo (avoid G) (K : Set α) (sourcePairContainers G p y z : Set (Finset α)) := by
    intro w hw
    have hwK : w ∈ K := hw
    have hwp : p ∉ avoid G w := by
      rcases Finset.mem_insert.mp hwK with rfl | hwL
      · exact notMem_avoid G _
      · obtain ⟨q,hq,hqw,hF⟩ := (mem_leaves.mp hwL).2
        have hqP : q = p := hunique q (mem_sources.mpr ⟨hq,w,hqw,hF⟩)
        exact (notMem_avoid_iff_forces G w p).mpr (hqP ▸ hF)
    have hcontains {v : α} (hI : v ∈ isolated G) : v ∈ avoid G w := by
      by_contra hn
      have he : w = v := (mem_isolated.mp hI).2.1 ((notMem_avoid_iff_forces G w v).mp hn)
      exact hKnotIso hI (he ▸ hwK)
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨avoid_mem_weak hG w,hwp⟩,
      hcontains hy,hcontains hz⟩
  have hinj : Set.InjOn (avoid G) (K : Set α) := by
    intro u hu v hv he
    exact avoid_injOn_ground (weakMinimalGround_separated hG hmin) (hKsub hu) (hKsub hv) he
  have h := Finset.card_le_card_of_injOn (avoid G) hmap hinj
  rwa [hKcard] at h

/-- Sum both global weak frequency inequalities and split at p.
The result is the additive, subtraction-free pair incidence bound. -/
theorem sourcePairAvoiders_incidence_add {G : Finset (Finset α)} {p y z : α}
    (hG : NoStrictMajority G) :
    (sourcePairContainers G p y z).card +
      frequency (G.filter (p ∈ ·)) y + frequency (G.filter (p ∈ ·)) z ≤
      (sourcePairAvoiders G p y z).card + (G.filter (p ∈ ·)).card := by
  let P := G.filter (p ∈ ·)
  let B := sourceAvoiders G p
  let BY := B.filter (y ∈ ·)
  let BZ := B.filter (z ∈ ·)
  let O := B.filter (fun A => y ∈ A ∨ z ∈ A)
  let C := sourcePairContainers G p y z
  let E := sourcePairAvoiders G p y z
  have hu : BY ∪ BZ = O := by
    ext A
    simp only [BY,BZ,O,Finset.mem_union,Finset.mem_filter]
    tauto
  have hi : BY ∩ BZ = C := by
    ext A
    simp only [BY,BZ,B,C,sourcePairContainers,Finset.mem_inter,Finset.mem_filter]
    tauto
  have hCO := Finset.card_union_add_card_inter BY BZ
  rw [hu,hi] at hCO
  have hEO : O.card + E.card = B.card :=
    Finset.card_filter_add_card_filter_not (s := B) (fun A => y ∈ A ∨ z ∈ A)
  have hPB : P.card + B.card = G.card :=
    Finset.card_filter_add_card_filter_not (p ∈ ·)
  have hfy := frequency_partition_by_point G p y
  have hfz := frequency_partition_by_point G p z
  change frequency P y + BY.card = frequency G y at hfy
  change frequency P z + BZ.card = frequency G z at hfz
  have hy := hG.2.2.2.2 y
  have hz := hG.2.2.2.2 z
  change C.card + frequency P y + frequency P z ≤ E.card + P.card
  omega

/-- A checked numeric exclusion witness cannot occur in an actual family. -/
theorem no_actual_containingTrace_witness {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hunique : ∀ q ∈ sources G, q = p)
    (lab : FourTraceLabels (isolated G)) {w : Witness}
    (hw : WitnessSpec (actualContainingMask G p lab) w) : False := by
  classical
  obtain ⟨hij,hj4,hs,h0,h1,h2,h3,h01,h12,h23,hcover⟩ := hw
  let i : Label := ⟨w.i,hij.trans hj4⟩
  let j : Label := ⟨w.j,hj4⟩
  let m := actualContainingMask G p lab
  let P := G.filter (p ∈ ·)
  let E := sourcePairAvoiders G p (lab.point i) (lab.point j)
  let C := sourcePairContainers G p (lab.point i) (lab.point j)
  let s := (supportBits m i.val j.val).length
  have hUpper : E.card ≤ (leaves G).card + s + 1 :=
    actual_pairAvoidance_upper_of_profile_chain hG hp hunique lab i j h0 h1 h2 h3 h01 h12 h23 hcover
  have hLower : (leaves G).card + 1 ≤ C.card :=
    coLeaf_sourcePairContainers_lower hG hmin hp hunique (lab.point_mem i) (lab.point_mem j)
  have hInc : C.card + frequency P (lab.point i) + frequency P (lab.point j) ≤ E.card + P.card :=
    sourcePairAvoiders_incidence_add hG
  have hmand := containingTraces_mandatory hG hp lab
  have hcard : P.card = (profile m).length :=
    (containingTraces_card hp hunique lab).symm.trans (card_familyMask_profile hmand)
  have hf (k : Label) : frequency P (lab.point k) = traceFrequency m k.val :=
    (containingTraces_frequency hp hunique lab k).symm.trans (frequency_familyMask_profile k hmand)
  change s + (profile m).length < traceFrequency m i.val + traceFrequency m j.val at hs
  rw [←hcard,←hf i,←hf j] at hs
  omega

/-- Arbitrary-ambient exact-four, one-source contradiction. This theorem
is not the separate multiple-source case or the full at-least-five bound. -/
theorem unique_source_not_exact_four_isolates {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hunique : ∀ q ∈ sources G, q = p)
    (hI : (isolated G).card = 4) : False := by
  obtain ⟨lab,w,hw⟩ := exists_containingTrace_witness_of_exact_four hG hmin hp hunique hI
  exact no_actual_containingTrace_witness hG hmin hp hunique lab hw

#print axioms coLeaf_sourcePairContainers_lower
#print axioms sourcePairAvoiders_incidence_add
#print axioms no_actual_containingTrace_witness
#print axioms unique_source_not_exact_four_isolates
end FranklForcingFiber
