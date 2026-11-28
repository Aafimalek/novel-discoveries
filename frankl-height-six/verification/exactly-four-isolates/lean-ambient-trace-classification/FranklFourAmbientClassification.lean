import FranklFourAmbientTrace
import FranklFourTraceCertificates
import FranklMissingDeletionApplication

namespace FranklForcingFiber
open FranklFourTraceCertificate

variable {α : Type*} [DecidableEq α]

private theorem survivor_nonzero_label_freq :
    ∀ i : Label, i ≠ 0 → traceFrequency 2045 i.val = 8 := by
  decide

/-- Under the one-source exactly-four hypotheses, the checked numeric
classification applies to the actual containing fiber. Its exceptional
mask gives the explicit original 15/7/at-least-8 profile. -/
theorem containingTrace_witness_or_survivor {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hunique : ∀ q ∈ sources G, q = p)
    (hI : (isolated G).card = 4) :
    ∃ lab : FourTraceLabels (isolated G),
      (∃ w, WitnessSpec (familyMask (containingTraces G p lab)) w) ∨
      ((G.filter (p ∈ ·)).card = 15 ∧
        frequency (G.filter (p ∈ ·)) (lab.point 0) = 7 ∧
        ∀ v ∈ ground G, v ≠ lab.point 0 → 8 ≤ frequency (G.filter (p ∈ ·)) v) := by
  classical
  obtain ⟨lab,helig⟩ := exists_eligible_containingTraceMask hG hmin hp hunique hI
  refine ⟨lab,?_⟩
  let F := containingTraces G p lab
  let m := familyMask F
  let P := G.filter (p ∈ ·)
  have hm : m < 2048 := familyMask_lt F
  have hmand := containingTraces_mandatory hG hp lab
  change eligibleB m = true at helig
  rcases classified_mask m hm helig with hsurv | ⟨w,hvalid⟩
  · right
    obtain ⟨_,_,hPC,hfx,_,_,_⟩ := survivor_profile
    have hcard : P.card = (profile m).length :=
      (containingTraces_card hp hunique lab).symm.trans (card_familyMask_profile hmand)
    have hfreq (i : Label) : frequency P (lab.point i) = traceFrequency m i.val :=
      (containingTraces_frequency hp hunique lab i).symm.trans
        (frequency_familyMask_profile i hmand)
    have hc : P.card = 15 := hcard.trans (hsurv.symm ▸ hPC)
    have hx : frequency P (lab.point 0) = 7 := by
      rw [hfreq 0,hsurv]
      exact hfx
    refine ⟨hc,hx,?_⟩
    intro v hv hne
    by_cases hvI : v ∈ isolated G
    · obtain ⟨i,rfl⟩ := (lab.range_iff v).mp hvI
      have hi : i ≠ 0 := fun e => hne (congrArg lab.point e)
      rw [hfreq i,hsurv,survivor_nonzero_label_freq i hi]
    · have he : P.filter (v ∈ ·) = P := by
        apply Finset.filter_eq_self.mpr
        intro A ha
        obtain ⟨haG,hpa⟩ := Finset.mem_filter.mp ha
        exact unique_source_all_nonisolates_present hp hunique haG hpa hv hvI
      change 8 ≤ (P.filter (v ∈ ·)).card
      rw [he,hc]
      decide
  · exact Or.inl ⟨w,witness_spec_of_valid hvalid⟩

/-- The repaired 15-trace profile cannot survive minimality, hence one
of the certified numeric witnesses must occur. The actual avoidance
contradiction for its witness is a separate geometric/counting step. -/
theorem exists_containingTrace_witness_of_exact_four {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hunique : ∀ q ∈ sources G, q = p)
    (hI : (isolated G).card = 4) :
    ∃ lab : FourTraceLabels (isolated G),
      ∃ w, WitnessSpec (familyMask (containingTraces G p lab)) w := by
  obtain ⟨lab,hw | ⟨hcard,hfreq,hother⟩⟩ :=
    containingTrace_witness_or_survivor hG hmin hp hunique hI
  · exact ⟨lab,hw⟩
  · exact False.elim (no_containing_profile_fifteen_seven_eight hG hmin
      (mem_sources.mp hp).1 hcard hfreq hother)

#print axioms containingTrace_witness_or_survivor
#print axioms exists_containingTrace_witness_of_exact_four
end FranklForcingFiber
