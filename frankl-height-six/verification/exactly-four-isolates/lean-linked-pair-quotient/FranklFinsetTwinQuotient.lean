import FranklTrueComplement

/- Checked by ordinary pinned Lean with warnings treated as errors. -/
namespace FranklFinsetTwinQuotient
variable {α : Type*} [DecidableEq α]

def traceFamily (K : Finset (Finset α)) (R : Finset α) : Finset (Finset α) :=
  K.image (fun A => A ∩ R)

/-- Every dropped coordinate has a retained twin. This is only a
condition on members of K, not a global identification. -/
def HasRetainedTwins (K : Finset (Finset α)) (U R : Finset α) : Prop :=
  ∀ x ∈ U \ R, ∃ y ∈ R, ∀ A ∈ K, x ∈ A ↔ y ∈ A

theorem trace_reflect {K : Finset (Finset α)} {U R A B : Finset α}
    (hU : ∀ C ∈ K, C ⊆ U) (ht : HasRetainedTwins K U R)
    (hA : A ∈ K) (hB : B ∈ K)
    (h : A ∩ R ⊆ B ∩ R) : A ⊆ B := by
  intro x hx
  by_cases hxR : x ∈ R
  · exact (Finset.mem_inter.mp (h (Finset.mem_inter.mpr ⟨hx,hxR⟩))).1
  · obtain ⟨y,hy,hxy⟩ := ht x (Finset.mem_sdiff.mpr ⟨hU A hA hx,hxR⟩)
    have hAy := (hxy A hA).mp hx
    have hBy := (Finset.mem_inter.mp (h (Finset.mem_inter.mpr ⟨hAy,hy⟩))).1
    exact (hxy B hB).mpr hBy

theorem traceFamily_card_eq {K : Finset (Finset α)} {U R : Finset α}
    (hU : ∀ C ∈ K, C ⊆ U) (ht : HasRetainedTwins K U R) :
    (traceFamily K R).card = K.card := by
  apply Finset.card_image_of_injOn
  intro A hA B hB he
  change A ∩ R = B ∩ R at he
  exact Finset.Subset.antisymm
    (trace_reflect hU ht hA hB (by rw [he]))
    (trace_reflect hU ht hB hA (by rw [he]))

theorem traceFamily_unionClosed {K : Finset (Finset α)} {R : Finset α}
    (hK : ∀ ⦃A B⦄, A ∈ K → B ∈ K → A ∪ B ∈ K) :
    ∀ ⦃A B⦄, A ∈ traceFamily K R → B ∈ traceFamily K R → A ∪ B ∈ traceFamily K R := by
  intro A B hA hB
  obtain ⟨A',hA',rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨B',hB',rfl⟩ := Finset.mem_image.mp hB
  exact Finset.mem_image.mpr ⟨A' ∪ B',hK hA' hB',Finset.union_inter_distrib_right _ _ _⟩

theorem traceFamily_noFourChain {K : Finset (Finset α)} {U R : Finset α}
    (hU : ∀ C ∈ K, C ⊆ U) (ht : HasRetainedTwins K U R)
    (hK : FranklHeightThreeSauer.NoFourChain K) :
    FranklHeightThreeSauer.NoFourChain (traceFamily K R) := by
  intro A B C D hA hB hC hD hAB hBC hCD
  obtain ⟨A',hA',rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨B',hB',rfl⟩ := Finset.mem_image.mp hB
  obtain ⟨C',hC',rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨D',hD',rfl⟩ := Finset.mem_image.mp hD
  have lift {P Q : Finset α} (hP : P ∈ K) (hQ : Q ∈ K) (hh : P ∩ R ⊂ Q ∩ R) : P ⊂ Q := by
    obtain ⟨hs,hn⟩ := Finset.ssubset_iff_subset_ne.mp hh
    exact Finset.ssubset_iff_subset_ne.mpr ⟨trace_reflect hU ht hP hQ hs,
      fun e => hn (congrArg (fun X : Finset α => X ∩ R) e)⟩
  exact hK hA' hB' hC' hD' (lift hA' hB' hAB) (lift hB' hC' hBC)
    (lift hC' hD' hCD)

theorem traceFamily_subset {K : Finset (Finset α)} {R A : Finset α}
    (hA : A ∈ traceFamily K R) : A ⊆ R := by
  obtain ⟨B,_,rfl⟩ := Finset.mem_image.mp hA
  exact Finset.inter_subset_right

theorem traceFamily_contains_support {K : Finset (Finset α)} {U R : Finset α}
    (hR : R ⊆ U) (hU : U ∈ K) : R ∈ traceFamily K R := by
  exact Finset.mem_image.mpr ⟨U,hU,Finset.inter_eq_right.mpr hR⟩

/-- A trace that deletes only marked coordinates lifts to the same
omission before quotienting, if no chosen twin is a marked coordinate. -/
theorem top_sdiff_mem_of_trace {K : Finset (Finset α)} {U R I J : Finset α}
    (hU : ∀ C ∈ K, C ⊆ U) (hR : R ⊆ U) (hJI : J ⊆ I) (hJR : J ⊆ R)
    (ht : ∀ x ∈ U \ R, ∃ y ∈ R \ I, ∀ A ∈ K, x ∈ A ↔ y ∈ A)
    (hJ : R \ J ∈ traceFamily K R) : U \ J ∈ K := by
  obtain ⟨A,hA,hTrace⟩ := Finset.mem_image.mp hJ
  have hEq : A = U \ J := by
    ext x
    by_cases hxR : x ∈ R
    · have hx : x ∈ A ↔ x ∈ A ∩ R := by simp [hxR]
      rw [hx,hTrace]
      exact ⟨fun hx' => Finset.mem_sdiff.mpr ⟨hR (Finset.mem_sdiff.mp hx').1,(Finset.mem_sdiff.mp hx').2⟩,
        fun hx' => Finset.mem_sdiff.mpr ⟨hxR,(Finset.mem_sdiff.mp hx').2⟩⟩
    · by_cases hxU : x ∈ U
      · obtain ⟨y,hy,hxy⟩ := ht x (Finset.mem_sdiff.mpr ⟨hxU,hxR⟩)
        obtain ⟨hyR,hyI⟩ := Finset.mem_sdiff.mp hy
        have hyTrace : y ∈ R \ J := Finset.mem_sdiff.mpr ⟨hyR,fun h => hyI (hJI h)⟩
        have hyA : y ∈ A := (Finset.mem_inter.mp (hTrace.symm ▸ hyTrace)).1
        have hxA := (hxy A hA).mpr hyA
        have hxJ : x ∉ J := fun h => hxR (hJR h)
        exact ⟨fun _ => Finset.mem_sdiff.mpr ⟨hxU,hxJ⟩,fun _ => hxA⟩
      · exact ⟨fun h => False.elim (hxU (hU A hA h)),
          fun h => False.elim (hxU (Finset.mem_sdiff.mp h).1)⟩
  exact hEq ▸ hA

#print axioms traceFamily_card_eq
#print axioms traceFamily_noFourChain
#print axioms top_sdiff_mem_of_trace
end FranklFinsetTwinQuotient
