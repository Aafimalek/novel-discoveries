import FranklHeightThreeSauer

namespace FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

def incidenceSignature (N : Finset (Finset α)) (x : α) : Finset (Finset α) := N.filter (x ∈ ·)

abbrev SignatureCoordinate (α : Type*) := Sum (Finset (Finset α)) α

def signatureProjection (N : Finset (Finset α)) (E I A : Finset α) :
    Finset (SignatureCoordinate α) :=
  ((A ∩ E).image (fun x => Sum.inl (incidenceSignature N x))) ∪
  ((A ∩ I).image Sum.inr)

theorem signatureProjection_union (N : Finset (Finset α)) (E I A B : Finset α) :
    signatureProjection N E I (A ∪ B) =
      signatureProjection N E I A ∪ signatureProjection N E I B := by
  unfold signatureProjection
  rw [Finset.union_inter_distrib_right, Finset.union_inter_distrib_right,
    Finset.image_union, Finset.image_union]
  ext y
  simp only [Finset.mem_union]
  tauto

theorem signatureProjection_reflect {N : Finset (Finset α)} {E I A B : Finset α}
    (_hA : A ∈ N) (hB : B ∈ N) (hAs : A ⊆ E ∪ I)
    (h : signatureProjection N E I A ⊆ signatureProjection N E I B) : A ⊆ B := by
  intro x hx
  rcases Finset.mem_union.mp (hAs hx) with hxE | hxI
  · have hxA : (Sum.inl (incidenceSignature N x) : SignatureCoordinate α) ∈ signatureProjection N E I A :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨x,Finset.mem_inter.mpr ⟨hx,hxE⟩,rfl⟩))
    rcases Finset.mem_union.mp (h hxA) with hy | hy
    · obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hy
      have hSig := Sum.inl.inj he
      have hB_y : B ∈ incidenceSignature N y := Finset.mem_filter.mpr ⟨hB,(Finset.mem_inter.mp hy).1⟩
      exact (Finset.mem_filter.mp (show B ∈ incidenceSignature N x from hSig ▸ hB_y)).2
    · obtain ⟨y,_,he⟩ := Finset.mem_image.mp hy
      cases he
  · have hxA : (Sum.inr x : SignatureCoordinate α) ∈ signatureProjection N E I A :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨x,Finset.mem_inter.mpr ⟨hx,hxI⟩,rfl⟩))
    rcases Finset.mem_union.mp (h hxA) with hy | hy
    · obtain ⟨y,_,he⟩ := Finset.mem_image.mp hy
      cases he
    · obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hy
      exact Sum.inr.inj he ▸ (Finset.mem_inter.mp hy).1

/-- Signature compression: retain one incidence signature per class and the
individual points in I; this improves the old power-set cap to Sauer. -/
theorem family_card_le_sauer_signatures
    {N : Finset (Finset α)} {E I : Finset α}
    (hU : ∀ ⦃A B⦄, A ∈ N → B ∈ N → A ∪ B ∈ N)
    (hH : FranklHeightThreeSauer.NoFourChain N)
    (hNI : ∀ A ∈ N, A ⊆ E ∪ I) :
    let m := (E.image (incidenceSignature N)).card + I.card
    N.card ≤ 1 + m + m.choose 2 := by
  let f := signatureProjection N E I
  let L := N.image f
  let T : Finset (SignatureCoordinate α) :=
    (E.image (fun x => Sum.inl (incidenceSignature N x))) ∪ (I.image Sum.inr)
  have hinj : Set.InjOn f (N : Set (Finset α)) := by
    intro A hA B hB he
    have hAB : f A ⊆ f B := by rw [he]
    have hBA : f B ⊆ f A := by rw [he]
    exact Finset.Subset.antisymm
      (signatureProjection_reflect hA hB (hNI A hA) hAB)
      (signatureProjection_reflect hB hA (hNI B hB) hBA)
  have hcard : L.card = N.card := Finset.card_image_of_injOn hinj
  have hLU : ∀ ⦃A B⦄, A ∈ L → B ∈ L → A ∪ B ∈ L := by
    intro A B hA hB
    obtain ⟨A',hA',rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨B',hB',rfl⟩ := Finset.mem_image.mp hB
    exact Finset.mem_image.mpr ⟨A' ∪ B',hU hA' hB',signatureProjection_union N E I A' B'⟩
  have hLH : FranklHeightThreeSauer.NoFourChain L := by
    intro A B C D hA hB hC hD hAB hBC hCD
    obtain ⟨A',hA',rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨B',hB',rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨C',hC',rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨D',hD',rfl⟩ := Finset.mem_image.mp hD
    have hLift {P Q : Finset α} (hP : P ∈ N) (hQ : Q ∈ N) (hPQ : f P ⊂ f Q) :
        P ⊂ Q := by
      obtain ⟨hsub,hne⟩ := Finset.ssubset_iff_subset_ne.mp hPQ
      exact Finset.ssubset_iff_subset_ne.mpr
        ⟨signatureProjection_reflect hP hQ (hNI P hP) hsub,fun e => hne (congrArg f e)⟩
    exact hH hA' hB' hC' hD' (hLift hA' hB' hAB) (hLift hB' hC' hBC) (hLift hC' hD' hCD)
  have hLT : ∀ ⦃A⦄, A ∈ L → A ⊆ T := by
    intro A hA
    obtain ⟨B,_,rfl⟩ := Finset.mem_image.mp hA
    exact Finset.union_subset_union (Finset.image_subset_image Finset.inter_subset_right)
      (Finset.image_subset_image Finset.inter_subset_right)
  have hT : T.card ≤ (E.image (incidenceSignature N)).card + I.card := by
    have hA : (E.image (fun x => (Sum.inl (incidenceSignature N x) : SignatureCoordinate α))).card ≤
        (E.image (incidenceSignature N)).card := by
      change (E.image ((Sum.inl : Finset (Finset α) → SignatureCoordinate α) ∘
        incidenceSignature N)).card ≤ _
      rw [← Finset.image_image]
      exact Finset.card_image_le
    have hB : (I.image (Sum.inr : α → SignatureCoordinate α)).card ≤ I.card := Finset.card_image_le
    have h := Finset.card_union_le
      (E.image (fun x => (Sum.inl (incidenceSignature N x) : SignatureCoordinate α)))
      (I.image (Sum.inr : α → SignatureCoordinate α))
    change T.card ≤ _ at h
    omega
  have hUpper := FranklHeightThreeSauer.card_le T hLU hLH hLT
  have hChoose := Nat.choose_le_choose 2 hT
  dsimp
  omega

#print axioms family_card_le_sauer_signatures

end FranklBlockIncidence
