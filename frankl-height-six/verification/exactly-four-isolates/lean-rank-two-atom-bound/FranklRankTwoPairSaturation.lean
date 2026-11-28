import FranklRankTwoAtomCounting

namespace FranklRankTwoAtoms
variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem singleton_isAtom_of_mem {D : Finset (Finset α)} {x : α}
    (hx : ({x} : Finset α) ∈ D) : IsAtom D {x} := by
  refine ⟨hx,⟨x,Finset.mem_singleton_self x⟩,?_⟩
  intro T _ hTN hsub
  obtain ⟨y,hy⟩ := hTN
  have he : y = x := Finset.mem_singleton.mp (hsub hy)
  exact Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr (he ▸ hy))

omit [DecidableEq α] in
theorem line_card_ge_two {D : Finset (Finset α)} {A : Finset α}
    (hA : IsLine D A) : 2 ≤ A.card := by
  have h0 := Finset.card_pos.mpr hA.2.1
  by_contra hn
  have h1 : A.card = 1 := by omega
  obtain ⟨x,rfl⟩ := Finset.card_eq_one.mp h1
  exact hA.2.2 (singleton_isAtom_of_mem hA.1)

private theorem atoms_eq_singletons_of_mem_all {D : Finset (Finset α)} {U : Finset α}
    (hS : ∀ ⦃A⦄, A ∈ D → A ⊆ U)
    (hSing : ∀ x ∈ U, ({x} : Finset α) ∈ D) :
    atoms D = U.image (fun x => ({x} : Finset α)) := by
  ext A
  constructor
  · intro ha
    have hat := mem_atoms.mp ha
    obtain ⟨x,hx⟩ := hat.2.1
    have hxU := hS hat.1 hx
    have he : ({x} : Finset α) = A :=
      hat.2.2 (hSing x hxU) ⟨x,Finset.mem_singleton_self x⟩
        (Finset.singleton_subset_iff.mpr hx)
    exact Finset.mem_image.mpr ⟨x,hxU,he⟩
  · intro hA
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hA
    exact mem_atoms.mpr (singleton_isAtom_of_mem (hSing x hx))

/-- When the rank-two bound is saturated with all singleton atoms,
every two-point support subset is itself a family member. -/
theorem pair_mem_of_quadratic_card_eq
    {D : Finset (Finset α)} {U R : Finset α}
    (h0 : (∅ : Finset α) ∈ D) (hD : InterClosed D)
    (hH : FranklHeightThreeSauer.NoFourChain D)
    (hS : ∀ ⦃A⦄, A ∈ D → A ⊆ U)
    (hSing : ∀ x ∈ U, ({x} : Finset α) ∈ D)
    (hcard : D.card = 1 + U.card + U.card.choose 2)
    (hRU : R ⊆ U) (hR : R.card = 2) : R ∈ D := by
  classical
  by_contra hn
  have hsplit : D.erase (∅ : Finset α) = atoms D ∪ lines D := by
    ext A
    simp only [Finset.mem_erase,Finset.mem_union,mem_atoms,mem_lines,IsAtom,IsLine,
      Finset.nonempty_iff_ne_empty]
    tauto
  have hdisj : Disjoint (atoms D) (lines D) := by
    apply Finset.disjoint_left.mpr
    intro A ha hl
    exact (mem_lines.mp hl).2.2 (mem_atoms.mp ha)
  have hAt : (atoms D).card = U.card := by
    rw [atoms_eq_singletons_of_mem_all hS hSing,
      Finset.card_image_of_injective _ (fun x y h => Finset.singleton_inj.mp h)]
  have hc := Finset.card_erase_add_one h0
  rw [hsplit,Finset.card_union_of_disjoint hdisj,hAt,hcard] at hc
  have hcL : (lines D).card = U.card.choose 2 := by omega
  have hget (A : ↥(lines D)) :
      ∃ T : Finset α, T ⊆ A.val ∧ T.card = 2 ∧ T ≠ R := by
    have hl := mem_lines.mp A.property
    by_cases hsub : R ⊆ A.val
    · have hnA : A.val ≠ R := fun e => hn (e ▸ hl.1)
      obtain ⟨x,hx⟩ := Finset.sdiff_nonempty.mpr
        (fun h => hnA (Finset.Subset.antisymm h hsub))
      obtain ⟨hxA,hxR⟩ := Finset.mem_sdiff.mp hx
      have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨y,hyR⟩ := hRne
      have hxy : x ≠ y := fun e => hxR (e.symm ▸ hyR)
      refine ⟨{x,y},Finset.insert_subset_iff.mpr
        ⟨hxA,Finset.singleton_subset_iff.mpr (hsub hyR)⟩,by simp [hxy],?_⟩
      intro he
      exact hxR (he ▸ Finset.mem_insert_self _ _)
    · obtain ⟨x,y,hx,hy,hxy⟩ := Finset.one_lt_card_iff.mp (line_card_ge_two hl)
      refine ⟨{x,y},Finset.insert_subset_iff.mpr
        ⟨hx,Finset.singleton_subset_iff.mpr hy⟩,by simp [hxy],?_⟩
      intro he
      exact hsub (he ▸ Finset.insert_subset_iff.mpr ⟨hx,Finset.singleton_subset_iff.mpr hy⟩)
  let f (A : ↥(lines D)) : ↥((U.powersetCard 2).erase R) :=
    ⟨(hget A).choose, Finset.mem_erase.mpr
      ⟨(hget A).choose_spec.2.2,Finset.mem_powersetCard.mpr
        ⟨(hget A).choose_spec.1.trans (hS (mem_lines.mp A.property).1),
          (hget A).choose_spec.2.1⟩⟩⟩
  have hf : Function.Injective f := by
    intro A B he
    apply Subtype.ext
    have hA := mem_lines.mp A.property
    have hB := mem_lines.mp B.property
    have hsA : (f A).val ⊆ A.val := (hget A).choose_spec.1
    have hsB : (f A).val ⊆ B.val :=
      (congrArg Subtype.val he).symm ▸ (hget B).choose_spec.1
    obtain ⟨x,y,hxy,hpair⟩ := Finset.card_eq_two.mp (hget A).choose_spec.2.1
    change (f A).val = {x,y} at hpair
    have hx : x ∈ (f A).val := by simp [hpair]
    have hy : y ∈ (f A).val := by simp [hpair]
    have hxU := hS hA.1 (hsA hx)
    have hyU := hS hA.1 (hsA hy)
    have hne : ({x} : Finset α) ≠ {y} := fun e => hxy (Finset.singleton_inj.mp e)
    exact line_eq_of_two_common_atoms h0 hD hH hA hB
      (singleton_isAtom_of_mem (hSing x hxU)) (singleton_isAtom_of_mem (hSing y hyU)) hne
      (Finset.singleton_subset_iff.mpr (hsA hx)) (Finset.singleton_subset_iff.mpr (hsB hx))
      (Finset.singleton_subset_iff.mpr (hsA hy)) (Finset.singleton_subset_iff.mpr (hsB hy))
  have hC := Finset.card_le_card_of_injective hf
  have hRP : R ∈ U.powersetCard 2 := Finset.mem_powersetCard.mpr ⟨hRU,hR⟩
  have hE := Finset.card_erase_add_one hRP
  rw [Finset.card_powersetCard] at hE
  omega

#print axioms singleton_isAtom_of_mem
#print axioms line_card_ge_two
#print axioms pair_mem_of_quadratic_card_eq
end FranklRankTwoAtoms
