import FranklForcingFiber
import Mathlib.Data.Finset.Max

/- Kernel-checked with pinned Lean 4.36 and Mathlib. -/
namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

/-- If a point occurs strictly more than half the time, some member loses
membership when that point is deleted. -/
theorem exists_missing_erase_of_strict_majority {B : Finset (Finset α)} {x : α}
    (hpos : B.card < 2 * frequency B x) :
    ∃ A ∈ B, x ∈ A ∧ A.erase x ∉ B := by
  classical
  by_contra h
  let X := B.filter (x ∈ ·)
  let Y := B.filter (x ∉ ·)
  have hmap : Set.MapsTo (fun A : Finset α => A.erase x)
      (X : Set (Finset α)) (Y : Set (Finset α)) := by
    intro A ha
    have hfa : A ∈ X := ha
    obtain ⟨hAB,hxA⟩ := Finset.mem_filter.mp hfa
    have heB : A.erase x ∈ B := by
      by_contra he
      exact h ⟨A,hAB,hxA,he⟩
    exact Finset.mem_filter.mpr ⟨heB,Finset.notMem_erase x A⟩
  have hinj : Set.InjOn (fun A : Finset α => A.erase x) (X : Set (Finset α)) := by
    intro A ha D hd eq
    have ha' : A ∈ X := ha
    have hd' : D ∈ X := hd
    exact (Finset.insert_erase (Finset.mem_filter.mp ha').2).symm.trans
      ((congrArg (insert x) eq).trans (Finset.insert_erase (Finset.mem_filter.mp hd').2))
  have hcards := Finset.card_le_card_of_injOn (fun A : Finset α => A.erase x) hmap hinj
  have hpart : X.card + Y.card = B.card := Finset.card_filter_add_card_filter_not (x ∈ ·)
  change B.card < 2 * X.card at hpos
  omega

/-- Choose a bad deletion which is maximal for inclusion. -/
theorem exists_maximal_missing_erase {B : Finset (Finset α)} {x : α}
    (hpos : B.card < 2 * frequency B x) :
    ∃ A ∈ B, x ∈ A ∧ A.erase x ∉ B ∧
      ∀ ⦃D⦄, D ∈ B → A ⊂ D → D.erase x ∈ B := by
  classical
  let F := B.filter (fun A => x ∈ A ∧ A.erase x ∉ B)
  obtain ⟨A,hAB,hxA,he⟩ := exists_missing_erase_of_strict_majority hpos
  have hF : F.Nonempty := ⟨A,Finset.mem_filter.mpr ⟨hAB,hxA,he⟩⟩
  obtain ⟨M,hMF,hmax⟩ := Finset.exists_max_image F (fun D => D.card) hF
  obtain ⟨hMB,hxM,heM⟩ := Finset.mem_filter.mp hMF
  refine ⟨M,hMB,hxM,heM,?_⟩
  intro D hDB hMD
  by_contra heD
  have hxD : x ∈ D := (Finset.ssubset_iff_subset_ne.mp hMD).1 hxM
  have hDF : D ∈ F := Finset.mem_filter.mpr ⟨hDB,hxD,heD⟩
  exact (Nat.not_lt_of_ge (hmax D hDF)) (Finset.card_lt_card hMD)

/-- Appending x to a superset of A.erase x is the same as unioning with A. -/
theorem insert_eq_union_of_erase_subset {A D : Finset α} {x : α}
    (hxA : x ∈ A) (hAD : A.erase x ⊆ D) :
    insert x D = A ∪ D := by
  ext y
  simp only [Finset.mem_insert,Finset.mem_union]
  constructor
  · rintro (rfl | hy)
    · exact Or.inl hxA
    · exact Or.inr hy
  · rintro (hy | hy)
    · by_cases h : y = x
      · exact Or.inl h
      · exact Or.inr (hAD (Finset.mem_erase.mpr ⟨h,hy⟩))
    · exact Or.inr hy

/-- Inserting the deletion of a maximal bad A preserves union closure. -/
theorem unionClosed_insert_maximal_missing_erase
    {B : Finset (Finset α)} {A : Finset α} {x : α}
    (hB : UnionClosed B) (hAB : A ∈ B)
    (hmax : ∀ ⦃D⦄, D ∈ B → A ⊂ D → D.erase x ∈ B) :
    UnionClosed (insert (A.erase x) B) := by
  classical
  let C := A.erase x
  have hnew : ∀ ⦃D⦄, D ∈ B → C ∪ D ∈ insert C B := by
    intro D hDB
    have hAD : A ∪ D ∈ B := hB hAB hDB
    by_cases hxD : x ∈ D
    · have heq : C ∪ D = A ∪ D := by
        ext y
        simp only [C,Finset.mem_union,Finset.mem_erase]
        constructor
        · rintro (⟨_,hy⟩ | hy)
          · exact Or.inl hy
          · exact Or.inr hy
        · rintro (hy | hy)
          · by_cases he : y = x
            · exact Or.inr (he.symm ▸ hxD)
            · exact Or.inl ⟨he,hy⟩
          · exact Or.inr hy
      exact Finset.mem_insert_of_mem (heq.symm ▸ hAD)
    · have heD : D.erase x = D := Finset.erase_eq_of_notMem hxD
      have heq : (A ∪ D).erase x = C ∪ D := by
        rw [Finset.erase_union_distrib,heD]
      by_cases he : A ∪ D = A
      · rw [he] at heq
        exact heq ▸ Finset.mem_insert_self C B
      · have hlt : A ⊂ A ∪ D :=
          Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left,fun e => he e.symm⟩
        exact Finset.mem_insert_of_mem (heq ▸ hmax hAD hlt)
  intro D E hd he
  rcases Finset.mem_insert.mp hd with rfl | hd
  · rcases Finset.mem_insert.mp he with rfl | he
    · simp
    · exact hnew he
  · rcases Finset.mem_insert.mp he with rfl | he
    · rw [Finset.union_comm]
      exact hnew hd
    · exact Finset.mem_insert_of_mem (hB hd he)

/-- The new point-free set raises the denominator by one and repairs all
frequencies provided every other point started with slack at least one. -/
theorem repaired_insert_weak_frequencies
    {B : Finset (Finset α)} {C : Finset α} {x : α}
    (hCB : C ∉ B) (hxC : x ∉ C)
    (hx : 2 * frequency B x ≤ B.card + 1)
    (hothers : ∀ v, v ≠ x → 2 * frequency B v + 1 ≤ B.card) :
    ∀ v, 2 * frequency (insert C B) v ≤ (insert C B).card := by
  classical
  have hcard : (insert C B).card = B.card + 1 := Finset.card_insert_of_notMem hCB
  intro v
  rw [hcard]
  by_cases he : v = x
  · subst v
    simpa [frequency,Finset.filter_insert,hxC] using hx
  · have hv := hothers v he
    by_cases hvC : v ∈ C
    · have hn : C ∉ B.filter (v ∈ ·) := fun h => hCB (Finset.mem_filter.mp h).1
      have hf : frequency (insert C B) v = frequency B v + 1 := by
        simp [frequency,Finset.filter_insert,hvC,hn]
      omega
    · simpa [frequency,Finset.filter_insert,hvC] using (show
        2 * frequency B v ≤ B.card + 1 by omega)

#print axioms exists_missing_erase_of_strict_majority
#print axioms exists_maximal_missing_erase
#print axioms insert_eq_union_of_erase_subset
#print axioms unionClosed_insert_maximal_missing_erase
#print axioms repaired_insert_weak_frequencies
end FranklForcingFiber
