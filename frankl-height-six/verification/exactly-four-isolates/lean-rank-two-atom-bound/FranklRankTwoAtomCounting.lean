import FranklRankTwoAtomGeometry
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace FranklRankTwoAtoms
open scoped BigOperators
variable {α : Type*} [DecidableEq α]

noncomputable def atomBelow (D : Finset (Finset α)) (A : Finset α) : Finset (Finset α) :=
  (atoms D).filter (· ⊆ A)

noncomputable def rich (D : Finset (Finset α)) : Finset (Finset α) :=
  (lines D).filter (fun A => 2 ≤ (atomBelow D A).card)

noncomputable def poor (D : Finset (Finset α)) : Finset (Finset α) :=
  (lines D).filter (fun A => ¬ (2 ≤ (atomBelow D A).card))

noncomputable def covered (D : Finset (Finset α)) : Finset α := (atoms D).biUnion id

theorem mem_atomBelow {D : Finset (Finset α)} {A C : Finset α} :
    C ∈ atomBelow D A ↔ IsAtom D C ∧ C ⊆ A := by
  rw [atomBelow,Finset.mem_filter,mem_atoms]

/-- A pair of distinct atoms belongs to at most one line. -/
theorem line_eq_of_two_common_atoms {D : Finset (Finset α)} {A B C E : Finset α}
    (h0 : (∅ : Finset α) ∈ D) (hD : InterClosed D)
    (hH : FranklHeightThreeSauer.NoFourChain D)
    (hA : IsLine D A) (hB : IsLine D B)
    (hC : IsAtom D C) (hE : IsAtom D E) (hne : C ≠ E)
    (hCA : C ⊆ A) (hCB : C ⊆ B) (hEA : E ⊆ A) (hEB : E ⊆ B) :
    A = B := by
  by_contra hn
  have hc : C ⊆ A ∩ B := fun _ h => Finset.mem_inter.mpr ⟨hCA h,hCB h⟩
  have he : E ⊆ A ∩ B := fun _ h => Finset.mem_inter.mpr ⟨hEA h,hEB h⟩
  rcases distinct_lines_inter_eq_empty_or_atom h0 hD hH hA hB hn with hi | hi
  · obtain ⟨x,hx⟩ := hC.2.1
    exact Finset.notMem_empty _ (hi ▸ hc hx)
  · exact hne ((hi.2.2 hC.1 hC.2.1 hc).trans (hi.2.2 hE.1 hE.2.1 he).symm)

theorem rich_card_le_choose_atoms {D : Finset (Finset α)}
    (h0 : (∅ : Finset α) ∈ D) (hD : InterClosed D)
    (hH : FranklHeightThreeSauer.NoFourChain D) :
    (rich D).card ≤ (atoms D).card.choose 2 := by
  classical
  have hchoose (A : ↥(rich D)) : ((atomBelow D A.val).powersetCard 2).Nonempty := by
    have ha := (Finset.mem_filter.mp A.property).2
    rw [Finset.nonempty_iff_ne_empty]
    intro hn
    have hc := Finset.card_powersetCard 2 (atomBelow D A.val)
    rw [hn,Finset.card_empty] at hc
    exact (Nat.ne_of_gt (Nat.choose_pos ha)) hc.symm
  let f (A : ↥(rich D)) : ↥((atoms D).powersetCard 2) :=
    ⟨(hchoose A).choose, by
      obtain ⟨hs,hc⟩ := Finset.mem_powersetCard.mp (hchoose A).choose_spec
      exact Finset.mem_powersetCard.mpr ⟨hs.trans (Finset.filter_subset _ _),hc⟩⟩
  have hfmem (A : ↥(rich D)) :
      (f A).val ∈ (atomBelow D A.val).powersetCard 2 := (hchoose A).choose_spec
  have hf : Function.Injective f := by
    intro A B he
    apply Subtype.ext
    have hA := mem_lines.mp (Finset.mem_filter.mp A.property).1
    have hB := mem_lines.mp (Finset.mem_filter.mp B.property).1
    have hPair := hfmem A
    have hPair' : (f A).val ∈ (atomBelow D B.val).powersetCard 2 :=
      (congrArg Subtype.val he).symm ▸ hfmem B
    obtain ⟨hAS,hAC⟩ := Finset.mem_powersetCard.mp hPair
    obtain ⟨hBS,_⟩ := Finset.mem_powersetCard.mp hPair'
    obtain ⟨C,E,hCE,hEq⟩ := Finset.card_eq_two.mp hAC
    have hC : C ∈ (f A).val := hEq.symm ▸ (by simp)
    have hE : E ∈ (f A).val := hEq.symm ▸ (by simp)
    obtain ⟨hCat,hCA⟩ := mem_atomBelow.mp (hAS hC)
    obtain ⟨hEat,hEA⟩ := mem_atomBelow.mp (hAS hE)
    exact line_eq_of_two_common_atoms h0 hD hH hA hB hCat hEat hCE
      hCA (mem_atomBelow.mp (hBS hC)).2 hEA (mem_atomBelow.mp (hBS hE)).2
  have hc := Finset.card_le_card_of_injective hf
  rw [Finset.card_powersetCard] at hc
  exact hc

theorem covered_subset_support {D : Finset (Finset α)} {U : Finset α}
    (hS : ∀ ⦃A⦄, A ∈ D → A ⊆ U) : covered D ⊆ U := by
  intro x hx
  obtain ⟨A,hA,hxA⟩ := Finset.mem_biUnion.mp hx
  exact hS (mem_atoms.mp hA).1 hxA

theorem poor_card_le_uncovered {D : Finset (Finset α)} {U : Finset α}
    (h0 : (∅ : Finset α) ∈ D) (hD : InterClosed D)
    (hH : FranklHeightThreeSauer.NoFourChain D)
    (hS : ∀ ⦃A⦄, A ∈ D → A ⊆ U) :
    (poor D).card ≤ (U \ covered D).card := by
  classical
  have hchoose (A : ↥(poor D)) : (A.val \ covered D).Nonempty := by
    have hl := mem_lines.mp (Finset.mem_filter.mp A.property).1
    have hcard : (atomBelow D A.val).card ≤ 1 := by
      have h := (Finset.mem_filter.mp A.property).2
      omega
    obtain ⟨C,hC,hCA⟩ := exists_atom_below hl.1 hl.2.1
    have honly {T : Finset α} (hT : IsAtom D T) (hTA : T ⊆ A.val) : T = C :=
      Finset.card_le_one_iff.mp hcard (mem_atomBelow.mpr ⟨hT,hTA⟩)
        (mem_atomBelow.mpr ⟨hC,hCA⟩)
    obtain ⟨x,hx,hAll⟩ := exists_atomless_point_single_atom_line hD hl hC hCA (@honly)
    refine ⟨x,Finset.mem_sdiff.mpr ⟨hx,?_⟩⟩
    intro hx'
    obtain ⟨T,hT,hTx⟩ := Finset.mem_biUnion.mp hx'
    exact hAll (mem_atoms.mp hT) hTx
  let f (A : ↥(poor D)) : ↥(U \ covered D) :=
    ⟨(hchoose A).choose, by
      obtain ⟨hx,hn⟩ := Finset.mem_sdiff.mp (hchoose A).choose_spec
      exact Finset.mem_sdiff.mpr ⟨hS (mem_lines.mp (Finset.mem_filter.mp A.property).1).1 hx,hn⟩⟩
  have hfmem (A : ↥(poor D)) : (f A).val ∈ A.val \ covered D := (hchoose A).choose_spec
  have hf : Function.Injective f := by
    intro A B he
    apply Subtype.ext
    have hA := mem_lines.mp (Finset.mem_filter.mp A.property).1
    have hB := mem_lines.mp (Finset.mem_filter.mp B.property).1
    obtain ⟨hxA,hxN⟩ := Finset.mem_sdiff.mp (hfmem A)
    have hxB : (f A).val ∈ B.val := (congrArg Subtype.val he).symm ▸
      (Finset.mem_sdiff.mp (hfmem B)).1
    apply atomless_point_line_unique h0 hD hH hA hB hxA hxB
    intro T hT hxT
    exact hxN (Finset.mem_biUnion.mpr ⟨T,mem_atoms.mpr hT,hxT⟩)
  exact Finset.card_le_card_of_injective hf

theorem covered_card_eq_sum {D : Finset (Finset α)} (hD : InterClosed D) :
    (covered D).card = ∑ A ∈ atoms D, A.card := by
  apply Finset.card_biUnion
  intro A hA B hB hne
  exact distinct_atoms_disjoint hD (mem_atoms.mp hA) (mem_atoms.mp hB) hne

theorem atoms_card_le_covered {D : Finset (Finset α)} (hD : InterClosed D) :
    (atoms D).card ≤ (covered D).card := by
  rw [covered_card_eq_sum hD,Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro A hA
  exact Finset.card_pos.mpr (mem_atoms.mp hA).2.1

/-- Rank-two atom-sensitive upper bound. This is stronger than the
unrefined Sauer bound when not every support coordinate is an atom. -/
theorem card_le_support_add_choose_atoms {D : Finset (Finset α)} {U : Finset α}
    (h0 : (∅ : Finset α) ∈ D) (hD : InterClosed D)
    (hH : FranklHeightThreeSauer.NoFourChain D)
    (hS : ∀ ⦃A⦄, A ∈ D → A ⊆ U) :
    D.card ≤ 1 + U.card + (atoms D).card.choose 2 := by
  classical
  have hsplit : D.erase (∅ : Finset α) = atoms D ∪ lines D := by
    ext A
    simp only [Finset.mem_erase,Finset.mem_union,mem_atoms,mem_lines,IsAtom,IsLine,
      Finset.nonempty_iff_ne_empty]
    tauto
  have hdisj : Disjoint (atoms D) (lines D) := by
    apply Finset.disjoint_left.mpr
    intro A hA hL
    exact (mem_lines.mp hL).2.2 (mem_atoms.mp hA)
  have hc := Finset.card_erase_add_one h0
  rw [hsplit,Finset.card_union_of_disjoint hdisj] at hc
  have hf : (rich D).card + (poor D).card = (lines D).card :=
    Finset.card_filter_add_card_filter_not _
  have ha := atoms_card_le_covered hD
  have hR := rich_card_le_choose_atoms h0 hD hH
  have hP := poor_card_le_uncovered h0 hD hH hS
  have hu := Finset.card_sdiff_add_card_eq_card (covered_subset_support hS)
  omega

/-- If the disjoint atoms cover as many slots as the whole support,
there is one singleton atom at every support point. -/
theorem atoms_eq_singletons_of_card_eq_support
    {D : Finset (Finset α)} {U : Finset α} (hD : InterClosed D)
    (hS : ∀ ⦃A⦄, A ∈ D → A ⊆ U) (heq : (atoms D).card = U.card) :
    atoms D = U.image (fun x => ({x} : Finset α)) := by
  classical
  have hcS := covered_subset_support hS
  have hc := atoms_card_le_covered hD
  have hu : covered D = U := Finset.eq_of_subset_of_card_le hcS (heq ▸ hc)
  have hsum : (∑ A ∈ atoms D, A.card) = (atoms D).card := by
    rw [← covered_card_eq_sum hD,hu,heq]
  have hAtomOne {A : Finset α} (hA : A ∈ atoms D) : A.card = 1 := by
    have hpos : 1 ≤ A.card := Finset.card_pos.mpr (mem_atoms.mp hA).2.1
    by_contra hn
    have hgt : 1 < A.card := by omega
    have hlt : (∑ _B ∈ atoms D, 1) < ∑ B ∈ atoms D, B.card :=
      Finset.sum_lt_sum (fun _ hB => Finset.card_pos.mpr (mem_atoms.mp hB).2.1)
        ⟨A,hA,hgt⟩
    rw [← Finset.card_eq_sum_ones,hsum] at hlt
    exact (Nat.lt_irrefl _ hlt)
  ext A
  constructor
  · intro hA
    obtain ⟨x,rfl⟩ := Finset.card_eq_one.mp (hAtomOne hA)
    exact Finset.mem_image.mpr ⟨x,hS (mem_atoms.mp hA).1 (Finset.mem_singleton_self x),rfl⟩
  · intro hA
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hA
    have hx' : x ∈ covered D := hu.symm ▸ hx
    obtain ⟨B,hB,hxB⟩ := Finset.mem_biUnion.mp hx'
    obtain ⟨y,rfl⟩ := Finset.card_eq_one.mp (hAtomOne hB)
    have hxy : x = y := Finset.mem_singleton.mp hxB
    exact hxy.symm ▸ hB

theorem singleton_atoms_of_large_card
    {D : Finset (Finset α)} {U : Finset α}
    (h0 : (∅ : Finset α) ∈ D) (hD : InterClosed D)
    (hH : FranklHeightThreeSauer.NoFourChain D)
    (hS : ∀ ⦃A⦄, A ∈ D → A ⊆ U)
    (hlarge : 1 + U.card + (U.card - 1).choose 2 < D.card) :
    atoms D = U.image (fun x => ({x} : Finset α)) := by
  have ha := (atoms_card_le_covered hD).trans (Finset.card_le_card (covered_subset_support hS))
  have heq : (atoms D).card = U.card := by
    by_contra hn
    have ht : (atoms D).card ≤ U.card - 1 := by omega
    have hct := card_le_support_add_choose_atoms h0 hD hH hS
    have hch := Nat.choose_le_choose 2 ht
    omega
  exact atoms_eq_singletons_of_card_eq_support hD hS heq

#print axioms line_eq_of_two_common_atoms
#print axioms rich_card_le_choose_atoms
#print axioms poor_card_le_uncovered
#print axioms atoms_card_le_covered
#print axioms card_le_support_add_choose_atoms
#print axioms atoms_eq_singletons_of_card_eq_support
#print axioms singleton_atoms_of_large_card
end FranklRankTwoAtoms
