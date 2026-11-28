import FranklHeightThreeSauer
import Mathlib.Data.Finset.Max

/- Kernel-checked generic atom geometry; counts are in the companion module. -/
namespace FranklRankTwoAtoms

variable {α : Type*} [DecidableEq α]

def InterClosed (D : Finset (Finset α)) : Prop :=
  ∀ ⦃A B⦄, A ∈ D → B ∈ D → A ∩ B ∈ D

def IsAtom (D : Finset (Finset α)) (A : Finset α) : Prop :=
  A ∈ D ∧ A.Nonempty ∧ ∀ ⦃B⦄, B ∈ D → B.Nonempty → B ⊆ A → B = A

def IsLine (D : Finset (Finset α)) (A : Finset α) : Prop :=
  A ∈ D ∧ A.Nonempty ∧ ¬ IsAtom D A

noncomputable def atoms (D : Finset (Finset α)) : Finset (Finset α) := by
  classical
  exact D.filter (IsAtom D)

noncomputable def lines (D : Finset (Finset α)) : Finset (Finset α) := by
  classical
  exact D.filter (IsLine D)

omit [DecidableEq α] in
theorem mem_atoms {D : Finset (Finset α)} {A : Finset α} :
    A ∈ atoms D ↔ IsAtom D A := by
  classical
  unfold atoms
  exact ⟨fun h => (Finset.mem_filter.mp h).2,fun h => Finset.mem_filter.mpr ⟨h.1,h⟩⟩

omit [DecidableEq α] in
theorem mem_lines {D : Finset (Finset α)} {A : Finset α} :
    A ∈ lines D ↔ IsLine D A := by
  classical
  unfold lines
  exact ⟨fun h => (Finset.mem_filter.mp h).2,fun h => Finset.mem_filter.mpr ⟨h.1,h⟩⟩

/-- Choose a smallest nonempty member below the given nonempty member. -/
theorem exists_atom_below {D : Finset (Finset α)} {A : Finset α}
    (hA : A ∈ D) (hne : A.Nonempty) :
    ∃ C, IsAtom D C ∧ C ⊆ A := by
  classical
  let E := D.filter (fun T => T.Nonempty ∧ T ⊆ A)
  have hE : E.Nonempty := ⟨A,Finset.mem_filter.mpr ⟨hA,hne,fun _ h => h⟩⟩
  obtain ⟨C,hCE,hmin⟩ := Finset.exists_min_image E (fun T => T.card) hE
  obtain ⟨hCD,hCN,hCA⟩ := Finset.mem_filter.mp hCE
  refine ⟨C,⟨hCD,hCN,?_⟩,hCA⟩
  intro T hTD hTN hTC
  by_contra hne'
  have hTE : T ∈ E := Finset.mem_filter.mpr ⟨hTD,hTN,hTC.trans hCA⟩
  have hlt : T ⊂ C := Finset.ssubset_iff_subset_ne.mpr ⟨hTC,hne'⟩
  exact (Nat.not_lt_of_ge (hmin T hTE)) (Finset.card_lt_card hlt)

/-- If an atom meets a member, their intersection must be the atom. -/
theorem atom_subset_of_common_point {D : Finset (Finset α)} {A B : Finset α}
    (hD : InterClosed D) (hA : IsAtom D A) (hB : B ∈ D)
    {x : α} (hxA : x ∈ A) (hxB : x ∈ B) : A ⊆ B := by
  have he : A ∩ B = A :=
    hA.2.2 (hD hA.1 hB) ⟨x,Finset.mem_inter.mpr ⟨hxA,hxB⟩⟩ Finset.inter_subset_left
  intro y hy
  exact (Finset.mem_inter.mp (he.symm ▸ hy)).2

theorem distinct_atoms_disjoint {D : Finset (Finset α)} {A B : Finset α}
    (hD : InterClosed D) (hA : IsAtom D A) (hB : IsAtom D B) (hne : A ≠ B) :
    Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  exact hne (hB.2.2 hA.1 hA.2.1 (atom_subset_of_common_point hD hA hB.1 hxA hxB))

theorem exists_atom_strict_below_line {D : Finset (Finset α)} {A : Finset α}
    (hA : IsLine D A) :
    ∃ C, IsAtom D C ∧ C ⊂ A := by
  obtain ⟨C,hC,hsub⟩ := exists_atom_below hA.1 hA.2.1
  exact ⟨C,hC,Finset.ssubset_iff_subset_ne.mpr ⟨hsub,fun he => hA.2.2 (he ▸ hC)⟩⟩

/-- A nonatom in an intersection system of height at most three,
with the empty set present, is maximal. -/
theorem line_is_maximal {D : Finset (Finset α)} {A B : Finset α}
    (h0 : (∅ : Finset α) ∈ D) (hH : FranklHeightThreeSauer.NoFourChain D)
    (hA : IsLine D A) (hB : B ∈ D) (hAB : A ⊆ B) : A = B := by
  by_contra hne
  obtain ⟨C,hC,hCA⟩ := exists_atom_strict_below_line hA
  exact hH h0 hC.1 hA.1 hB (Finset.empty_ssubset.mpr hC.2.1) hCA
    (Finset.ssubset_iff_subset_ne.mpr ⟨hAB,hne⟩)

/-- Two different nonatoms have intersection empty or a single atom. -/
theorem distinct_lines_inter_eq_empty_or_atom {D : Finset (Finset α)} {A B : Finset α}
    (h0 : (∅ : Finset α) ∈ D) (hD : InterClosed D)
    (hH : FranklHeightThreeSauer.NoFourChain D)
    (hA : IsLine D A) (hB : IsLine D B) (hne : A ≠ B) :
    A ∩ B = ∅ ∨ IsAtom D (A ∩ B) := by
  classical
  by_cases hE : A ∩ B = ∅
  · exact Or.inl hE
  · right
    have hI := hD hA.1 hB.1
    have hN : (A ∩ B).Nonempty := Finset.nonempty_iff_ne_empty.mpr hE
    by_contra hna
    have hIA : A ∩ B = A := line_is_maximal h0 hH ⟨hI,hN,hna⟩ hA.1 Finset.inter_subset_left
    have hIB : A ∩ B = B := line_is_maximal h0 hH ⟨hI,hN,hna⟩ hB.1 Finset.inter_subset_right
    exact hne (hIA.symm.trans hIB)

/-- A point in no atom belongs to at most one line. -/
theorem atomless_point_line_unique {D : Finset (Finset α)} {A B : Finset α} {x : α}
    (h0 : (∅ : Finset α) ∈ D) (hD : InterClosed D)
    (hH : FranklHeightThreeSauer.NoFourChain D)
    (hA : IsLine D A) (hB : IsLine D B) (hxA : x ∈ A) (hxB : x ∈ B)
    (hx : ∀ ⦃C⦄, IsAtom D C → x ∉ C) : A = B := by
  by_contra hne
  have hxi : x ∈ A ∩ B := Finset.mem_inter.mpr ⟨hxA,hxB⟩
  rcases distinct_lines_inter_eq_empty_or_atom h0 hD hH hA hB hne with h | h
  · exact Finset.notMem_empty _ (h ▸ hxi)
  · exact hx h hxi

/-- A line containing just one atom has a point outside all atoms. -/
theorem exists_atomless_point_single_atom_line {D : Finset (Finset α)} {A C : Finset α}
    (hD : InterClosed D) (hA : IsLine D A)
    (hC : IsAtom D C) (hCA : C ⊆ A)
    (honly : ∀ ⦃T⦄, IsAtom D T → T ⊆ A → T = C) :
    ∃ x ∈ A, ∀ ⦃T⦄, IsAtom D T → x ∉ T := by
  have hne : C ≠ A := fun e => hA.2.2 (e ▸ hC)
  obtain ⟨x,hx⟩ := Finset.sdiff_nonempty.mpr (fun hAC =>
    hne (Finset.Subset.antisymm hCA hAC))
  obtain ⟨hxA,hxC⟩ := Finset.mem_sdiff.mp hx
  refine ⟨x,hxA,?_⟩
  intro T hT hxT
  have he := honly hT (atom_subset_of_common_point hD hT hA.1 hxT hxA)
  exact hxC (he ▸ hxT)

#print axioms exists_atom_below
#print axioms distinct_atoms_disjoint
#print axioms line_is_maximal
#print axioms distinct_lines_inter_eq_empty_or_atom
#print axioms atomless_point_line_unique
#print axioms exists_atomless_point_single_atom_line
end FranklRankTwoAtoms
