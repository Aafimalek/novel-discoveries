import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.SDiff

namespace FranklHeightSix

variable {α : Type*} [DecidableEq α]

def UnionClosed (G : Finset (Finset α)) : Prop :=
  ∀ ⦃A B⦄, A ∈ G → B ∈ G → A ∪ B ∈ G

def NoThreeChain (G : Finset (Finset α)) : Prop :=
  ∀ ⦃A B C⦄, A ∈ G → B ∈ G → C ∈ G → A ⊂ B → B ⊂ C → False

/-- The union of a nonempty finite union-closed family is its maximum member. -/
theorem exists_top {G : Finset (Finset α)} (hU : UnionClosed G) (hNE : G.Nonempty) :
    ∃ T ∈ G, ∀ ⦃A⦄, A ∈ G → A ⊆ T := by
  let T := G.sup' hNE id
  refine ⟨T, ?_, ?_⟩
  · exact Finset.sup'_mem (G : Set (Finset α))
      (fun _ hX _ hY => hU hX hY) G hNE id (fun _ h => h)
  · intro A hA
    exact Finset.le_sup' id hA

/-- Distinct proper members of a height-two family union to the maximum. -/
theorem union_eq_top_of_ne {G : Finset (Finset α)} {T A B : Finset α}
    (hU : UnionClosed G) (hH : NoThreeChain G) (hT : T ∈ G)
    (hTop : ∀ ⦃X⦄, X ∈ G → X ⊆ T)
    (hA : A ∈ G) (hB : B ∈ G) (hAT : A ≠ T) (hAB : A ≠ B) :
    A ∪ B = T := by
  have hAT' : A ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hTop hA, hAT⟩
  have hBA : ¬ B ⊆ A := by
    intro h
    exact hH hB hA hT (Finset.ssubset_iff_subset_ne.mpr ⟨h, Ne.symm hAB⟩) hAT'
  have hAne : A ≠ A ∪ B := by
    intro h
    apply hBA
    simpa only [← h] using (Finset.subset_union_right : B ⊆ A ∪ B)
  by_contra hne
  exact hH hA (hU hA hB) hT
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, hAne⟩)
    (Finset.ssubset_iff_subset_ne.mpr ⟨hTop (hU hA hB), hne⟩)

/-- Distinct proper members have disjoint complements in the maximum. -/
theorem disjoint_complements {G : Finset (Finset α)} {T A B : Finset α}
    (hU : UnionClosed G) (hH : NoThreeChain G) (hT : T ∈ G)
    (hTop : ∀ ⦃X⦄, X ∈ G → X ⊆ T)
    (hA : A ∈ G) (hB : B ∈ G) (hAT : A ≠ T) (hAB : A ≠ B) :
    Disjoint (T \ A) (T \ B) := by
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  have hxA' := Finset.mem_sdiff.mp hxA
  have hxB' := Finset.mem_sdiff.mp hxB
  have hxU : x ∈ A ∪ B := by
    rw [union_eq_top_of_ne hU hH hT hTop hA hB hAT hAB]
    exact hxA'.1
  exact (Finset.mem_union.mp hxU).elim hxA'.2 hxB'.2

/-- A finite union-closed family of height at most two has at most
`T.card + 1` sets, where `T` is its maximum. -/
theorem card_le_top_card_add_one {G : Finset (Finset α)} {T : Finset α}
    (hU : UnionClosed G) (hH : NoThreeChain G) (hT : T ∈ G)
    (hTop : ∀ ⦃X⦄, X ∈ G → X ⊆ T) : G.card ≤ T.card + 1 := by
  classical
  have hw (A : ↥(G.erase T)) : (T \ (A : Finset α)).Nonempty := by
    have hA := Finset.mem_erase.mp A.property
    apply Finset.sdiff_nonempty.mpr
    intro h
    exact hA.1 (Finset.Subset.antisymm (hTop hA.2) h)
  let f (A : ↥(G.erase T)) : ↥T :=
    ⟨(hw A).choose, (Finset.mem_sdiff.mp (hw A).choose_spec).1⟩
  have hfmem (A : ↥(G.erase T)) : (f A : α) ∈ T \ (A : Finset α) :=
    (hw A).choose_spec
  have hf : Function.Injective f := by
    intro A B heq
    by_contra hne
    have hA := Finset.mem_erase.mp A.property
    have hB := Finset.mem_erase.mp B.property
    have hne' : (A : Finset α) ≠ (B : Finset α) := fun h => hne (Subtype.ext h)
    have hd := disjoint_complements hU hH hT hTop hA.2 hB.2 hA.1 hne'
    exact Finset.disjoint_left.mp hd (hfmem A) (by simpa only [heq] using hfmem B)
  have hcard : (G.erase T).card ≤ T.card := Finset.card_le_card_of_injective hf
  calc
    G.card = (G.erase T).card + 1 := (Finset.card_erase_add_one hT).symm
    _ ≤ T.card + 1 := Nat.add_le_add_right hcard 1

def NoSevenChain (G : Finset (Finset α)) : Prop :=
  ∀ ⦃A B C D E F H⦄, A ∈ G → B ∈ G → C ∈ G → D ∈ G →
    E ∈ G → F ∈ G → H ∈ G → A ⊂ B → B ⊂ C → C ⊂ D →
    D ⊂ E → E ⊂ F → F ⊂ H → False

/-- A down-set of a five-member chain's bottom in a height-six family has
at most `T.card + 1` members. -/
theorem card_subsets_le_of_four_extensions {G : Finset (Finset α)}
    {T D E F H : Finset α}
    (hU : UnionClosed G) (hH : NoSevenChain G)
    (hT : T ∈ G) (hD : D ∈ G) (hE : E ∈ G) (hF : F ∈ G) (hLast : H ∈ G)
    (hTD : T ⊂ D) (hDE : D ⊂ E) (hEF : E ⊂ F) (hFH : F ⊂ H) :
    (G.filter (fun A => A ⊆ T)).card ≤ T.card + 1 := by
  let L := G.filter (fun A => A ⊆ T)
  have hL (A : Finset α) : A ∈ L ↔ A ∈ G ∧ A ⊆ T := Finset.mem_filter
  have hLT : T ∈ L := (hL T).mpr ⟨hT, fun _ hx => hx⟩
  have hLU : UnionClosed L := by
    intro A B hA hB
    have ha := (hL A).mp hA
    have hb := (hL B).mp hB
    exact (hL (A ∪ B)).mpr ⟨hU ha.1 hb.1, Finset.union_subset ha.2 hb.2⟩
  have hLH : NoThreeChain L := by
    intro A B C hA hB hC hAB hBC
    have hc := (hL C).mp hC
    exact hH ((hL A).mp hA).1 ((hL B).mp hB).1 hc.1 hD hE hF hLast hAB hBC
      (Finset.ssubset_of_subset_of_ssubset hc.2 hTD) hDE hEF hFH
  exact card_le_top_card_add_one hLU hLH hLT (fun {A} hA => ((hL A).mp hA).2)

/-- Complementation inside a fixed universe strictly reverses proper inclusion. -/
theorem sdiff_ssubset_sdiff {U P Q : Finset α} (hPQ : P ⊂ Q) (hQU : Q ⊆ U) :
    U \ Q ⊂ U \ P := by
  have hPQ' := (Finset.ssubset_iff_subset_ne.mp hPQ).1
  have hs : U \ Q ⊆ U \ P := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hx'.1, fun h => hx'.2 (hPQ' h)⟩
  obtain ⟨x, hxQ, hxP⟩ := (Finset.ssubset_iff_of_subset hPQ').mp hPQ
  exact (Finset.ssubset_iff_of_subset hs).mpr
    ⟨x, Finset.mem_sdiff.mpr ⟨hQU hxQ, hxP⟩, fun h => (Finset.mem_sdiff.mp h).2 hxQ⟩

/-- If three nested nonempty omitted sets are represented by complements,
then the avoidance fiber of a strictly larger omitted set has linear size. -/
theorem card_avoiding_le_of_three_complements {G : Finset (Finset α)}
    {U S₁ S₂ S₃ S₄ : Finset α} (hU : UnionClosed G) (hH : NoSevenChain G)
    (hTop : ∀ ⦃A⦄, A ∈ G → A ⊆ U) (hUG : U ∈ G)
    (h₁ : U \ S₁ ∈ G) (h₂ : U \ S₂ ∈ G) (h₃ : U \ S₃ ∈ G)
    (hNE₁ : S₁.Nonempty) (h₁₂ : S₁ ⊂ S₂) (h₂₃ : S₂ ⊂ S₃)
    (h₃₄ : S₃ ⊂ S₄) (h₄U : S₄ ⊆ U) :
    (G.filter (fun A => Disjoint A S₄)).card ≤ U.card - S₄.card + 1 := by
  let L := G.filter (fun A => Disjoint A S₄)
  change L.card ≤ U.card - S₄.card + 1
  have hL (A : Finset α) : A ∈ L ↔ A ∈ G ∧ Disjoint A S₄ := Finset.mem_filter
  have hLU : UnionClosed L := by
    intro A B hA hB
    have ha := (hL A).mp hA
    have hb := (hL B).mp hB
    refine (hL (A ∪ B)).mpr ⟨hU ha.1 hb.1, Finset.disjoint_left.mpr ?_⟩
    intro x hx
    exact (Finset.mem_union.mp hx).elim
      (fun h => Finset.disjoint_left.mp ha.2 h) (fun h => Finset.disjoint_left.mp hb.2 h)
  by_cases hNE : L.Nonempty
  · obtain ⟨T, hT, hMax⟩ := exists_top hLU hNE
    have hTG := (hL T).mp hT
    have hTS₄ : T ⊆ U \ S₄ := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hTop hTG.1 hx, Finset.disjoint_left.mp hTG.2 hx⟩
    have h₃U : S₃ ⊆ U := fun _ hx => h₄U ((Finset.ssubset_iff_subset_ne.mp h₃₄).1 hx)
    have h₂U : S₂ ⊆ U := fun _ hx => h₃U ((Finset.ssubset_iff_subset_ne.mp h₂₃).1 hx)
    have h₁U : S₁ ⊆ U := fun _ hx => h₂U ((Finset.ssubset_iff_subset_ne.mp h₁₂).1 hx)
    have hTD : T ⊂ U \ S₃ :=
      Finset.ssubset_of_subset_of_ssubset hTS₄ (sdiff_ssubset_sdiff h₃₄ h₄U)
    have hDE : U \ S₃ ⊂ U \ S₂ := sdiff_ssubset_sdiff h₂₃ h₃U
    have hEF : U \ S₂ ⊂ U \ S₁ := sdiff_ssubset_sdiff h₁₂ h₂U
    have hFH : U \ S₁ ⊂ U := by
      obtain ⟨x, hx⟩ := hNE₁
      exact (Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr
        ⟨x, h₁U hx, fun h => (Finset.mem_sdiff.mp h).2 hx⟩
    have hFilters : L = G.filter (fun A => A ⊆ T) := by
      ext A
      rw [hL A, Finset.mem_filter]
      constructor
      · intro h
        exact ⟨h.1, hMax ((hL A).mpr h)⟩
      · intro h
        refine ⟨h.1, Finset.disjoint_left.mpr ?_⟩
        intro x hx
        exact Finset.disjoint_left.mp hTG.2 (h.2 hx)
    calc
      L.card = (G.filter (fun A => A ⊆ T)).card := congrArg Finset.card hFilters
      _ ≤ T.card + 1 := card_subsets_le_of_four_extensions hU hH hTG.1
        h₃ h₂ h₁ hUG hTD hDE hEF hFH
      _ ≤ (U \ S₄).card + 1 := Nat.add_le_add_right (Finset.card_le_card hTS₄) 1
      _ = U.card - S₄.card + 1 := by rw [Finset.card_sdiff_of_subset h₄U]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hNE, Finset.card_empty]
    exact Nat.zero_le _

end FranklHeightSix

#print axioms FranklHeightSix.card_le_top_card_add_one
#print axioms FranklHeightSix.card_subsets_le_of_four_extensions
#print axioms FranklHeightSix.card_avoiding_le_of_three_complements
