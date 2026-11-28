import FranklRankTwoPairSaturation
import FranklCrossStarPair

/- Kernel-checked on pinned Lean 4.36 and Mathlib. -/
namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

/-- Complement relative to the supplied support, rather than relative to
some larger coordinate universe. -/
def complementOn (U : Finset α) (K : Finset (Finset α)) : Finset (Finset α) :=
  K.image (fun A => U \ A)

theorem complementOn_mem_iff {U : Finset α} {K : Finset (Finset α)} {D : Finset α}
    (hS : ∀ ⦃A⦄, A ∈ K → A ⊆ U) :
    D ∈ complementOn U K ↔ D ⊆ U ∧ U \ D ∈ K := by
  constructor
  · intro hd
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hd
    exact ⟨Finset.sdiff_subset,by simpa only [Finset.sdiff_sdiff_eq_self (hS hA)] using hA⟩
  · rintro ⟨hDU,hD⟩
    exact Finset.mem_image.mpr ⟨U \ D,hD,Finset.sdiff_sdiff_eq_self hDU⟩

theorem complementOn_card_eq {U : Finset α} {K : Finset (Finset α)}
    (hS : ∀ ⦃A⦄, A ∈ K → A ⊆ U) :
    (complementOn U K).card = K.card := by
  apply Finset.card_image_of_injOn
  intro A hA B hB he
  have hA' : A ∈ K := hA
  have hB' : B ∈ K := hB
  have hh := congrArg (fun R : Finset α => U \ R) he
  simpa only [Finset.sdiff_sdiff_eq_self (hS hA'),Finset.sdiff_sdiff_eq_self (hS hB')] using hh

theorem empty_mem_complementOn {U : Finset α} {K : Finset (Finset α)} (hU : U ∈ K) :
    (∅ : Finset α) ∈ complementOn U K :=
  Finset.mem_image.mpr ⟨U,hU,Finset.sdiff_self U⟩

theorem mem_complementOn_subset {U : Finset α} {K : Finset (Finset α)} {D : Finset α}
    (hD : D ∈ complementOn U K) : D ⊆ U := by
  obtain ⟨A,_,rfl⟩ := Finset.mem_image.mp hD
  exact Finset.sdiff_subset

theorem complementOn_interClosed {U : Finset α} {K : Finset (Finset α)}
    (hK : UnionClosed K) : FranklRankTwoAtoms.InterClosed (complementOn U K) := by
  intro D E hd he
  obtain ⟨A,ha,rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨B,hb,rfl⟩ := Finset.mem_image.mp he
  exact Finset.mem_image.mpr ⟨A ∪ B,hK ha hb,Finset.sdiff_union_distrib U A B⟩

/-- Complement reverses strict inclusion on sets inside one support. -/
theorem ssubset_of_complement_ssubset {U A B : Finset α}
    (hBU : B ⊆ U) (h : U \ A ⊂ U \ B) : B ⊂ A := by
  obtain ⟨hsub,hne⟩ := Finset.ssubset_iff_subset_ne.mp h
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_,fun e => hne (by rw [e])⟩
  intro x hx
  by_contra hnx
  have hxC := hsub (Finset.mem_sdiff.mpr ⟨hBU hx,hnx⟩)
  exact (Finset.mem_sdiff.mp hxC).2 hx

theorem complementOn_noFourChain {U : Finset α} {K : Finset (Finset α)}
    (hS : ∀ ⦃A⦄, A ∈ K → A ⊆ U) (hH : NoFourChain K) :
    FranklHeightThreeSauer.NoFourChain (complementOn U K) := by
  intro A B C D ha hb hc hd hab hbc hcd
  obtain ⟨A',ha',rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨B',hb',rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨C',hc',rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨D',hd',rfl⟩ := Finset.mem_image.mp hd
  exact hH hd' hc' hb' ha' (ssubset_of_complement_ssubset (hS hd') hcd)
    (ssubset_of_complement_ssubset (hS hc') hbc) (ssubset_of_complement_ssubset (hS hb') hab)

/-- A nonempty union-closed family's ground is its maximum member. -/
theorem ground_mem_unionClosed {K : Finset (Finset α)}
    (hK : UnionClosed K) (hn : K.Nonempty) : ground K ∈ K := by
  obtain ⟨T,hT,hTop⟩ := FranklFiberHeightSix.exists_top hK hn
  have he : T = ground K := Finset.Subset.antisymm (subset_ground hT) (Finset.sup_le (fun _ h => hTop h))
  exact he ▸ hT

/-- Take complements on the true support (the union of the family). -/
def trueComplement (K : Finset (Finset α)) : Finset (Finset α) :=
  complementOn (ground K) K

theorem trueComplement_card_eq (K : Finset (Finset α)) :
    (trueComplement K).card = K.card :=
  complementOn_card_eq (fun _ h => subset_ground h)

theorem trueComplement_interClosed {K : Finset (Finset α)} (hK : UnionClosed K) :
    FranklRankTwoAtoms.InterClosed (trueComplement K) :=
  complementOn_interClosed hK

theorem trueComplement_noFourChain {K : Finset (Finset α)} (hK : NoFourChain K) :
    FranklHeightThreeSauer.NoFourChain (trueComplement K) :=
  complementOn_noFourChain (fun _ h => subset_ground h) hK

theorem trueComplement_empty_mem {K : Finset (Finset α)}
    (hK : UnionClosed K) (hn : K.Nonempty) :
    (∅ : Finset α) ∈ trueComplement K :=
  empty_mem_complementOn (ground_mem_unionClosed hK hn)

theorem trueComplement_atom_bound {K : Finset (Finset α)}
    (hK : UnionClosed K) (hn : K.Nonempty) (hH : NoFourChain K) :
    K.card ≤ 1 + (ground K).card + (FranklRankTwoAtoms.atoms (trueComplement K)).card.choose 2 := by
  rw [← trueComplement_card_eq K]
  exact FranklRankTwoAtoms.card_le_support_add_choose_atoms
    (trueComplement_empty_mem hK hn) (trueComplement_interClosed hK)
    (trueComplement_noFourChain hH) (fun _ h => mem_complementOn_subset h)

theorem trueComplement_singleton_mem_of_large_card {K : Finset (Finset α)}
    (hK : UnionClosed K) (hn : K.Nonempty) (hH : NoFourChain K)
    (hlarge : 1 + (ground K).card + ((ground K).card - 1).choose 2 < K.card)
    {x : α} (hx : x ∈ ground K) :
    ({x} : Finset α) ∈ trueComplement K := by
  have h := FranklRankTwoAtoms.singleton_atoms_of_large_card (U := ground K)
    (trueComplement_empty_mem hK hn) (trueComplement_interClosed hK)
    (trueComplement_noFourChain hH) (fun _ h => mem_complementOn_subset h)
    (by rwa [trueComplement_card_eq])
  apply (FranklRankTwoAtoms.mem_atoms.mp ?_).1
  rw [h]
  exact Finset.mem_image_of_mem _ hx

theorem trueComplement_pair_mem_of_exact_card {K : Finset (Finset α)}
    (hK : UnionClosed K) (hn : K.Nonempty) (hH : NoFourChain K)
    (hSingle : ∀ x ∈ ground K, ({x} : Finset α) ∈ trueComplement K)
    (hcard : K.card = 1 + (ground K).card + (ground K).card.choose 2)
    {R : Finset α} (hR : R ⊆ ground K) (h2 : R.card = 2) :
    R ∈ trueComplement K :=
  FranklRankTwoAtoms.pair_mem_of_quadratic_card_eq (U := ground K)
    (trueComplement_empty_mem hK hn) (trueComplement_interClosed hK)
    (trueComplement_noFourChain hH) (fun _ h => mem_complementOn_subset h)
    hSingle (by rwa [trueComplement_card_eq]) hR h2

#print axioms complementOn_mem_iff
#print axioms complementOn_card_eq
#print axioms complementOn_interClosed
#print axioms complementOn_noFourChain
#print axioms trueComplement_atom_bound
#print axioms trueComplement_singleton_mem_of_large_card
#print axioms trueComplement_pair_mem_of_exact_card
end FranklForcingFiber
