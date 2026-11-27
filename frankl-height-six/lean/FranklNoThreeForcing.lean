import Mathlib.Data.Nat.Find
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.ByContra

namespace FranklLocalHeightSix

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


end FranklLocalHeightSix

namespace FranklNoThreeForcing

variable {α : Type*} [DecidableEq α]

def UnionClosed (G : Finset (Finset α)) : Prop :=
  ∀ ⦃A B⦄, A ∈ G → B ∈ G → A ∪ B ∈ G

def NoSevenChain (G : Finset (Finset α)) : Prop :=
  ∀ ⦃A B C D E F H⦄, A ∈ G → B ∈ G → C ∈ G → D ∈ G →
    E ∈ G → F ∈ G → H ∈ G → A ⊂ B → B ⊂ C → C ⊂ D →
    D ⊂ E → E ⊂ F → F ⊂ H → False

def ground (G : Finset (Finset α)) : Finset α := G.sup id

def frequency (G : Finset (Finset α)) (x : α) : Nat :=
  (G.filter (x ∈ ·)).card

def Counterexample (G : Finset (Finset α)) : Prop :=
  G.Nonempty ∧ (∀ ⦃A⦄, A ∈ G → A.Nonempty) ∧ UnionClosed G ∧
  NoSevenChain G ∧ ∀ x, 2 * frequency G x < G.card

def MinimalGround (G : Finset (Finset α)) : Prop :=
  ∀ H : Finset (Finset α), Counterexample H → (ground G).card ≤ (ground H).card

def eraseCoordinate (G : Finset (Finset α)) (x : α) : Finset (Finset α) :=
  G.image (·.erase x)

/-- The occurrence of `x` forces that of `y`. -/
def Forces (G : Finset (Finset α)) (x y : α) : Prop :=
  ∀ ⦃A⦄, A ∈ G → x ∈ A → y ∈ A

theorem subset_ground {G : Finset (Finset α)} {A : Finset α} (ha : A ∈ G) :
    A ⊆ ground G :=
  Finset.le_sup (f := id) ha

theorem eraseCoordinate_unionClosed {G : Finset (Finset α)} (hG : UnionClosed G)
    (x : α) : UnionClosed (eraseCoordinate G x) := by
  intro A B ha hb
  obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hb
  exact Finset.mem_image.mpr ⟨A' ∪ B', hG hA' hB', Finset.erase_union_distrib _ _ _⟩

/-- A strict step in the projection lifts from any chosen preimage of its bottom:
join the current lift with any preimage of the larger projected set. -/
theorem lift_step {G : Finset (Finset α)} (hG : UnionClosed G) (x : α)
    {A B : Finset α} (ha : A ∈ G) (hb : B ∈ eraseCoordinate G x)
    (hab : A.erase x ⊂ B) :
    ∃ B' ∈ G, A ⊂ B' ∧ B'.erase x = B := by
  obtain ⟨C, hc, hce⟩ := Finset.mem_image.mp hb
  have hsub := (Finset.ssubset_iff_subset_ne.mp hab).1
  have he : (A ∪ C).erase x = B := by
    rw [Finset.erase_union_distrib, hce, Finset.union_eq_right.mpr hsub]
  refine ⟨A ∪ C, hG ha hc, Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩, he⟩
  intro heq
  exact (Finset.ssubset_iff_subset_ne.mp hab).2
    ((congrArg (·.erase x) heq).trans he)

theorem eraseCoordinate_noSevenChain {G : Finset (Finset α)}
    (hG : UnionClosed G) (hH : NoSevenChain G) (x : α) :
    NoSevenChain (eraseCoordinate G x) := by
  intro A B C D E F H ha hb hc hd he hf hh hab hbc hcd hde hef hfh
  obtain ⟨A', ha', hA'⟩ := Finset.mem_image.mp ha
  obtain ⟨B', hb', hab', hB'⟩ := lift_step hG x ha' hb (hA' ▸ hab)
  obtain ⟨C', hc', hbc', hC'⟩ := lift_step hG x hb' hc (hB' ▸ hbc)
  obtain ⟨D', hd', hcd', hD'⟩ := lift_step hG x hc' hd (hC' ▸ hcd)
  obtain ⟨E', he', hde', hE'⟩ := lift_step hG x hd' he (hD' ▸ hde)
  obtain ⟨F', hf', hef', hF'⟩ := lift_step hG x he' hf (hE' ▸ hef)
  obtain ⟨H', hh', hfh', _⟩ := lift_step hG x hf' hh (hF' ▸ hfh)
  exact hH ha' hb' hc' hd' he' hf' hh' hab' hbc' hcd' hde' hef' hfh'

theorem ground_eraseCoordinate_subset (G : Finset (Finset α)) (x : α) :
    ground (eraseCoordinate G x) ⊆ (ground G).erase x := by
  apply Finset.sup_le
  intro A ha
  obtain ⟨A', ha', rfl⟩ := Finset.mem_image.mp ha
  exact Finset.erase_subset_erase _ (subset_ground ha')

theorem frequency_eraseCoordinate (G : Finset (Finset α)) {x y : α}
    (hyx : y ≠ x) (hi : Set.InjOn (·.erase x) (G : Set (Finset α))) :
    frequency (eraseCoordinate G x) y = frequency G y := by
  have he : (eraseCoordinate G x).filter (y ∈ ·) =
      (G.filter (y ∈ ·)).image (·.erase x) := by
    ext A
    constructor
    · intro h
      obtain ⟨B, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).1
      exact Finset.mem_image.mpr ⟨B, Finset.mem_filter.mpr
        ⟨hb, (Finset.mem_erase.mp (Finset.mem_filter.mp h).2).2⟩, rfl⟩
    · intro h
      obtain ⟨B, hb, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨B, (Finset.mem_filter.mp hb).1, rfl⟩,
        Finset.mem_erase.mpr ⟨hyx, (Finset.mem_filter.mp hb).2⟩⟩
  unfold frequency
  rw [he]
  exact Finset.card_image_of_injOn
    (fun _ ha _ hb h => hi (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 h)

/-- A singleton member would force its element to be in at least half the family:
union with it injects the sets missing the element into the sets containing it. -/
theorem counterexample_no_singleton {G : Finset (Finset α)} (hG : Counterexample G)
    (x : α) : {x} ∉ G := by
  intro hx
  let P := G.filter (x ∈ ·)
  let Q := G.filter (x ∉ ·)
  have hmap : Set.MapsTo (insert x) (Q : Set (Finset α)) (P : Set (Finset α)) := by
    intro A ha
    have hA := Finset.mem_filter.mp (show A ∈ Q from ha)
    have hi : insert x A = {x} ∪ A := by ext z; simp
    show insert x A ∈ P
    exact Finset.mem_filter.mpr ⟨hi.symm ▸ hG.2.2.1 hx hA.1, Finset.mem_insert_self _ _⟩
  have hinj : Set.InjOn (insert x) (Q : Set (Finset α)) := by
    intro A ha B hb h
    have hAx := (Finset.mem_filter.mp (show A ∈ Q from ha)).2
    have hBx := (Finset.mem_filter.mp (show B ∈ Q from hb)).2
    have he := congrArg (·.erase x) h
    simpa only [Finset.erase_insert hAx, Finset.erase_insert hBx] using he
  have hc := Finset.card_le_card_of_injOn (insert x) hmap hinj
  have hsum : P.card + Q.card = G.card := Finset.card_filter_add_card_filter_not (x ∈ ·)
  have hfreq : 2 * P.card < G.card := hG.2.2.2.2 x
  omega

theorem counterexample_eraseCoordinate {G : Finset (Finset α)} {x : α}
    (hG : Counterexample G)
    (hi : Set.InjOn (·.erase x) (G : Set (Finset α))) :
    Counterexample (eraseCoordinate G x) := by
  have hno := counterexample_no_singleton hG x
  rcases hG with ⟨hne, hset, hu, hh, hf⟩
  refine ⟨hne.image _, ?_, eraseCoordinate_unionClosed hu x,
    eraseCoordinate_noSevenChain hu hh x, ?_⟩
  · intro A ha
    obtain ⟨B, hb, rfl⟩ := Finset.mem_image.mp ha
    by_contra hempty
    apply hno
    have he : B = {x} := by
      ext z
      simp only [Finset.mem_singleton]
      constructor
      · intro hz
        by_contra hzx
        exact hempty ⟨z, Finset.mem_erase.mpr ⟨hzx, hz⟩⟩
      · intro hzx
        obtain ⟨w, hw⟩ := hset hb
        by_cases hwx : w = x
        · exact hzx.symm ▸ hwx ▸ hw
        · exact False.elim (hempty ⟨w, Finset.mem_erase.mpr ⟨hwx, hw⟩⟩)
    exact he ▸ hb
  · intro z
    by_cases hzx : z = x
    · subst z
      have hzero : frequency (eraseCoordinate G x) x = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro A ha
        obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ha).1
        exact Finset.notMem_erase _ _ (Finset.mem_filter.mp ha).2
      rw [hzero, Nat.mul_zero]
      exact Finset.card_pos.mpr (hne.image _)
    · rw [frequency_eraseCoordinate G hzx hi]
      change 2 * frequency G z < (G.image (·.erase x)).card
      rw [Finset.card_image_of_injOn hi]
      exact hf z

theorem erase_not_injOn {G : Finset (Finset α)} {x : α}
    (hG : Counterexample G) (hmin : MinimalGround G) (hx : x ∈ ground G) :
    ¬ Set.InjOn (·.erase x) (G : Set (Finset α)) := by
  intro hi
  have hc := hmin (eraseCoordinate G x) (counterexample_eraseCoordinate hG hi)
  have hs := Finset.card_le_card (ground_eraseCoordinate_subset G x)
  have hlt := Finset.card_lt_card (Finset.erase_ssubset hx)
  exact (Nat.not_lt_of_ge (hc.trans hs)) hlt

theorem equal_of_erase_and_same_membership {A B : Finset α} {x : α}
    (he : A.erase x = B.erase x) (hmem : x ∈ A ↔ x ∈ B) : A = B := by
  ext z
  by_cases hz : z = x
  · simpa only [hz] using hmem
  · have hh : z ∈ A.erase x ↔ z ∈ B.erase x := by rw [he]
    exact ⟨fun h => (Finset.mem_erase.mp (hh.mp (Finset.mem_erase.mpr ⟨hz, h⟩))).2,
      fun h => (Finset.mem_erase.mp (hh.mpr (Finset.mem_erase.mpr ⟨hz, h⟩))).2⟩

theorem erase_injOn_of_twins {G : Finset (Finset α)} {x y : α}
    (hxy : x ≠ y) (hx : Forces G x y) (hy : Forces G y x) :
    Set.InjOn (·.erase x) (G : Set (Finset α)) := by
  intro A ha B hb he
  apply equal_of_erase_and_same_membership he
  change A.erase x = B.erase x at he
  have he' : y ∈ A.erase x ↔ y ∈ B.erase x := by rw [he]
  have hne : y ≠ x := hxy.symm
  have hmem : y ∈ A ↔ y ∈ B :=
    ⟨fun h => (Finset.mem_erase.mp (he'.mp (Finset.mem_erase.mpr ⟨hne, h⟩))).2,
      fun h => (Finset.mem_erase.mp (he'.mpr (Finset.mem_erase.mpr ⟨hne, h⟩))).2⟩
  exact ⟨fun h => hy hb (hmem.mp (hx ha h)), fun h => hy ha (hmem.mpr (hx hb h))⟩

/-- Distinct ground points of a ground-minimal counterexample are not twins. -/
theorem minimal_no_twins {G : Finset (Finset α)} {x y : α}
    (hG : Counterexample G) (hmin : MinimalGround G) (hx : x ∈ ground G)
    (hxy : x ≠ y) (hForce : Forces G x y) :
    ¬ Forces G y x := by
  intro hy
  exact erase_not_injOn hG hmin hx (erase_injOn_of_twins hxy hForce hy)

theorem eq_insert_of_erase_of_mem {A B : Finset α} {x : α}
    (he : A.erase x = B.erase x) (hx : x ∈ B) : B = insert x A := by
  apply equal_of_erase_and_same_membership
  · exact he.symm.trans (Finset.erase_insert_eq_erase _ _).symm
  · exact ⟨fun _ => Finset.mem_insert_self _ _, fun _ => hx⟩

/-- Deleting any active coordinate creates a collision in a ground-minimal
counterexample. In the original family this is a one-point edge. -/
theorem minimal_coordinate_edge {G : Finset (Finset α)} {x : α}
    (hG : Counterexample G) (hmin : MinimalGround G) (hx : x ∈ ground G) :
    ∃ A ∈ G, x ∉ A ∧ insert x A ∈ G := by
  classical
  by_contra hnone
  apply erase_not_injOn hG hmin hx
  intro A ha B hb he
  change A.erase x = B.erase x at he
  have aux {S T : Finset α} (hs : S ∈ G) (ht : T ∈ G)
      (he' : S.erase x = T.erase x) (hS : x ∉ S) (hT : x ∈ T) : False := by
    have ht' := eq_insert_of_erase_of_mem he' hT
    exact hnone ⟨S, hs, hS, ht' ▸ ht⟩
  apply equal_of_erase_and_same_membership he
  exact ⟨fun h => by
    by_contra h'
    exact aux hb ha he.symm h' h,
  fun h => by
    by_contra h'
    exact aux ha hb he h' h⟩

def avoid (G : Finset (Finset α)) (x : α) : Finset α :=
  ground (G.filter (x ∉ ·))

theorem avoid_subset {G : Finset (Finset α)} {x : α} {A : Finset α}
    (hA : A ∈ G) (hx : x ∉ A) : A ⊆ avoid G x :=
  subset_ground (Finset.mem_filter.mpr ⟨hA, hx⟩)

theorem notMem_avoid_iff_forces (G : Finset (Finset α)) (x y : α) :
    y ∉ avoid G x ↔ Forces G y x := by
  classical
  constructor
  · intro hy A hA hyA
    by_contra hxA
    exact hy (avoid_subset hA hxA hyA)
  · intro h
    have hs : avoid G x ⊆ (ground G).erase y := by
      apply Finset.sup_le
      intro A hA
      have hm := Finset.mem_filter.mp hA
      intro z hz
      refine Finset.mem_erase.mpr ⟨?_, subset_ground hm.1 hz⟩
      intro hzy
      exact hm.2 (h hm.1 (hzy ▸ hz))
    intro hy
    exact Finset.notMem_erase _ _ (hs hy)

theorem notMem_avoid (G : Finset (Finset α)) (x : α) : x ∉ avoid G x :=
  (notMem_avoid_iff_forces G x x).mpr (by intro A _ hx; exact hx)

theorem avoid_mem {G : Finset (Finset α)} (hG : Counterexample G) (x : α) :
    avoid G x ∈ G := by
  classical
  let S := G.filter (x ∉ ·)
  have hn : S.Nonempty := by
    by_contra hh
    have hmem : ∀ A ∈ G, x ∈ A := by
      intro A ha
      by_contra hA
      exact hh ⟨A, Finset.mem_filter.mpr ⟨ha, hA⟩⟩
    have hfilter : G.filter (x ∈ ·) = G := Finset.filter_eq_self.mpr hmem
    have hf := hG.2.2.2.2 x
    simp only [frequency, hfilter] at hf
    omega
  change S.sup id ∈ G
  rw [← Finset.sup'_eq_sup hn]
  exact Finset.sup'_mem (G : Set (Finset α))
    (fun _ hA _ hB => hG.2.2.1 hA hB) S hn id (fun _ hA => (Finset.mem_filter.mp hA).1)

/-- The witness edge can always be moved to the largest set avoiding that point. -/
theorem minimal_canonical_coordinate_edge {G : Finset (Finset α)} {x : α}
    (hG : Counterexample G) (hmin : MinimalGround G) (hx : x ∈ ground G) :
    avoid G x ∈ G ∧ x ∉ avoid G x ∧ insert x (avoid G x) ∈ G := by
  obtain ⟨A, hA, hAx, hIns⟩ := minimal_coordinate_edge hG hmin hx
  have hav := avoid_mem hG x
  have hl := avoid_subset hA hAx
  refine ⟨hav, notMem_avoid G x, ?_⟩
  have hEq : insert x A ∪ avoid G x = insert x (avoid G x) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_insert]
    exact ⟨fun h => h.elim (fun h' => h'.elim Or.inl (fun h'' => Or.inr (hl h''))) Or.inr,
      fun h => h.elim (fun e => Or.inl (Or.inl e)) Or.inr⟩
  exact hEq ▸ hG.2.2.1 hIns hav

/-- Ground points with no other point forcing them have a nonempty co-singleton in
the family. No co-singleton hypotheses are assumed. -/
theorem coSingleton_of_no_incoming_forcing {G : Finset (Finset α)} {x : α}
    (hG : Counterexample G)
    (h : ∀ y ∈ ground G, y ≠ x → ¬ Forces G y x) :
    (ground G).erase x ∈ G := by
  have ha := avoid_mem hG x
  have he : avoid G x = (ground G).erase x := by
    ext y
    constructor
    · intro hy
      refine Finset.mem_erase.mpr ⟨?_, subset_ground ha hy⟩
      intro hyx
      exact notMem_avoid G x (hyx ▸ hy)
    · intro hy
      obtain ⟨hyx, hground⟩ := Finset.mem_erase.mp hy
      by_contra hav
      exact h y hground hyx ((notMem_avoid_iff_forces G x y).mp hav)
  exact he ▸ ha

/-- For strictly one-way forcing, the respective largest avoiding sets are
strictly reverse ordered. -/
theorem avoid_ssubset_of_strict_forces {G : Finset (Finset α)} {x y : α}
    (hG : Counterexample G) (hxy : Forces G x y) (hyx : ¬ Forces G y x) :
    avoid G y ⊂ avoid G x := by
  classical
  have hn : x ∉ avoid G y := (notMem_avoid_iff_forces G y x).mpr hxy
  have hs := avoid_subset (avoid_mem hG y) hn
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hs, ?_⟩
  intro he
  apply hyx
  apply (notMem_avoid_iff_forces G x y).mp
  rw [← he]
  exact notMem_avoid G y

/-- Any counterexample yields one with minimum ground cardinality, without a
finiteness assumption on the ambient type. -/
theorem exists_minimalGround_of_counterexample
    {G : Finset (Finset α)} (hG : Counterexample G) :
    ∃ H : Finset (Finset α), Counterexample H ∧ MinimalGround H := by
  classical
  have hn : ∃ n : Nat, ∃ H : Finset (Finset α), Counterexample H ∧ (ground H).card = n :=
    ⟨(ground G).card, G, hG, rfl⟩
  obtain ⟨H, hH, hcard⟩ := Nat.find_spec hn
  refine ⟨H, hH, ?_⟩
  intro K hK
  rw [hcard]
  exact Nat.find_min' hn ⟨K, hK, rfl⟩

theorem ground_mem {G : Finset (Finset α)} (hG : Counterexample G) :
    ground G ∈ G := by
  unfold ground
  rw [← Finset.sup'_eq_sup hG.1]
  exact Finset.sup'_mem (G : Set (Finset α))
    (fun _ hA _ hB => hG.2.2.1 hA hB) G hG.1 id (fun _ hA => hA)

theorem avoid_ssubset_ground {G : Finset (Finset α)} {x : α}
    (hG : Counterexample G) (hx : x ∈ ground G) : avoid G x ⊂ ground G := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_ground (avoid_mem hG x), ?_⟩
  intro he
  exact notMem_avoid G x (he.symm ▸ hx)

/-- In the complement family, each principal forcing ideal and that ideal with its
generator removed are represented. -/
theorem minimal_principal_ideal_pair {G : Finset (Finset α)} {x : α}
    (hG : Counterexample G) (hmin : MinimalGround G) (hx : x ∈ ground G) :
    ∃ D ∈ G.image (fun A => ground G \ A),
      D.erase x ∈ G.image (fun A => ground G \ A) ∧
      ∀ y, y ∈ D ↔ y ∈ ground G ∧ Forces G y x := by
  obtain ⟨ha, _, hi⟩ := minimal_canonical_coordinate_edge hG hmin hx
  refine ⟨ground G \ avoid G x, Finset.mem_image.mpr ⟨_, ha, rfl⟩, ?_, ?_⟩
  · refine Finset.mem_image.mpr ⟨_, hi, ?_⟩
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    tauto
  · intro y
    simp only [Finset.mem_sdiff, notMem_avoid_iff_forces]

theorem avoid_ssubset_of_forces_minimal {G : Finset (Finset α)} {x y : α}
    (hG : Counterexample G) (hmin : MinimalGround G) (hx : x ∈ ground G)
    (hxy : x ≠ y) (hf : Forces G x y) :
    avoid G y ⊂ avoid G x :=
  avoid_ssubset_of_strict_forces hG hf (minimal_no_twins hG hmin hx hxy hf)

/-- There cannot be a chain of six successively distinct ground points under
forcing in a minimal counterexample: their reversed avoidance sets followed by
the ground would be a seven-member chain. -/
theorem noSixForcingChain {G : Finset (Finset α)}
    (hG : Counterexample G) (hmin : MinimalGround G)
    {a b c d e f : α}
    (ha : a ∈ ground G) (hb : b ∈ ground G) (hc : c ∈ ground G)
    (hd : d ∈ ground G) (he : e ∈ ground G)
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) (hef : e ≠ f)
    (fab : Forces G a b) (fbc : Forces G b c) (fcd : Forces G c d)
    (fde : Forces G d e) (fef : Forces G e f) : False :=
  hG.2.2.2.1 (avoid_mem hG f) (avoid_mem hG e) (avoid_mem hG d)
    (avoid_mem hG c) (avoid_mem hG b) (avoid_mem hG a) (ground_mem hG)
    (avoid_ssubset_of_forces_minimal hG hmin he hef fef)
    (avoid_ssubset_of_forces_minimal hG hmin hd hde fde)
    (avoid_ssubset_of_forces_minimal hG hmin hc hcd fcd)
    (avoid_ssubset_of_forces_minimal hG hmin hb hbc fbc)
    (avoid_ssubset_of_forces_minimal hG hmin ha hab fab)
    (avoid_ssubset_ground hG ha)


def Separated (G : Finset (Finset α)) : Prop :=
  ∀ ⦃x y⦄, x ∈ ground G → x ≠ y → Forces G x y → ¬ Forces G y x

def Terminal (G : Finset (Finset α)) (x : α) : Prop :=
  ∀ ⦃y⦄, Forces G x y → y = x

omit [DecidableEq α] in
theorem forces_refl (G : Finset (Finset α)) (x : α) : Forces G x x := by
  intro A _ hx; exact hx

omit [DecidableEq α] in
theorem forces_trans {G : Finset (Finset α)} {x y z : α}
    (hxy : Forces G x y) (hyz : Forces G y z) : Forces G x z := by
  intro A ha hx
  exact hyz ha (hxy ha hx)

theorem exists_mem_of_mem_ground {G : Finset (Finset α)} {x : α}
    (hx : x ∈ ground G) : ∃ A ∈ G, x ∈ A := by
  classical
  by_contra hn
  have hsub : ground G ⊆ (ground G).erase x := by
    apply Finset.sup_le
    intro A ha y hy
    refine Finset.mem_erase.mpr ⟨?_, subset_ground ha hy⟩
    intro e
    exact hn ⟨A, ha, e ▸ hy⟩
  exact Finset.notMem_erase _ _ (hsub hx)

theorem mem_ground_of_forces {G : Finset (Finset α)} {x y : α}
    (hx : x ∈ ground G) (hf : Forces G x y) : y ∈ ground G := by
  obtain ⟨A, ha, hxa⟩ := exists_mem_of_mem_ground hx
  exact subset_ground ha (hf ha hxa)

theorem frequency_lt_of_forces {G : Finset (Finset α)} {x y : α}
    (hxy : Forces G x y) (hyx : ¬ Forces G y x) : frequency G x < frequency G y := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro A ha
    obtain ⟨hA, hx⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨hA, hxy hA hx⟩
  · intro he
    apply hyx
    intro A ha hy
    have hh : A ∈ G.filter (y ∈ ·) := Finset.mem_filter.mpr ⟨ha, hy⟩
    rw [← he] at hh
    exact (Finset.mem_filter.mp hh).2

theorem terminal_above {G : Finset (Finset α)} {x : α}
    (hsep : Separated G) (hx : x ∈ ground G) :
    ∃ s ∈ ground G, Forces G x s ∧ Terminal G s := by
  classical
  let S := (ground G).filter (Forces G x)
  have hS : S.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨hx, forces_refl G x⟩⟩
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image S (frequency G) hS
  obtain ⟨hsg, hxs⟩ := Finset.mem_filter.mp hs
  refine ⟨s, hsg, hxs, ?_⟩
  intro y hsy
  by_contra hne
  have hyS : y ∈ S := Finset.mem_filter.mpr ⟨mem_ground_of_forces hsg hsy, forces_trans hxs hsy⟩
  exact (Nat.not_lt_of_ge (hmax y hyS))
    (frequency_lt_of_forces hsy (hsep hsg (Ne.symm hne) hsy))

/-- The weak frequency bound allows points occurring in exactly half the members. -/
def NoStrictMajority (G : Finset (Finset α)) : Prop :=
  G.Nonempty ∧ (∀ ⦃A⦄, A ∈ G → A.Nonempty) ∧ UnionClosed G ∧
  NoSevenChain G ∧ ∀ x, 2 * frequency G x ≤ G.card

theorem Counterexample.noStrictMajority {G : Finset (Finset α)}
    (hG : Counterexample G) : NoStrictMajority G :=
  ⟨hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1, fun x => Nat.le_of_lt (hG.2.2.2.2 x)⟩

theorem avoid_mem_weak {G : Finset (Finset α)} (hG : NoStrictMajority G) (x : α) :
    avoid G x ∈ G := by
  classical
  let S := G.filter (x ∉ ·)
  have hn : S.Nonempty := by
    by_contra hh
    have hmem : ∀ A ∈ G, x ∈ A := by
      intro A ha
      by_contra hA
      exact hh ⟨A, Finset.mem_filter.mpr ⟨ha, hA⟩⟩
    have hfilter : G.filter (x ∈ ·) = G := Finset.filter_eq_self.mpr hmem
    have hf := hG.2.2.2.2 x
    simp only [frequency, hfilter] at hf
    have hpos := Finset.card_pos.mpr hG.1
    omega
  change S.sup id ∈ G
  rw [← Finset.sup'_eq_sup hn]
  exact Finset.sup'_mem (G : Set (Finset α))
    (fun _ hA _ hB => hG.2.2.1 hA hB) S hn id (fun _ hA => (Finset.mem_filter.mp hA).1)

theorem ground_mem_weak {G : Finset (Finset α)} (hG : NoStrictMajority G) :
    ground G ∈ G := by
  unfold ground
  rw [← Finset.sup'_eq_sup hG.1]
  exact Finset.sup'_mem (G : Set (Finset α))
    (fun _ hA _ hB => hG.2.2.1 hA hB) G hG.1 id (fun _ hA => hA)

theorem avoid_ssubset_ground_weak {G : Finset (Finset α)} {x : α}
    (hG : NoStrictMajority G) (hx : x ∈ ground G) : avoid G x ⊂ ground G := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_ground (avoid_mem_weak hG x), ?_⟩
  intro he
  exact notMem_avoid G x (he.symm ▸ hx)

theorem avoid_ssubset_of_strict_forces_weak {G : Finset (Finset α)} {x y : α}
    (hG : NoStrictMajority G) (hxy : Forces G x y) (hyx : ¬ Forces G y x) :
    avoid G y ⊂ avoid G x := by
  classical
  have hn : x ∉ avoid G y := (notMem_avoid_iff_forces G y x).mpr hxy
  have hs := avoid_subset (avoid_mem_weak hG y) hn
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hs, ?_⟩
  intro he
  apply hyx
  apply (notMem_avoid_iff_forces G x y).mp
  rw [← he]
  exact notMem_avoid G y

theorem other_terminal {G : Finset (Finset α)} {s : α}
    (hG : NoStrictMajority G) (hsep : Separated G) :
    ∃ t ∈ avoid G s, Terminal G t := by
  classical
  have ha := avoid_mem_weak hG s
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image (avoid G s) (frequency G) (hG.2.1 ha)
  refine ⟨t, ht, ?_⟩
  intro y hty
  by_contra hne
  exact (Nat.not_lt_of_ge (hmax y (hty ha ht)))
    (frequency_lt_of_forces hty (hsep (subset_ground ha ht) (Ne.symm hne) hty))

theorem avoid_injOn_ground {G : Finset (Finset α)} (hsep : Separated G) :
    Set.InjOn (avoid G) (ground G : Set α) := by
  intro x hx y _ he
  by_contra hne
  have hxy : Forces G x y := (notMem_avoid_iff_forces G y x).mp (he ▸ notMem_avoid G x)
  have hyx : Forces G y x := (notMem_avoid_iff_forces G x y).mp (he.symm ▸ notMem_avoid G y)
  exact hsep hx hne hxy hyx

theorem both_count_le_neither_count {G : Finset (Finset α)} {s t : α}
    (hs : 2 * frequency G s ≤ G.card) (ht : 2 * frequency G t ≤ G.card) :
    (G.filter (fun A => s ∈ A ∧ t ∈ A)).card ≤
      (G.filter (fun A => ¬ (s ∈ A ∨ t ∈ A))).card := by
  let P := G.filter (s ∈ ·)
  let Q := G.filter (t ∈ ·)
  have hu : P ∪ Q = G.filter (fun A => s ∈ A ∨ t ∈ A) := by
    ext A
    simp only [P, Q, Finset.mem_union, Finset.mem_filter]
    tauto
  have hi : P ∩ Q = G.filter (fun A => s ∈ A ∧ t ∈ A) := by
    ext A
    simp only [P, Q, Finset.mem_inter, Finset.mem_filter]
    tauto
  have hc := Finset.card_union_add_card_inter P Q
  rw [hu, hi] at hc
  have hp := Finset.card_filter_add_card_filter_not (s := G) (fun A => s ∈ A ∨ t ∈ A)
  change 2 * P.card ≤ G.card at hs
  change 2 * Q.card ≤ G.card at ht
  omega

theorem ground_subfilter (G : Finset (Finset α)) (P : Finset α → Prop) [DecidablePred P] :
    ground (G.filter P) ⊆ ground G := by
  apply Finset.sup_le
  intro A hA
  exact subset_ground (Finset.mem_filter.mp hA).1

theorem noThreeForcingChain_of_separated {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hsep : Separated G)
    {p q r : α} (hp : p ∈ ground G) (hpq : p ≠ q) (hqr : q ≠ r)
    (fpq : Forces G p q) (fqr : Forces G q r) : False := by
  classical
  have hq := mem_ground_of_forces hp fpq
  have hr := mem_ground_of_forces hq fqr
  obtain ⟨s, hs, hrs, hsTerm⟩ := terminal_above hsep hr
  have fqs := forces_trans fqr hrs
  have fps := forces_trans fpq fqs
  have hsq : s ≠ q := by
    intro e
    subst s
    exact hqr (hsTerm fqr).symm
  have hsp : s ≠ p := by
    intro e
    subst s
    exact hpq (hsTerm fpq).symm
  obtain ⟨t, ht, htTerm⟩ := other_terminal (s := s) hG hsep
  have hts : t ≠ s := fun e => notMem_avoid G s (e ▸ ht)
  have htG := subset_ground (avoid_mem_weak hG s) ht
  have htp : t ≠ p := fun e => hts (e.symm ▸ (htTerm (e.symm ▸ fps)).symm)
  have htq : t ≠ q := fun e => hts (e.symm ▸ (htTerm (e.symm ▸ fqs)).symm)
  let V := ((ground G).erase s).erase t
  let P := G.filter (fun A => s ∈ A ∧ t ∈ A)
  let N := G.filter (fun A => ¬ (s ∈ A ∨ t ∈ A))
  have hV (v : α) (hv : v ∈ V) : v ∈ ground G ∧ v ≠ s ∧ v ≠ t := by
    obtain ⟨hvt, hv'⟩ := Finset.mem_erase.mp hv
    obtain ⟨hvs, hvg⟩ := Finset.mem_erase.mp hv'
    exact ⟨hvg, hvs, hvt⟩
  have hmaps : Set.MapsTo (avoid G) (V : Set α) (P.erase (ground G) : Set (Finset α)) := by
    intro v hv
    obtain ⟨hvg, hvs, hvt⟩ := hV v hv
    have hsv : s ∈ avoid G v := by
      by_contra hn
      exact hvs (hsTerm ((notMem_avoid_iff_forces G v s).mp hn))
    have htv : t ∈ avoid G v := by
      by_contra hn
      exact hvt (htTerm ((notMem_avoid_iff_forces G v t).mp hn))
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨avoid_mem_weak hG v, hsv, htv⟩⟩
    intro he
    exact notMem_avoid G v (he.symm ▸ hvg)
  have hVcard := Finset.card_le_card_of_injOn (avoid G) hmaps
    (fun a ha b hb he => avoid_injOn_ground hsep (hV a ha).1 (hV b hb).1 he)
  have hTopP : ground G ∈ P := Finset.mem_filter.mpr ⟨ground_mem_weak hG, hs, htG⟩
  have hPcard := Finset.card_erase_add_one hTopP
  have hV0 := Finset.card_erase_add_one hs
  have hV1 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hts, htG⟩)
  change V.card + 1 = ((ground G).erase s).card at hV1
  have hPN : P.card ≤ N.card :=
    both_count_le_neither_count (hG.2.2.2.2 s) (hG.2.2.2.2 t)
  have hn : N.Nonempty := Finset.card_pos.mp (by omega)
  let T := ground N
  have hT : T ∈ G := by
    change N.sup id ∈ G
    rw [← Finset.sup'_eq_sup hn]
    exact Finset.sup'_mem (G : Set (Finset α))
      (fun _ hA _ hB => hG.2.2.1 hA hB) N hn id (fun _ hA => (Finset.mem_filter.mp hA).1)
  have hsub : T ⊆ avoid G s := by
    apply Finset.sup_le
    intro A ha
    obtain ⟨hA, hno⟩ := Finset.mem_filter.mp ha
    exact avoid_subset hA (fun hh => hno (Or.inl hh))
  have hAbs (x : α) (hF : Forces G x s ∨ Forces G x t) : x ∉ T := by
    intro hx'
    obtain ⟨A, hAN, hAx⟩ := exists_mem_of_mem_ground hx'
    obtain ⟨hAG, hno⟩ := Finset.mem_filter.mp hAN
    exact hno (hF.elim (fun hf => Or.inl (hf hAG hAx)) (fun hf => Or.inr (hf hAG hAx)))
  have hTs : T ⊂ avoid G s :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun he => hAbs t (Or.inr (forces_refl G t)) (he.symm ▸ ht)⟩
  have hsq' := avoid_ssubset_of_strict_forces_weak hG fqs (hsep hq hsq.symm fqs)
  have hqp' := avoid_ssubset_of_strict_forces_weak hG fpq (hsep hp hpq fpq)
  have hpU := avoid_ssubset_ground_weak hG hp
  have hHeight := FranklLocalHeightSix.card_subsets_le_of_four_extensions
    hG.2.2.1 hG.2.2.2.1 hT (avoid_mem_weak hG s) (avoid_mem_weak hG q) (avoid_mem_weak hG p)
    (ground_mem_weak hG) hTs hsq' hqp' hpU
  have hNle : N.card ≤ (G.filter (fun A => A ⊆ T)).card := by
    apply Finset.card_le_card
    intro A ha
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1, subset_ground ha⟩
  let W := V.erase p |>.erase q
  have hW : T ⊆ W := by
    intro x hx
    have hneq (y : α) (hy : y ∉ T) : x ≠ y := fun e => hy (e ▸ hx)
    exact Finset.mem_erase.mpr ⟨hneq q (hAbs q (Or.inl fqs)),
      Finset.mem_erase.mpr ⟨hneq p (hAbs p (Or.inl fps)),
        Finset.mem_erase.mpr ⟨hneq t (hAbs t (Or.inr (forces_refl G t))),
          Finset.mem_erase.mpr ⟨hneq s (hAbs s (Or.inl (forces_refl G s))), subset_ground hT hx⟩⟩⟩⟩
  have hW0 := Finset.card_erase_add_one (show p ∈ V from
    Finset.mem_erase.mpr ⟨htp.symm, Finset.mem_erase.mpr ⟨hsp.symm, hp⟩⟩)
  have hW1 := Finset.card_erase_add_one (show q ∈ V.erase p from
    Finset.mem_erase.mpr ⟨hpq.symm, Finset.mem_erase.mpr ⟨htq.symm, Finset.mem_erase.mpr ⟨hsq.symm, hq⟩⟩⟩)
  change W.card + 1 = (V.erase p).card at hW1
  have hWcard := Finset.card_le_card hW
  omega

theorem minimal_noThreeForcingChain {G : Finset (Finset α)}
    (hG : Counterexample G) (hmin : MinimalGround G)
    {p q r : α} (hp : p ∈ ground G) (hpq : p ≠ q) (hqr : q ≠ r)
    (fpq : Forces G p q) (fqr : Forces G q r) : False :=
  noThreeForcingChain_of_separated hG.noStrictMajority (by intro x y hx hxy hf; exact minimal_no_twins hG hmin hx hxy hf) hp hpq hqr fpq fqr

def WeakMinimalGround (G : Finset (Finset α)) : Prop :=
  ∀ H : Finset (Finset α), NoStrictMajority H → (ground G).card ≤ (ground H).card

theorem noStrictMajority_erase_twin {G : Finset (Finset α)} {x y : α}
    (hG : NoStrictMajority G) (hxy : x ≠ y) (hf : Forces G x y) (hr : Forces G y x) :
    NoStrictMajority (eraseCoordinate G x) := by
  have hi := erase_injOn_of_twins hxy hf hr
  rcases hG with ⟨hne, hset, hu, hh, hfreq⟩
  refine ⟨hne.image _, ?_, eraseCoordinate_unionClosed hu x,
    eraseCoordinate_noSevenChain hu hh x, ?_⟩
  · intro A ha
    obtain ⟨B, hb, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨z, hz⟩ := hset hb
    by_cases hzx : z = x
    · exact ⟨y, Finset.mem_erase.mpr ⟨hxy.symm, hf hb (hzx ▸ hz)⟩⟩
    · exact ⟨z, Finset.mem_erase.mpr ⟨hzx, hz⟩⟩
  · intro z
    by_cases hzx : z = x
    · subst z
      have hzero : frequency (eraseCoordinate G x) x = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro A ha
        obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ha).1
        exact Finset.notMem_erase _ _ (Finset.mem_filter.mp ha).2
      simp [hzero]
    · rw [frequency_eraseCoordinate G hzx hi]
      change 2 * frequency G z ≤ (G.image (·.erase x)).card
      rw [Finset.card_image_of_injOn hi]
      exact hfreq z

theorem weakMinimalGround_separated {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) : Separated G := by
  intro x y hx hxy hf hr
  have hc := hmin (eraseCoordinate G x) (noStrictMajority_erase_twin hG hxy hf hr)
  have hs := Finset.card_le_card (ground_eraseCoordinate_subset G x)
  have hlt := Finset.card_lt_card (Finset.erase_ssubset hx)
  exact (Nat.not_lt_of_ge (hc.trans hs)) hlt

theorem exists_weakMinimalGround_of_noStrictMajority {G : Finset (Finset α)}
    (hG : NoStrictMajority G) :
    ∃ H : Finset (Finset α), NoStrictMajority H ∧ WeakMinimalGround H := by
  classical
  have hn : ∃ n : Nat, ∃ H : Finset (Finset α), NoStrictMajority H ∧ (ground H).card = n :=
    ⟨(ground G).card, G, hG, rfl⟩
  obtain ⟨H, hH, hcard⟩ := Nat.find_spec hn
  refine ⟨H, hH, ?_⟩
  intro K hK
  rw [hcard]
  exact Nat.find_min' hn ⟨K, hK, rfl⟩

/-- Any counterexample to the strict-majority variant yields a separating
counterexample with no three-point forcing chain, without any assumption on
parity or the existence of an exact-half frequency. -/
theorem exists_noThree_reduction_of_noStrictMajority {G : Finset (Finset α)}
    (hG : NoStrictMajority G) :
    ∃ H : Finset (Finset α), NoStrictMajority H ∧ Separated H ∧
      ∀ ⦃p q r⦄, p ∈ ground H → p ≠ q → q ≠ r → Forces H p q → Forces H q r → False := by
  obtain ⟨H, hH, hmin⟩ := exists_weakMinimalGround_of_noStrictMajority hG
  have hsep := weakMinimalGround_separated hH hmin
  exact ⟨H, hH, hsep, fun _ _ _ h1 h2 h3 h4 h5 =>
    noThreeForcingChain_of_separated hH hsep h1 h2 h3 h4 h5⟩

#print axioms noThreeForcingChain_of_separated
#print axioms minimal_noThreeForcingChain
#print axioms weakMinimalGround_separated
#print axioms exists_noThree_reduction_of_noStrictMajority
end FranklNoThreeForcing
