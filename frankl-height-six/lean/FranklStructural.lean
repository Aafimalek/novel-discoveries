import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Find

namespace FranklStructuralRanks

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

#print axioms lift_step
#print axioms eraseCoordinate_noSevenChain
#print axioms minimal_no_twins
#print axioms counterexample_no_singleton
#print axioms minimal_coordinate_edge
#print axioms minimal_canonical_coordinate_edge
#print axioms coSingleton_of_no_incoming_forcing
#print axioms avoid_ssubset_of_strict_forces
#print axioms exists_minimalGround_of_counterexample
#print axioms minimal_principal_ideal_pair
#print axioms noSixForcingChain

end FranklStructuralRanks
