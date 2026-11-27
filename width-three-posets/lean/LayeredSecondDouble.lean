import ForkDiamond

namespace WidthThree

noncomputable section

universe u

variable {α : Type u} [PartialOrder α] {n : ℕ} [Fintype α]

/-- The first three candidates form a fork; the shared upper tail may have arbitrary size. -/
structure FrontForkShape (a b x y : α) (tail : Finset α) : Prop where
  b_lt_x : b < x
  b_lt_y : b < y
  x_ne_y : x ≠ y
  tailAbove : ∀ z ∈ tail, x < z ∧ y < z
  describe : ∀ z, Branch a b z ↔ z = b ∨ z = x ∨ z = y ∨ z ∈ tail

private theorem FrontForkShape.swap {a b x y : α} {tail : Finset α}
    (hF : FrontForkShape a b x y tail) : FrontForkShape a b y x tail :=
  ⟨hF.b_lt_y, hF.b_lt_x, hF.x_ne_y.symm, 
    fun z hz => ⟨(hF.tailAbove z hz).2, (hF.tailAbove z hz).1⟩, fun z => by
      rw [hF.describe]
      tauto⟩

private theorem FrontForkShape.b_mem {a b x y : α} {tail : Finset α}
    (hF : FrontForkShape a b x y tail) : Branch a b b :=
  (hF.describe b).mpr (Or.inl rfl)

private theorem FrontForkShape.x_mem {a b x y : α} {tail : Finset α}
    (hF : FrontForkShape a b x y tail) : Branch a b x :=
  (hF.describe x).mpr (Or.inr (Or.inl rfl))

private theorem FrontForkShape.y_mem {a b x y : α} {tail : Finset α}
    (hF : FrontForkShape a b x y tail) : Branch a b y := hF.swap.x_mem

private theorem front_index_le_one {a b x y : α} {tail : Finset α}
    (hF : FrontForkShape a b x y tail) {R : Ranking α n}
    (hax : R.rank a < R.rank x) (hay : R.rank a < R.rank y) :
    index a b R ≤ 1 := by
  classical
  have hsub : beforeSet R a (Branch a b) ⊆ {b} := by
    intro z hz
    obtain ⟨hzS, hr⟩ := mem_beforeSet.mp hz
    rcases (hF.describe z).mp hzS with e | e | e | ht
    · simpa [e]
    · subst z
      exact ((not_lt_of_ge (le_of_lt hax)) hr).elim
    · subst z
      exact ((not_lt_of_ge (le_of_lt hay)) hr).elim
    · exact ((not_lt_of_ge (le_of_lt (hax.trans (R.mono (hF.tailAbove z ht).1)))) hr).elim
  simpa only [Finset.card_singleton] using Finset.card_le_card hsub

private theorem front_two_le {a b x y : α} {tail : Finset α}
    (hF : FrontForkShape a b x y tail) {R : Ranking α n}
    (hxa : R.rank x < R.rank a) : 2 ≤ index a b R := by
  classical
  have hb : b ∈ beforeSet R a (Branch a b) :=
    mem_beforeSet.mpr ⟨hF.b_mem, (R.mono hF.b_lt_x).trans hxa⟩
  have hx : x ∈ beforeSet R a (Branch a b) := mem_beforeSet.mpr ⟨hF.x_mem, hxa⟩
  have hs : ({b, x} : Finset α) ⊆ beforeSet R a (Branch a b) := by
    intro z hz
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hz : z = b ∨ z = x) with e | e
    · simpa [e] using hb
    · simpa [e] using hx
  have hc : ({b, x} : Finset α).card = 2 := by
    simp [ne_of_lt hF.b_lt_x]
  simpa only [hc] using Finset.card_le_card hs

private theorem front_beforeBoth_iff {a b x y : α} {tail : Finset α}
    (hba : ¬ b ≤ a) (hF : FrontForkShape a b x y tail) {R : Ranking α n} :
    (R.rank a < R.rank x ∧ R.rank a < R.rank y) ↔ index a b R < 2 := by
  constructor
  · intro h
    have hh := front_index_le_one hF h.1 h.2
    omega
  · intro h
    constructor
    · by_contra hn
      have hh := front_two_le hF
        (lt_of_not_rank_lt (branch_ne_a hba hF.x_mem).symm hn)
      omega
    · by_contra hn
      have hh := front_two_le hF.swap
        (lt_of_not_rank_lt (branch_ne_a hba hF.y_mem).symm hn)
      omega

private theorem front_middle_forward {a b x y : α} {tail : Finset α}
    (hF : FrontForkShape a b x y tail) {R : Ranking α n}
    (hxa : R.rank x < R.rank a) (hay : R.rank a < R.rank y) :
    index a b R = 2 := by
  classical
  have heq : beforeSet R a (Branch a b) = {b, x} := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzS, hr⟩ := mem_beforeSet.mp hz
      rcases (hF.describe z).mp hzS with e | e | e | ht
      · simp [e]
      · simp [e]
      · subst z
        exact ((not_lt_of_ge (le_of_lt hay)) hr).elim
      · exact ((not_lt_of_ge (le_of_lt (hay.trans (R.mono (hF.tailAbove z ht).2)))) hr).elim
    · intro hz
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hz : z = b ∨ z = x) with e | e
      · subst z
        exact mem_beforeSet.mpr ⟨hF.b_mem, (R.mono hF.b_lt_x).trans hxa⟩
      · subst z
        exact mem_beforeSet.mpr ⟨hF.x_mem, hxa⟩
  change (beforeSet R a (Branch a b)).card = 2
  rw [heq]
  simp [ne_of_lt hF.b_lt_x]

private theorem front_minority_middle_le {a b x y : α} {tail : Finset α}
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b) (hF : FrontForkShape a b x y tail) :
    3 * eventCard (fun R : Ranking α n => index a b R = 2 ∧ R.rank y < R.rank x) ≤
      pairCount y x n := by
  let E : Ranking α n → Prop := fun R => R.rank y < R.rank x
  have hE : BranchOrderInvariant a b E := by
    intro R T h he
    exact (h y x hF.y_mem hF.x_mem).mp he
  let q (k : ℕ) := Nat.card (BinGiven a b k E)
  have hone (k : ℕ) : q (k + 1) ≤ q k := natCard_binGiven_succ_le a b hba hd k E hE
  have hsum := sum_fibers_le (fun R : Ranking α n => index a b R) E 3
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
  change q 0 + (q 1 + q 2) ≤ pairCount y x n at hsum
  change 3 * q 2 ≤ pairCount y x n
  have h01 : q 1 ≤ q 0 := hone 0
  have h12 : q 2 ≤ q 1 := hone 1
  omega

private theorem front_three_le_of_both_before
    {a b x y : α} {tail : Finset α} (hF : FrontForkShape a b x y tail)
    {R : Ranking α n} (hxa : R.rank x < R.rank a) (hya : R.rank y < R.rank a) :
    3 ≤ index a b R := by
  classical
  have hb : b ∈ beforeSet R a (Branch a b) :=
    mem_beforeSet.mpr ⟨hF.b_mem, (R.mono hF.b_lt_x).trans hxa⟩
  have hx : x ∈ beforeSet R a (Branch a b) := mem_beforeSet.mpr ⟨hF.x_mem, hxa⟩
  have hy : y ∈ beforeSet R a (Branch a b) := mem_beforeSet.mpr ⟨hF.y_mem, hya⟩
  have hs : ({b, x, y} : Finset α) ⊆ beforeSet R a (Branch a b) := by
    intro z hz
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hz :
      z = b ∨ z = x ∨ z = y) with e | e | e
    · subst z; exact hb
    · subst z; exact hx
    · subst z; exact hy
  have hc : ({b, x, y} : Finset α).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨ne_of_lt hF.b_lt_x, ne_of_lt hF.b_lt_y, hF.x_ne_y⟩
  simpa only [hc] using Finset.card_le_card hs

private theorem front_middle_iff {a b x y : α} {tail : Finset α}
    (hba : ¬ b ≤ a) (hF : FrontForkShape a b x y tail) {R : Ranking α n} :
    (R.rank a < R.rank x ∧ ¬ R.rank a < R.rank y) ↔
      (index a b R = 2 ∧ R.rank y < R.rank x) := by
  constructor
  · rintro ⟨hax, hnay⟩
    have hya := lt_of_not_rank_lt (branch_ne_a hba hF.y_mem).symm hnay
    exact ⟨front_middle_forward hF.swap hya hax, hya.trans hax⟩
  · rintro ⟨hc, hyx⟩
    have hax : R.rank a < R.rank x := by
      by_contra hn
      have hxa := lt_of_not_rank_lt (branch_ne_a hba hF.x_mem).symm hn
      have h3 := front_three_le_of_both_before hF hxa (hyx.trans hxa)
      omega
    refine ⟨hax, ?_⟩
    intro hay
    have h1 := front_index_le_one hF hax hay
    omega

private theorem front_pair_count_split {a b x y : α} {tail : Finset α}
    (hba : ¬ b ≤ a) (hF : FrontForkShape a b x y tail) :
    pairCount a x n = prefixCount a b 2 n +
      eventCard (fun R : Ranking α n => index a b R = 2 ∧ R.rank y < R.rank x) := by
  have h := eventCard_split (fun R : Ranking α n => R.rank a < R.rank x)
    (fun R : Ranking α n => R.rank a < R.rank y)
  have hboth : eventCard (fun R : Ranking α n => R.rank a < R.rank x ∧ R.rank a < R.rank y) =
      prefixCount a b 2 n := eventCard_congr (fun _ => front_beforeBoth_iff hba hF)
  have hmid : eventCard (fun R : Ranking α n => R.rank a < R.rank x ∧ ¬ R.rank a < R.rank y) =
      eventCard (fun R : Ranking α n => index a b R = 2 ∧ R.rank y < R.rank x) :=
    eventCard_congr (fun _ => front_middle_iff hba hF)
  rw [hboth, hmid] at h
  exact h

private theorem front_pair_bin_split {a b x y : α} {tail : Finset α}
    (hF : FrontForkShape a b x y tail) :
    Nat.card (Bin a b 2 n) =
      eventCard (fun R : Ranking α n => index a b R = 2 ∧ R.rank y < R.rank x) +
      eventCard (fun R : Ranking α n => index a b R = 2 ∧ R.rank x < R.rank y) := by
  have h := eventCard_split (fun R : Ranking α n => index a b R = 2)
    (fun R : Ranking α n => R.rank y < R.rank x)
  have he : eventCard (fun R : Ranking α n => index a b R = 2 ∧ ¬ R.rank y < R.rank x) =
      eventCard (fun R : Ranking α n => index a b R = 2 ∧ R.rank x < R.rank y) := by
    apply eventCard_congr
    intro R
    constructor
    · exact fun h => ⟨h.1, lt_of_not_rank_lt hF.x_ne_y.symm h.2⟩
    · exact fun h => ⟨h.1, lt_asymm h.2⟩
  rw [he] at h
  exact h

private theorem prefixCount_two_eq {a b : α} :
    prefixCount a b 2 n = Nat.card (Bin a b 0 n) + Nat.card (Bin a b 1 n) := by
  have hzero : prefixCount a b 0 n = 0 := by
    apply Finite.card_eq_zero_iff.mpr
    exact ⟨fun t => (Nat.not_lt_zero _) t.property⟩
  have h0 : prefixCount a b 1 n = prefixCount a b 0 n + Nat.card (Bin a b 0 n) :=
    prefixCount_succ a b 0
  have h1 : prefixCount a b 2 n = prefixCount a b 1 n + Nat.card (Bin a b 1 n) :=
    prefixCount_succ a b 1
  omega

private theorem front_prefixFive_le_sum {a b x y : α} {tail : Finset α}
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b)
    (hF : FrontForkShape a b x y tail) :
    prefixCount a b 5 n ≤ pairCount a x n + pairCount a y n := by
  let q (k : ℕ) := Nat.card (Bin a b k n)
  have hq : Antitone q := antitone_nat_of_succ_le (fun i => natCard_bin_succ_le a b hba hd i)
  have h01 : q 1 ≤ q 0 := hq (by omega)
  have h12 : q 2 ≤ q 1 := hq (by omega)
  have h23 : q 3 ≤ q 2 := hq (by omega)
  have h34 : q 4 ≤ q 3 := hq (by omega)
  have hp2 : prefixCount a b 2 n = q 0 + q 1 := prefixCount_two_eq
  have hp3 : prefixCount a b 3 n = prefixCount a b 2 n + q 2 := prefixCount_succ a b 2
  have hp4 : prefixCount a b 4 n = prefixCount a b 3 n + q 3 := prefixCount_succ a b 3
  have hp5 : prefixCount a b 5 n = prefixCount a b 4 n + q 4 := prefixCount_succ a b 4
  have hx := front_pair_count_split (n := n) hba hF
  have hy := front_pair_count_split (n := n) hba hF.swap
  have hb := front_pair_bin_split (n := n) hF
  change q 2 = _ at hb
  omega

private theorem front_double_low {a b x y : α} {tail : Finset α}
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b)
    (hF : FrontForkShape a b x y tail)
    (hp : 18 * pairCount a b n ≤ 5 * Nat.card (Ranking α n))
    (hn : ¬ ∃ u v : α, Balanced u v n) :
    3 * pairCount a x n < Nat.card (Ranking α n) ∧
      3 * pairCount a y n < Nat.card (Ranking α n) := by
  let N := Nat.card (Ranking α n)
  let A := prefixCount a b 2 n
  let q (k : ℕ) := Nat.card (Bin a b k n)
  have hq : Antitone q := antitone_nat_of_succ_le (fun i => natCard_bin_succ_le a b hba hd i)
  have hp2 : A = q 0 + q 1 := prefixCount_two_eq
  have hp0 : q 0 = pairCount a b n := eventCard_congr (fun _ => index_zero_iff hba hF.b_mem)
  have hq10 : q 1 ≤ q 0 := hq (by omega)
  have hq20 : q 2 ≤ q 0 := hq (by omega)
  have hA : A ≤ 2 * pairCount a b n := by omega
  have side (u v : α) (h : u ≠ v) :
      3 * pairCount u v n < N ∨ 2 * N < 3 * pairCount u v n := by
    by_contra! h'
    exact hn ⟨u, v, h, h'.1, h'.2⟩
  have hmakes (u v : α) (hS : FrontForkShape a b u v tail)
      (hm : 3 * pairCount v u n < N) :
      3 * pairCount a u n < N ∧ 3 * pairCount a v n < N := by
    let Cuv := eventCard (fun R : Ranking α n => index a b R = 2 ∧ R.rank v < R.rank u)
    let Cvu := eventCard (fun R : Ranking α n => index a b R = 2 ∧ R.rank u < R.rank v)
    have hu : pairCount a u n = A + Cuv := front_pair_count_split hba hS
    have hv : pairCount a v n = A + Cvu := front_pair_count_split hba hS.swap
    have hsum : q 2 = Cuv + Cvu := front_pair_bin_split hS
    have hcount : 3 * Cuv ≤ pairCount v u n := front_minority_middle_le hba hd hS
    have hp' : 18 * pairCount a b n ≤ 5 * N := hp
    have hlu : 3 * pairCount a u n < N := by
      rcases side a u (branch_ne_a hba hS.x_mem).symm with hlo | hhi
      · exact hlo
      · omega
    have hlv : 3 * pairCount a v n < N := by
      rcases side a v (branch_ne_a hba hS.y_mem).symm with hlo | hhi
      · exact hlo
      · omega
    exact ⟨hlu, hlv⟩
  rcases side x y hF.x_ne_y with hlo | hhi
  · exact (hmakes y x hF.swap hlo).symm
  · have ht : pairCount x y n + pairCount y x n = N := pairCount_add hF.x_ne_y
    exact hmakes x y hF (by omega)

/-- The exclusive upset is the ordinal sum of consecutive nonempty antichains
of size at most two. The first block is {b}, and the second block may have either size. -/
structure LayeredBranch (a b : α) (layer : α → ℕ) (top : ℕ) : Prop where
  hasSecond : 1 ≤ top
  levelsBounded : ∀ z, Branch a b z → layer z ≤ top
  levelsNonempty : ∀ j, j ≤ top → (branchStratum a b layer j).Nonempty
  levelsSmall : ∀ j, (branchStratum a b layer j).card ≤ 2
  base : branchStratum a b layer 0 = {b}
  orderByLevel : ∀ x y, Branch a b x → Branch a b y → (x < y ↔ layer x < layer y)

private theorem LayeredBranch.base_mem {a b : α} {layer : α → ℕ} {top : ℕ}
    (H : LayeredBranch a b layer top) : Branch a b b ∧ layer b = 0 := by
  apply mem_branchStratum.mp
  rw [H.base]
  exact Finset.mem_singleton_self b

private theorem LayeredBranch.card_before_pos {a b : α} {layer : α → ℕ} {top j : ℕ}
    (H : LayeredBranch a b layer top) (hj : 0 < j) :
    1 ≤ (belowStratum a b layer j).card := by
  have hb : b ∈ belowStratum a b layer j :=
    mem_belowStratum.mpr ⟨H.base_mem.1, by rw [H.base_mem.2]; exact hj⟩
  exact Finset.one_le_card.mpr ⟨b, hb⟩

private theorem LayeredBranch.two_le_card_before {a b : α} {layer : α → ℕ} {top j : ℕ}
    (H : LayeredBranch a b layer top) (hj : 2 ≤ j) :
    2 ≤ (belowStratum a b layer j).card := by
  classical
  obtain ⟨c, hc⟩ := H.levelsNonempty 1 H.hasSecond
  obtain ⟨hcB, hc1⟩ := mem_branchStratum.mp hc
  have hne : b ≠ c := by
    intro e
    have hb0 := H.base_mem.2
    rw [e, hc1] at hb0
    omega
  have hcard : ({b, c} : Finset α).card = 2 := Finset.card_pair hne
  have hsub : ({b, c} : Finset α) ⊆ belowStratum a b layer j := by
    intro z hz
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hz :
      z = b ∨ z = c) with e | e
    · subst z
      exact mem_belowStratum.mpr ⟨H.base_mem.1, by rw [H.base_mem.2]; omega⟩
    · subst z
      exact mem_belowStratum.mpr ⟨hcB, by rw [hc1]; omega⟩
  simpa only [hcard] using Finset.card_le_card hsub

/-- The actual singleton/two-element layer hypotheses imply each adjacent-layer
doubling step of the earlier rank-interval theorem. -/

private theorem LayeredBranch.toSingleton {a b : α} {layer : α → ℕ} {top : ℕ}
    (H : LayeredBranch a b layer top) (h : (branchStratum a b layer 1).card = 1) :
    SingletonHeadLayers a b layer top :=
  ⟨H.hasSecond, H.levelsBounded, H.levelsNonempty, H.levelsSmall, H.base, h, H.orderByLevel⟩

private theorem LayeredBranch.upper_next_card {a b y : α} {layer : α → ℕ} {top j : ℕ}
    (H : LayeredBranch a b layer top) (hy : Branch a b y) (hyj : layer y = j + 1) :
    (branchUpperSet a b y).card ≤ (belowStratum a b layer j).card +
      (branchStratum a b layer j).card + (branchStratum a b layer (j + 1)).card := by
  classical
  have hsub : branchUpperSet a b y ⊆
      (belowStratum a b layer j ∪ branchStratum a b layer j) ∪
      branchStratum a b layer (j + 1) := by
    intro z hz
    obtain ⟨hzB, hnyz⟩ := mem_branchUpperSet.mp hz
    have hle : layer z ≤ j + 1 := by
      apply le_of_not_gt
      intro h
      exact hnyz ((H.orderByLevel y z hy hzB).mpr (by omega))
    rcases (show layer z < j ∨ layer z = j ∨ layer z = j + 1 by omega) with h | h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (mem_belowStratum.mpr ⟨hzB, h⟩))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inr (mem_branchStratum.mpr ⟨hzB, h⟩))))
    · exact Finset.mem_union.mpr (Or.inr (mem_branchStratum.mpr ⟨hzB, h⟩))
  have h := Finset.card_le_card hsub
  have h₁ := Finset.card_union_le (belowStratum a b layer j) (branchStratum a b layer j)
  have h₂ := Finset.card_union_le (belowStratum a b layer j ∪ branchStratum a b layer j)
    (branchStratum a b layer (j + 1))
  omega

private theorem LayeredBranch.rankStepLate {a b x y : α} {layer : α → ℕ} {top j : ℕ}
    (H : LayeredBranch a b layer top) (hj : 2 ≤ j)
    (hx : Branch a b x) (hy : Branch a b y)
    (hxj : layer x = j) (hyj : layer y = j + 1) :
    BranchRankStep a b x y := by
  classical
  refine ⟨hx, hy, ?_⟩
  have hnot : x ∉ belowStratum a b layer j := by
    intro h
    have hn := (mem_belowStratum.mp h).2
    omega
  have hsub : insert x (belowStratum a b layer j) ⊆ branchLowerSet a b x := by
    intro z hz
    rcases Finset.mem_insert.mp hz with e | h
    · subst z
      exact mem_branchLowerSet.mpr ⟨hx, le_rfl⟩
    · obtain ⟨hzB, hzj⟩ := mem_belowStratum.mp h
      exact mem_branchLowerSet.mpr ⟨hzB,
        le_of_lt ((H.orderByLevel z x hzB hx).mpr (by omega))⟩
  have hl := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at hl
  have hbound := H.upper_next_card hy hyj
  have hC := H.two_le_card_before hj
  have hs₁ := H.levelsSmall j
  have hs₂ := H.levelsSmall (j + 1)
  omega

private theorem LayeredBranch.upper_five_of_level_two {a b y : α} {layer : α → ℕ} {top : ℕ}
    (H : LayeredBranch a b layer top) (hy : Branch a b y) (hy2 : layer y = 2) :
    (branchUpperSet a b y).card ≤ 5 := by
  have he : belowStratum a b layer 1 = branchStratum a b layer 0 := by
    ext z
    simp only [mem_belowStratum, mem_branchStratum]
    constructor
    · rintro ⟨hz, hp⟩
      exact ⟨hz, by omega⟩
    · rintro ⟨hz, hp⟩
      exact ⟨hz, by omega⟩
  have hc : (belowStratum a b layer 1).card = 1 := by rw [he, H.base]; simp
  have h2 : layer y = 1 + 1 := hy2
  have hbound := H.upper_next_card hy h2
  have hs1 := H.levelsSmall 1
  have hs2 := H.levelsSmall (1 + 1)
  omega

private def branchTail (a b : α) (layer : α → ℕ) : Finset α := by
  classical
  exact (branchFinset a b).filter (fun z => 1 < layer z)

@[simp] private theorem mem_branchTail {a b z : α} {layer : α → ℕ} :
    z ∈ branchTail a b layer ↔ Branch a b z ∧ 1 < layer z := by
  classical
  simp [branchTail]

private theorem LayeredBranch.frontShape [DecidableEq α]
    {a b x y : α} {layer : α → ℕ} {top : ℕ}
    (H : LayeredBranch a b layer top) (hne : x ≠ y)
    (he : branchStratum a b layer 1 = ({x, y} : Finset α)) :
    FrontForkShape a b x y (branchTail a b layer) := by
  classical
  have hx : x ∈ branchStratum a b layer 1 := by rw [he]; simp
  have hy : y ∈ branchStratum a b layer 1 := by rw [he]; simp
  obtain ⟨hxB, hx1⟩ := mem_branchStratum.mp hx
  obtain ⟨hyB, hy1⟩ := mem_branchStratum.mp hy
  refine ⟨(H.orderByLevel b x H.base_mem.1 hxB).mpr (by rw [H.base_mem.2, hx1]; omega),
    (H.orderByLevel b y H.base_mem.1 hyB).mpr (by rw [H.base_mem.2, hy1]; omega), hne, ?_, ?_⟩
  · intro z hz
    obtain ⟨hzB, hzL⟩ := mem_branchTail.mp hz
    exact ⟨(H.orderByLevel x z hxB hzB).mpr (by omega), (H.orderByLevel y z hyB hzB).mpr (by omega)⟩
  · intro z
    constructor
    · intro hz
      rcases (show layer z = 0 ∨ layer z = 1 ∨ 1 < layer z by omega) with e | e | e
      · have hm : z ∈ branchStratum a b layer 0 := mem_branchStratum.mpr ⟨hz, e⟩
        rw [H.base] at hm
        exact Or.inl (Finset.mem_singleton.mp hm)
      · have hm : z ∈ branchStratum a b layer 1 := mem_branchStratum.mpr ⟨hz, e⟩
        rw [he] at hm
        rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hm :
          z = x ∨ z = y) with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (mem_branchTail.mpr ⟨hz, e⟩)))
    · rintro (rfl | rfl | rfl | hz)
      · exact H.base_mem.1
      · exact hxB
      · exact hyB
      · exact (mem_branchTail.mp hz).1

private theorem two_cover_impossible_of_low {a b u v : α}
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b) (hb : Branch a b b)
    (hu : Branch a b u) (hv : Branch a b v)
    (hcover : ∀ z, Branch a b z → z ≤ u ∨ z ≤ v)
    (hlowb : 3 * pairCount a b n < Nat.card (Ranking α n))
    (hlou : 3 * pairCount a u n < Nat.card (Ranking α n))
    (hlov : 3 * pairCount a v n < Nat.card (Ranking α n)) : False := by
  classical
  let N := Nat.card (Ranking α n)
  change 3 * pairCount a b n < N at hlowb
  change 3 * pairCount a u n < N at hlou
  change 3 * pairCount a v n < N at hlov
  let m := (branchFinset a b).card
  have hq : Antitone (fun i : ℕ => Nat.card (Bin a b i n)) :=
    antitone_nat_of_succ_le (fun i => natCard_bin_succ_le a b hba hd i)
  have hq0 : Nat.card (Bin a b 0 n) = pairCount a b n :=
    eventCard_congr (fun _ => index_zero_iff hba hb)
  have hlast : Nat.card (Bin a b m n) ≤ pairCount a b n := by
    rw [← hq0]
    exact hq (Nat.zero_le m)
  let E : Ranking α n → Prop := fun R => R.rank a < R.rank u
  let F : Ranking α n → Prop := fun R => R.rank a < R.rank v
  have htot : pairCount a u n + eventCard (fun R => ¬ E R) = N := count_add_complement E
  have hsplit := eventCard_split (fun R => ¬ E R) F
  have hrest1 : eventCard (fun R => ¬ E R ∧ F R) ≤ pairCount a v n :=
    eventCard_mono (fun _ h => h.2)
  have hrest2 : eventCard (fun R => ¬ E R ∧ ¬ F R) ≤ Nat.card (Bin a b m n) := by
    apply eventCard_mono
    intro R h
    have hua := lt_of_not_rank_lt (branch_ne_a hba hu).symm h.1
    have hva := lt_of_not_rank_lt (branch_ne_a hba hv).symm h.2
    have heq : beforeSet R a (Branch a b) = branchFinset a b := by
      ext z
      constructor
      · exact fun hz => mem_branchFinset.mpr (mem_beforeSet.mp hz).1
      · intro hz
        have hzB := mem_branchFinset.mp hz
        apply mem_beforeSet.mpr
        refine ⟨hzB, ?_⟩
        rcases hcover z hzB with hzu | hzv
        · exact lt_of_le_of_lt (R.mono.monotone hzu) hua
        · exact lt_of_le_of_lt (R.mono.monotone hzv) hva
    change (beforeSet R a (Branch a b)).card = m
    rw [heq]
  omega

set_option maxHeartbeats 600000 in
/-- The layered-upset case with genuine two-element second block, for an
arbitrary number of later one- or two-element blocks, at the 5/18 threshold. -/
theorem balanced_of_layeredBranch_second_two {a b : α} {layer : α → ℕ} {top : ℕ}
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b)
    (H : LayeredBranch a b layer top) (hsecond : (branchStratum a b layer 1).card = 2)
    (hp : 18 * pairCount a b n ≤ 5 * Nat.card (Ranking α n)) :
    ∃ x y : α, Balanced x y n := by
  classical
  let N := Nat.card (Ranking α n)
  change 18 * pairCount a b n ≤ 5 * N at hp
  by_contra hn
  have side (z : α) (hz : Branch a b z) :
      3 * pairCount a z n < N ∨ 2 * N < 3 * pairCount a z n := by
    by_contra! h
    exact hn ⟨a, z, (branch_ne_a hba hz).symm, h.1, h.2⟩
  obtain ⟨x, y, hne, he⟩ := Finset.card_eq_two.mp hsecond
  have hF := H.frontShape hne he
  have hlowb : 3 * pairCount a b n < N := by
    rcases side b H.base_mem.1 with hlo | hhi
    · exact hlo
    · omega
  have hm : 3 * pairCount a x n < N ∧ 3 * pairCount a y n < N := front_double_low hba hd hF hp hn
  obtain ⟨hlowx, hlowy⟩ := hm
  have hlevelTwo (z : α) (hz : Branch a b z) (hz2 : layer z = 2) :
      3 * pairCount a z n < N := by
    have hup := H.upper_five_of_level_two hz hz2
    have hQ : pairCount a z n ≤ prefixCount a b 5 n :=
      (pairCount_le_prefixCount_upper hz).trans (prefixCount_le_of_le a b hup)
    have hs := front_prefixFive_le_sum (n := n) hba hd hF
    rcases side z hz with hlo | hhi
    · exact hlo
    · omega
  have lowAt (j : ℕ) : ∀ z, Branch a b z → layer z = j → j ≤ top →
      3 * pairCount a z n < N := by
    induction j with
    | zero =>
      intro z hz hz0 _
      have h := mem_branchStratum.mpr ⟨hz, hz0⟩
      rw [H.base] at h
      have e := Finset.mem_singleton.mp h
      subst z
      exact hlowb
    | succ j ih =>
      intro z hz hzj hj
      by_cases h0 : j = 0
      · have hz1 : layer z = 1 := by omega
        have h := mem_branchStratum.mpr ⟨hz, hz1⟩
        rw [he] at h
        rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using h :
          z = x ∨ z = y) with rfl | rfl
        · exact hlowx
        · exact hlowy
      by_cases h1 : j = 1
      · exact hlevelTwo z hz (by omega)
      obtain ⟨w, hw⟩ := H.levelsNonempty j (by omega)
      obtain ⟨hwB, hwj⟩ := mem_branchStratum.mp hw
      have hwLow := ih w hwB hwj (by omega)
      have hstep := H.rankStepLate (j := j) (by omega) hwB hz hwj hzj
      have hbound := pairCount_le_twice_of_branchRankInterval (n := n) hba hd hstep.1 hstep.2.1 hstep.2.2
      rcases side z hz with hlo | hhi
      · exact hlo
      · omega
  obtain ⟨u, v, hu, hv, hlast⟩ := Finset.exists_two_cover_of_small_nonempty
    (H.levelsNonempty top le_rfl) (H.levelsSmall top)
  obtain ⟨huB, huTop⟩ := mem_branchStratum.mp hu
  obtain ⟨hvB, hvTop⟩ := mem_branchStratum.mp hv
  have hcover (z : α) (hzB : Branch a b z) : z ≤ u ∨ z ≤ v := by
    by_cases heq : layer z = top
    · rcases hlast z (mem_branchStratum.mpr ⟨hzB, heq⟩) with e | e
      · exact Or.inl (le_of_eq e)
      · exact Or.inr (le_of_eq e)
    · have hle := H.levelsBounded z hzB
      exact Or.inl (le_of_lt ((H.orderByLevel z u hzB huB).mpr (by omega)))
  exact two_cover_impossible_of_low hba hd H.base_mem.1 huB hvB hcover hlowb
    (lowAt top u huB huTop le_rfl) (lowAt top v hvB hvTop le_rfl)

/-- Full written layered-upset sufficient condition. Either the second block is
singleton (with initial comparison ≤1/2), or the initial comparison is ≤5/18. -/
theorem balanced_of_layeredBranch {a b : α} {layer : α → ℕ} {top : ℕ}
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b) (H : LayeredBranch a b layer top)
    (hp : 2 * pairCount a b n ≤ Nat.card (Ranking α n))
    (hfront : (branchStratum a b layer 1).card = 1 ∨
      18 * pairCount a b n ≤ 5 * Nat.card (Ranking α n)) :
    ∃ x y : α, Balanced x y n := by
  rcases hfront with hs | hlo
  · exact balanced_of_singletonHeadLayers hba hd (H.toSingleton hs) hp
  have hpos := (H.levelsNonempty 1 H.hasSecond).card_pos
  have hcap := H.levelsSmall 1
  by_cases h1 : (branchStratum a b layer 1).card = 1
  · exact balanced_of_singletonHeadLayers hba hd (H.toSingleton h1) hp
  have h2 : (branchStratum a b layer 1).card = 2 := by omega
  exact balanced_of_layeredBranch_second_two hba hd H h2 hlo

end

end WidthThree

#print axioms WidthThree.balanced_of_layeredBranch_second_two
#print axioms WidthThree.balanced_of_layeredBranch
