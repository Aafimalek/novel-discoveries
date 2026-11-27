import BranchOrder

namespace WidthThree

noncomputable section

universe u

private abbrev eventCard {γ : Type u} (E : γ → Prop) := Nat.card {r : γ // E r}

private theorem eventCard_congr {γ : Type u} {E F : γ → Prop}
    (h : ∀ r, E r ↔ F r) : eventCard E = eventCard F :=
  Nat.card_congr (Equiv.subtypeEquivProp (funext fun r => propext (h r)))

private theorem eventCard_mono {γ : Type u} [Finite γ] {E F : γ → Prop}
    (h : ∀ r, E r → F r) : eventCard E ≤ eventCard F :=
  Nat.card_le_card_of_injective
    (fun r : {r : γ // E r} => (⟨r.val, h r.val r.property⟩ : {r : γ // F r}))
    (fun _ _ hr => Subtype.ext (congrArg (fun t : {r : γ // F r} => t.val) hr))

private theorem eventCard_split {γ : Type u} [Finite γ] (E F : γ → Prop) :
    eventCard E = eventCard (fun r => E r ∧ F r) + eventCard (fun r => E r ∧ ¬ F r) := by
  classical
  let p : {r : γ // E r} → Prop := fun r => F r.val
  let e₁ : {r : {r : γ // E r} // p r} ≃ {r : γ // E r ∧ F r} :=
    { toFun := fun r => ⟨r.val.val, r.val.property, r.property⟩
      invFun := fun r => ⟨⟨r.val, r.property.1⟩, r.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₂ : {r : {r : γ // E r} // ¬ p r} ≃ {r : γ // E r ∧ ¬ F r} :=
    { toFun := fun r => ⟨r.val.val, r.val.property, r.property⟩
      invFun := fun r => ⟨⟨r.val, r.property.1⟩, r.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := Nat.card_congr (Equiv.sumCompl p)
  rw [Nat.card_sum, Nat.card_congr e₁, Nat.card_congr e₂] at h
  exact h.symm

private def forgetFiber {γ : Type u} (f : γ → ℕ) (E : γ → Prop) (m : ℕ) :
    (Σ i : Fin m, {r : γ // f r = i.val ∧ E r}) → {r : γ // E r} :=
  fun i => ⟨i.2.val, i.2.property.2⟩

private theorem forgetFiber_injective {γ : Type u} (f : γ → ℕ) (E : γ → Prop) (m : ℕ) :
    Function.Injective (forgetFiber f E m) := by
  rintro ⟨i, r⟩ ⟨j, s⟩ h
  have hrs : r.val = s.val := congrArg Subtype.val h
  have hvj : f r.val = j.val := by
    rw [hrs]
    exact s.property.1
  have hij : i = j := Fin.ext (r.property.1.symm.trans hvj)
  subst j
  have hsub : r = s := Subtype.ext hrs
  subst s
  rfl

private theorem sum_fibers_le {γ : Type u} [Finite γ] (f : γ → ℕ) (E : γ → Prop) (m : ℕ) :
    (∑ i : Fin m, eventCard (fun r => f r = i.val ∧ E r)) ≤ eventCard E := by
  rw [← Nat.card_sigma]
  exact Nat.card_le_card_of_injective (forgetFiber f E m) (forgetFiber_injective f E m)

private theorem sum_fibers_eq {γ : Type u} [Finite γ] (f : γ → ℕ) (E : γ → Prop) (m : ℕ)
    (h : ∀ r, E r → f r < m) :
    (∑ i : Fin m, eventCard (fun r => f r = i.val ∧ E r)) = eventCard E := by
  rw [← Nat.card_sigma]
  apply Nat.card_eq_of_bijective
  constructor
  · exact forgetFiber_injective f E m
  · intro r
    exact ⟨⟨⟨f r.val, h r.val r.property⟩, ⟨r.val, rfl, r.property⟩⟩, rfl⟩

variable {α : Type u} [PartialOrder α] {n : ℕ}

/-- Number of ranked linear extensions placing x before y. -/
def pairCount (x y : α) (n : ℕ) : ℕ :=
  Nat.card {R : Ranking α n // R.rank x < R.rank y}

def Balanced (x y : α) (n : ℕ) : Prop :=
  x ≠ y ∧ Nat.card (Ranking α n) ≤ 3 * pairCount x y n ∧
    3 * pairCount x y n ≤ 2 * Nat.card (Ranking α n)

private theorem pairCount_add [Fintype α] {x y : α} (hxy : x ≠ y) :
    pairCount x y n + pairCount y x n = Nat.card (Ranking α n) := by
  classical
  let p : Ranking α n → Prop := fun R => R.rank x < R.rank y
  have h := Nat.card_congr (Equiv.sumCompl p)
  rw [Nat.card_sum] at h
  have hc : eventCard (fun R : Ranking α n => ¬ p R) =
      eventCard (fun R : Ranking α n => R.rank y < R.rank x) := by
    apply eventCard_congr
    intro R
    exact ⟨fun hp => lt_of_le_of_ne (le_of_not_gt hp) (fun e => hxy (R.inj e.symm)),
      fun hp => not_lt_of_ge (le_of_lt hp)⟩
  change pairCount x y n + eventCard (fun R : Ranking α n => ¬ p R) = _ at h
  rw [hc] at h
  exact h

/-- A fork, or a diamond, as the entire exclusive upset of b. -/
structure ForkShape (a b x y : α) (tail : Finset α) : Prop where
  b_lt_x : b < x
  b_lt_y : b < y
  x_ne_y : x ≠ y
  tailSize : tail.card ≤ 1
  tailAbove : ∀ z ∈ tail, x < z ∧ y < z
  describe : ∀ z, Branch a b z ↔ z = b ∨ z = x ∨ z = y ∨ z ∈ tail

variable [Fintype α]

private abbrev index (a b : α) (R : Ranking α n) :=
  (beforeSet R a (Branch a b)).card

private theorem ForkShape.swap {a b x y : α} {tail : Finset α}
    (hF : ForkShape a b x y tail) : ForkShape a b y x tail :=
  ⟨hF.b_lt_y, hF.b_lt_x, hF.x_ne_y.symm, hF.tailSize,
    fun z hz => ⟨(hF.tailAbove z hz).2, (hF.tailAbove z hz).1⟩, fun z => by
      rw [hF.describe]
      tauto⟩

private theorem ForkShape.b_mem {a b x y : α} {tail : Finset α}
    (hF : ForkShape a b x y tail) : Branch a b b :=
  (hF.describe b).mpr (Or.inl rfl)

private theorem ForkShape.x_mem {a b x y : α} {tail : Finset α}
    (hF : ForkShape a b x y tail) : Branch a b x :=
  (hF.describe x).mpr (Or.inr (Or.inl rfl))

private theorem ForkShape.y_mem {a b x y : α} {tail : Finset α}
    (hF : ForkShape a b x y tail) : Branch a b y := hF.swap.x_mem

private theorem branch_ne_a {a b z : α} (hba : ¬ b ≤ a) (hz : Branch a b z) : z ≠ a := by
  intro e
  subst z
  exact hba hz.1

private theorem lt_of_not_rank_lt {R : Ranking α n} {x y : α}
    (hne : x ≠ y) (h : ¬ R.rank x < R.rank y) : R.rank y < R.rank x :=
  lt_of_le_of_ne (le_of_not_gt h) (fun e => hne (R.inj e.symm))

private theorem index_zero_iff {R : Ranking α n} {a b : α}
    (hba : ¬ b ≤ a) (hb : Branch a b b) : index a b R = 0 ↔ R.rank a < R.rank b := by
  constructor
  · intro h
    by_contra! hn
    have hlt : R.rank b < R.rank a :=
      lt_of_le_of_ne hn (fun eq => hba (le_of_eq (R.inj eq)))
    have hm := mem_beforeSet.mpr ⟨hb, hlt⟩
    exact (Finset.card_ne_zero_of_mem hm) h
  · intro hab
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨hzS, hzlt⟩ := mem_beforeSet.mp hz
    exact (not_lt_of_ge (R.mono.monotone hzS.1)) (hzlt.trans hab)

private theorem index_le_four {a b x y : α} {tail : Finset α}
    (hF : ForkShape a b x y tail) (R : Ranking α n) : index a b R ≤ 4 := by
  classical
  have hsub : beforeSet R a (Branch a b) ⊆ insert b (insert x (insert y tail)) := by
    intro z hz
    simpa only [Finset.mem_insert] using (hF.describe z).mp (mem_beforeSet.mp hz).1
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le b (insert x (insert y tail))
  have h3 := Finset.card_insert_le x (insert y tail)
  have h4 := Finset.card_insert_le y tail
  have ht := hF.tailSize
  change (beforeSet R a (Branch a b)).card ≤ 4
  omega

private theorem index_le_one_of_beforeBoth {a b x y : α} {tail : Finset α}
    (hF : ForkShape a b x y tail) {R : Ranking α n}
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

private theorem two_le_index_of_xBefore {a b x y : α} {tail : Finset α}
    (hF : ForkShape a b x y tail) {R : Ranking α n}
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

private theorem beforeBoth_iff {a b x y : α} {tail : Finset α}
    (hba : ¬ b ≤ a) (hF : ForkShape a b x y tail) {R : Ranking α n} :
    (R.rank a < R.rank x ∧ R.rank a < R.rank y) ↔ index a b R < 2 := by
  constructor
  · intro h
    have hh := index_le_one_of_beforeBoth hF h.1 h.2
    omega
  · intro h
    constructor
    · by_contra hn
      have hh := two_le_index_of_xBefore hF
        (lt_of_not_rank_lt (branch_ne_a hba hF.x_mem).symm hn)
      omega
    · by_contra hn
      have hh := two_le_index_of_xBefore hF.swap
        (lt_of_not_rank_lt (branch_ne_a hba hF.y_mem).symm hn)
      omega

private theorem middle_forward {a b x y : α} {tail : Finset α}
    (hF : ForkShape a b x y tail) {R : Ranking α n}
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

private theorem early_count_bounds {a b x y : α} {tail : Finset α}
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b) (hF : ForkShape a b x y tail) :
    let A := eventCard (fun R : Ranking α n => index a b R < 2)
    2 * Nat.card (Ranking α n) ≤ 5 * A ∧ A ≤ 2 * pairCount a b n := by
  dsimp only
  let q (k : ℕ) := Nat.card (Bin a b k n)
  have hone (k : ℕ) : q (k + 1) ≤ q k := natCard_bin_succ_le a b hba hd k
  have htotal := sum_fibers_eq (fun R : Ranking α n => index a b R) (fun _ => True) 5
    (fun R _ => Nat.lt_succ_of_le (index_le_four hF R))
  have he (k : Fin 5) : eventCard (fun R : Ranking α n => index a b R = k.val ∧ True) =
      q k.val := eventCard_congr (fun _ => ⟨And.left, fun h => ⟨h, trivial⟩⟩)
  simp only [he, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at htotal
  change q 0 + (q 1 + (q 2 + (q 3 + q 4))) =
    eventCard (fun _ : Ranking α n => True) at htotal
  have htrue : eventCard (fun _ : Ranking α n => True) = Nat.card (Ranking α n) :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
  rw [htrue] at htotal
  have hearly := sum_fibers_eq (fun R : Ranking α n => index a b R)
    (fun R => index a b R < 2) 2 (fun _ h => h)
  have he2 (k : Fin 2) : eventCard (fun R : Ranking α n =>
      index a b R = k.val ∧ index a b R < 2) = q k.val := by
    apply eventCard_congr
    intro R
    refine ⟨And.left, fun e => ⟨e, ?_⟩⟩
    change index a b R = k.val at e
    exact e.symm ▸ k.isLt
  simp only [he2, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hearly
  change q 0 + q 1 = eventCard (fun R : Ranking α n => index a b R < 2) at hearly
  have hq0 : q 0 = pairCount a b n := eventCard_congr (fun _ => index_zero_iff hba hF.b_mem)
  have h01 : q 1 ≤ q 0 := hone 0
  have h12 : q 2 ≤ q 1 := hone 1
  have h23 : q 3 ≤ q 2 := hone 2
  have h34 : q 4 ≤ q 3 := hone 3
  omega

private theorem minority_middle_count_le {a b x y : α} {tail : Finset α}
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b) (hF : ForkShape a b x y tail) :
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

set_option maxHeartbeats 500000 in
/-- If the exclusive upset is a fork or a diamond and the first bin occupies
at most (5/18) of the extensions, some pair is balanced. The parameter n
may be specialized to the cardinality of the poset. -/
theorem forkDiamond_balanced {a b x y : α} {tail : Finset α}
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b) (hF : ForkShape a b x y tail)
    (hp : 18 * pairCount a b n ≤ 5 * Nat.card (Ranking α n)) :
    ∃ u v : α, Balanced u v n := by
  classical
  let A := eventCard (fun R : Ranking α n => index a b R < 2)
  let total := Nat.card (Ranking α n)
  have hA : 2 * total ≤ 5 * A ∧ A ≤ 2 * pairCount a b n :=
    early_count_bounds hba hd hF
  by_contra hn
  have hside (u v : α) (huv : u ≠ v) :
      3 * pairCount u v n < total ∨ 2 * total < 3 * pairCount u v n := by
    by_contra! h
    exact hn ⟨u, v, huv, h.1, h.2⟩
  have hHigh (u v : α) (hS : ForkShape a b u v tail) :
      2 * total < 3 * pairCount a u n := by
    have hle : A ≤ pairCount a u n := eventCard_mono (fun R hr =>
      ((beforeBoth_iff hba hS).mpr hr).1)
    rcases hside a u (branch_ne_a hba hS.x_mem).symm with hlow | hhigh
    · have hmass := hA.1
      omega
    · exact hhigh
  have hForbid (u v : α) (hS : ForkShape a b u v tail) (hminor : 3 * pairCount v u n < total) :
      ¬ 2 * total < 3 * pairCount a u n := by
    let m := eventCard (fun R : Ranking α n => index a b R = 2 ∧ R.rank v < R.rank u)
    have hm : 3 * m ≤ pairCount v u n := minority_middle_count_le hba hd hS
    have hsplit := eventCard_split
      (fun R : Ranking α n => R.rank a < R.rank u)
      (fun R : Ranking α n => R.rank a < R.rank v)
    have hboth : eventCard (fun R : Ranking α n => R.rank a < R.rank u ∧ R.rank a < R.rank v) = A :=
      eventCard_congr (fun _ => beforeBoth_iff hba hS)
    have hmid : eventCard (fun R : Ranking α n => R.rank a < R.rank u ∧ ¬R.rank a < R.rank v) ≤ m := by
      apply eventCard_mono
      intro R h
      have hlt := lt_of_not_rank_lt (branch_ne_a hba hS.y_mem).symm h.2
      exact ⟨middle_forward hS.swap hlt h.1, hlt.trans h.1⟩
    change pairCount a u n = _ at hsplit
    rw [hboth] at hsplit
    have halt := hA.2
    change 18 * pairCount a b n ≤ 5 * total at hp
    omega
  have hpartition : pairCount x y n + pairCount y x n = total :=
    pairCount_add hF.x_ne_y
  rcases hside x y hF.x_ne_y with hlo | hhi
  · exact hForbid y x hF.swap hlo (hHigh y x hF.swap)
  · have hlow : 3 * pairCount y x n < total := by omega
    exact hForbid x y hF hlow (hHigh x y hF)


/-- The exclusive upset, counted as a finite family. -/
def branchFinset (a b : α) : Finset α := by
  classical
  exact Finset.univ.filter (Branch a b)

@[simp] theorem mem_branchFinset {a b z : α} :
    z ∈ branchFinset a b ↔ Branch a b z := by
  classical
  simp [branchFinset]

/-- Vertices of the exclusive upset at or below x. -/
def branchLowerSet (a b x : α) : Finset α := by
  classical
  exact (branchFinset a b).filter (· ≤ x)

@[simp] theorem mem_branchLowerSet {a b x z : α} :
    z ∈ branchLowerSet a b x ↔ Branch a b z ∧ z ≤ x := by
  classical
  simp [branchLowerSet]

/-- Vertices of the exclusive upset that are not strict successors of x. -/
def branchUpperSet (a b x : α) : Finset α := by
  classical
  exact (branchFinset a b).filter (fun z => ¬ x < z)

@[simp] theorem mem_branchUpperSet {a b x z : α} :
    z ∈ branchUpperSet a b x ↔ Branch a b z ∧ ¬ x < z := by
  classical
  simp [branchUpperSet]

private abbrev prefixCount (a b : α) (k n : ℕ) :=
  eventCard (fun R : Ranking α n => index a b R < k)

private theorem prefixCount_succ (a b : α) (k : ℕ) :
    prefixCount a b (k + 1) n = prefixCount a b k n + Nat.card (Bin a b k n) := by
  have h := eventCard_split (fun R : Ranking α n => index a b R < k + 1)
    (fun R : Ranking α n => index a b R < k)
  have hl : eventCard (fun R : Ranking α n => index a b R < k + 1 ∧ index a b R < k) =
      prefixCount a b k n := by
    apply eventCard_congr
    intro R
    omega
  have hr : eventCard (fun R : Ranking α n => index a b R < k + 1 ∧ ¬ index a b R < k) =
      Nat.card (Bin a b k n) := by
    apply eventCard_congr
    intro R
    change (index a b R < k + 1 ∧ ¬ index a b R < k) ↔ index a b R = k
    omega
  rw [hl, hr] at h
  exact h

private theorem prefixCount_le_of_le (a b : α) {j k : ℕ} (hjk : j ≤ k) :
    prefixCount a b j n ≤ prefixCount a b k n :=
  eventCard_mono (fun _ h => lt_of_lt_of_le h hjk)

private theorem prefixCount_subadditive (a b : α) (hba : ¬ b ≤ a)
    (hd : ∀ z, z < a → z < b) (L K : ℕ) :
    prefixCount a b (L + K) n ≤ prefixCount a b L n + prefixCount a b K n := by
  have hq : Antitone (fun i : ℕ => Nat.card (Bin a b i n)) :=
    antitone_nat_of_succ_le (fun i => natCard_bin_succ_le a b hba hd i)
  induction K with
  | zero => simp only [Nat.add_zero]; exact Nat.le_add_right _ _
  | succ K ih =>
    have hk : Nat.card (Bin a b (L + K) n) ≤ Nat.card (Bin a b K n) :=
      hq (Nat.le_add_left K L)
    rw [Nat.add_succ, prefixCount_succ, prefixCount_succ]
    omega

private theorem prefixCount_lower_le {a b x : α} (hba : ¬ b ≤ a)
    (hx : Branch a b x) :
    prefixCount a b (branchLowerSet a b x).card n ≤ pairCount a x n := by
  apply eventCard_mono
  intro R h
  by_contra hn
  have hxa := lt_of_not_rank_lt (branch_ne_a hba hx).symm hn
  have hs : branchLowerSet a b x ⊆ beforeSet R a (Branch a b) := by
    intro z hz
    obtain ⟨hzB, hzx⟩ := mem_branchLowerSet.mp hz
    exact mem_beforeSet.mpr ⟨hzB, lt_of_le_of_lt (R.mono.monotone hzx) hxa⟩
  exact (not_lt_of_ge (Finset.card_le_card hs)) h

private theorem pairCount_le_prefixCount_upper {a b y : α} (hy : Branch a b y) :
    pairCount a y n ≤ prefixCount a b (branchUpperSet a b y).card n := by
  classical
  apply eventCard_mono
  intro R hay
  have hs : beforeSet R a (Branch a b) ⊆ (branchUpperSet a b y).erase y := by
    intro z hz
    obtain ⟨hzB, hza⟩ := mem_beforeSet.mp hz
    have hzy := hza.trans hay
    refine Finset.mem_erase.mpr ⟨fun eq => (lt_irrefl _ (eq ▸ hzy)), ?_⟩
    exact mem_branchUpperSet.mpr ⟨hzB, fun hyz => lt_asymm hzy (R.mono hyz)⟩
  have hyU : y ∈ branchUpperSet a b y := mem_branchUpperSet.mpr ⟨hy, lt_irrefl y⟩
  have hcard := Finset.card_erase_add_one hyU
  have hbound := Finset.card_le_card hs
  change (beforeSet R a (Branch a b)).card < (branchUpperSet a b y).card
  omega

/-- A directed step on the exclusive upset cannot more than double the number
of linear extensions in which a precedes the selected vertex. -/
theorem pairCount_le_twice_of_branchRankInterval {a b x y : α}
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b)
    (hx : Branch a b x) (hy : Branch a b y)
    (hr : (branchUpperSet a b y).card ≤ 2 * (branchLowerSet a b x).card) :
    pairCount a y n ≤ 2 * pairCount a x n := by
  let L := (branchLowerSet a b x).card
  let U := (branchUpperSet a b y).card
  have h0 : pairCount a y n ≤ prefixCount a b U n := pairCount_le_prefixCount_upper hy
  have h1 : prefixCount a b U n ≤ prefixCount a b (L + L) n :=
    prefixCount_le_of_le a b (by simpa only [two_mul] using hr)
  have h2 : prefixCount a b (L + L) n ≤
      prefixCount a b L n + prefixCount a b L n := prefixCount_subadditive a b hba hd L L
  have h3 : prefixCount a b L n ≤ pairCount a x n := prefixCount_lower_le hba hx
  omega

def BranchRankStep (a b x y : α) : Prop :=
  Branch a b x ∧ Branch a b y ∧
    (branchUpperSet a b y).card ≤ 2 * (branchLowerSet a b x).card

private theorem count_add_complement {γ : Type u} [Finite γ] (E : γ → Prop) :
    eventCard E + eventCard (fun r => ¬ E r) = Nat.card γ := by
  classical
  have h := Nat.card_congr (Equiv.sumCompl E)
  rw [Nat.card_sum] at h
  exact h

/-- A width-three obstruction criterion: if two vertices cover all of the exclusive
upset from above, and both are reachable from b by rank-interval steps, then a
balanced pair exists provided the initial comparison has probability at most 1/2.
The two covering vertices may coincide. -/
theorem balanced_of_branchRankReach {a b u v : α}
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b) (hb : Branch a b b)
    (hu : Branch a b u) (hv : Branch a b v)
    (hcover : ∀ z, Branch a b z → z ≤ u ∨ z ≤ v)
    (hru : Relation.ReflTransGen (BranchRankStep a b) b u)
    (hrv : Relation.ReflTransGen (BranchRankStep a b) b v)
    (hp : 2 * pairCount a b n ≤ Nat.card (Ranking α n)) :
    ∃ x y : α, Balanced x y n := by
  classical
  let N := Nat.card (Ranking α n)
  by_contra hn
  have side (z : α) (hz : Branch a b z) :
      3 * pairCount a z n < N ∨ 2 * N < 3 * pairCount a z n := by
    by_contra! h
    exact hn ⟨a, z, (branch_ne_a hba hz).symm, h.1, h.2⟩
  have hlowb : 3 * pairCount a b n < N := by
    rcases side b hb with hlo | hhi
    · exact hlo
    · change 2 * pairCount a b n ≤ N at hp
      omega
  have reachLow (z : α) (hr : Relation.ReflTransGen (BranchRankStep a b) b z) :
      3 * pairCount a z n < N := by
    induction hr with
    | refl => exact hlowb
    | tail _ hstep ih =>
      obtain ⟨hsrc, hdst, hgap⟩ := hstep
      have hbound := pairCount_le_twice_of_branchRankInterval (n := n) hba hd hsrc hdst hgap
      rcases side _ hdst with hlo | hhi
      · exact hlo
      · omega
  have hlou := reachLow u hru
  have hlov := reachLow v hrv
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

end

end WidthThree

#print axioms WidthThree.pairCount_le_twice_of_branchRankInterval
#print axioms WidthThree.balanced_of_branchRankReach
