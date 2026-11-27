import Mathlib.Tactic
import Mathlib.Data.Fintype.Card

namespace WidthThree

variable {α : Type*} [PartialOrder α] {n : ℕ}

/-- If n is the cardinality of α, these are the linear extensions of α. -/
structure Ranking (α : Type*) [PartialOrder α] (n : ℕ) where
  rank : α → Fin n
  inj : Function.Injective rank
  mono : StrictMono rank

theorem Ranking.eq_of_rank_eq {R T : Ranking α n}
    (h : ∀ x, R.rank x = T.rank x) : R = T := by
  cases R with
  | mk r ri rm =>
    cases T with
    | mk t ti tm =>
      have he : r = t := funext h
      subst t
      rfl

instance [Finite α] : Finite (Ranking α n) :=
  Finite.of_injective (Ranking.rank : Ranking α n → α → Fin n)
    (fun _ _ h => Ranking.eq_of_rank_eq fun x => congrFun h x)

/-- The exclusive upset, with b included when a and b are incomparable. -/
def Branch (a b x : α) : Prop := b ≤ x ∧ ¬ a < x

def LastBefore (R : Ranking α n) (a x : α) (S : α → Prop) : Prop :=
  S x ∧ R.rank x < R.rank a ∧
    ∀ z, S z → R.rank z < R.rank a → R.rank z ≤ R.rank x

def FirstAfter (R : Ranking α n) (a x : α) (S : α → Prop) : Prop :=
  S x ∧ R.rank a < R.rank x ∧
    ∀ z, S z → R.rank a < R.rank z → R.rank x ≤ R.rank z

theorem FirstAfter.unique {R : Ranking α n} {a x y : α} {S : α → Prop}
    (hx : FirstAfter R a x S) (hy : FirstAfter R a y S) : x = y := by
  exact R.inj (le_antisymm (hx.2.2 y hy.1 hy.2.1) (hy.2.2 x hx.1 hx.2.1))

private theorem swap_strictMono [DecidableEq α] (R : Ranking α n) (a x : α)
    (hxa : R.rank x < R.rank a) (hnxa : ¬ x < a)
    (hgap : ∀ z, R.rank x < R.rank z → R.rank z < R.rank a →
      (¬ z < a) ∧ (¬ x < z)) :
    StrictMono (fun z => R.rank (Equiv.swap a x z)) := by
  intro u v huv
  change R.rank (Equiv.swap a x u) < R.rank (Equiv.swap a x v)
  by_cases hua : u = a
  · subst u
    have hva : v ≠ a := ne_of_gt huv
    have hvx : v ≠ x := by
      intro e
      subst v
      exact (not_lt_of_ge (le_of_lt hxa)) (R.mono huv)
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hva hvx]
    exact hxa.trans (R.mono huv)
  by_cases hux : u = x
  · subst u
    have hva : v ≠ a := by
      intro e
      subst v
      exact hnxa huv
    have hvx : v ≠ x := ne_of_gt huv
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hva hvx]
    have hne : R.rank v ≠ R.rank a := fun h => hva (R.inj h)
    rcases lt_trichotomy (R.rank a) (R.rank v) with h | h | h
    · exact h
    · exact False.elim (hne h.symm)
    · exact False.elim ((hgap v (R.mono huv) h).2 huv)
  by_cases hva : v = a
  · subst v
    rw [Equiv.swap_apply_of_ne_of_ne hua hux, Equiv.swap_apply_left]
    have hne : R.rank u ≠ R.rank x := fun h => hux (R.inj h)
    rcases lt_trichotomy (R.rank u) (R.rank x) with h | h | h
    · exact h
    · exact False.elim (hne h)
    · exact False.elim ((hgap u h (R.mono huv)).1 huv)
  by_cases hvx : v = x
  · subst v
    rw [Equiv.swap_apply_of_ne_of_ne hua hux, Equiv.swap_apply_right]
    exact (R.mono huv).trans hxa
  rw [Equiv.swap_apply_of_ne_of_ne hua hux, Equiv.swap_apply_of_ne_of_ne hva hvx]
  exact R.mono huv

noncomputable def branchSwap (R : Ranking α n) {a b x : α}
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b)
    (hx : LastBefore R a x (Branch a b)) : Ranking α n := by
  letI : DecidableEq α := Classical.decEq α
  refine ⟨fun z => R.rank (Equiv.swap a x z), ?_, ?_⟩
  · intro u v h
    exact (Equiv.swap a x).injective (R.inj h)
  · apply swap_strictMono R a x hx.2.1
    · intro hxa
      exact hba (le_of_lt (lt_of_le_of_lt hx.1.1 hxa))
    · intro z hxz hza
      constructor
      · intro h
        have hzx : R.rank z < R.rank x :=
          (R.mono (hd z h)).trans_le (R.mono.monotone hx.1.1)
        exact (not_lt_of_ge (le_of_lt hxz)) hzx
      · intro h
        have hS : Branch a b z :=
          ⟨le_trans hx.1.1 (le_of_lt h), fun haz =>
            (not_lt_of_ge (le_of_lt hza)) (R.mono haz)⟩
        exact (not_lt_of_ge (hx.2.2 z hS hza)) hxz

theorem branchSwap_rank {R : Ranking α n} {a b x z : α}
    {hba : ¬ b ≤ a} {hd : ∀ z, z < a → z < b}
    {hx : LastBefore R a x (Branch a b)} :
    (branchSwap R hba hd hx).rank z =
      R.rank (@Equiv.swap α (Classical.decEq α) a x z) := by
  rfl

@[simp] theorem branchSwap_at_a {R : Ranking α n} {a b x : α}
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b)
    (hx : LastBefore R a x (Branch a b)) :
    (branchSwap R hba hd hx).rank a = R.rank x := by
  letI := Classical.decEq α
  rw [branchSwap_rank, Equiv.swap_apply_left]

@[simp] theorem branchSwap_at_x {R : Ranking α n} {a b x : α}
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b)
    (hx : LastBefore R a x (Branch a b)) :
    (branchSwap R hba hd hx).rank x = R.rank a := by
  letI := Classical.decEq α
  rw [branchSwap_rank, Equiv.swap_apply_right]

theorem branchSwap_elsewhere {R : Ranking α n} {a b x z : α}
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b)
    (hx : LastBefore R a x (Branch a b))
    (hza : z ≠ a) (hzx : z ≠ x) :
    (branchSwap R hba hd hx).rank z = R.rank z := by
  letI := Classical.decEq α
  rw [branchSwap_rank, Equiv.swap_apply_of_ne_of_ne hza hzx]

theorem branchSwap_firstAfter {R : Ranking α n} {a b x : α}
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b)
    (hx : LastBefore R a x (Branch a b)) :
    FirstAfter (branchSwap R hba hd hx) a x (Branch a b) := by
  refine ⟨hx.1, ?_, ?_⟩
  · rw [branchSwap_at_a, branchSwap_at_x]
    exact hx.2.1
  · intro z hz hzafter
    by_cases hzx : z = x
    · subst z
      exact le_rfl
    have hza : z ≠ a := by
      intro e
      subst z
      exact hba hz.1
    rw [branchSwap_at_a, branchSwap_elsewhere hba hd hx hza hzx] at hzafter
    rw [branchSwap_at_x, branchSwap_elsewhere hba hd hx hza hzx]
    by_contra! h
    exact (not_lt_of_ge (hx.2.2 z hz h)) hzafter

noncomputable def beforeSet [Fintype α] (R : Ranking α n)
    (a : α) (S : α → Prop) : Finset α := by
  classical
  exact Finset.univ.filter (fun z => S z ∧ R.rank z < R.rank a)

@[simp] theorem mem_beforeSet [Fintype α] {R : Ranking α n} {a z : α}
    {S : α → Prop} : z ∈ beforeSet R a S ↔ S z ∧ R.rank z < R.rank a := by
  classical
  simp [beforeSet]

theorem branchSwap_erases [Fintype α] [DecidableEq α] {R : Ranking α n} {a b x : α}
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b)
    (hx : LastBefore R a x (Branch a b)) :
    beforeSet (branchSwap R hba hd hx) a (Branch a b) =
      (beforeSet R a (Branch a b)).erase x := by
  ext z
  by_cases hzx : z = x
  · subst z
    constructor
    · intro h
      have hr := (mem_beforeSet.mp h).2
      rw [branchSwap_at_x, branchSwap_at_a] at hr
      exact ((not_lt_of_ge (le_of_lt hx.2.1)) hr).elim
    · intro h
      exact ((Finset.mem_erase.mp h).1 rfl).elim
  by_cases hza : z = a
  · subst z
    constructor
    · intro h
      exact (hba (mem_beforeSet.mp h).1.1).elim
    · intro h
      exact (hba (mem_beforeSet.mp (Finset.mem_erase.mp h).2).1.1).elim
  constructor
  · intro h
    obtain ⟨hz, hr⟩ := mem_beforeSet.mp h
    rw [branchSwap_elsewhere hba hd hx hza hzx, branchSwap_at_a] at hr
    exact Finset.mem_erase.mpr ⟨hzx, mem_beforeSet.mpr ⟨hz, hr.trans hx.2.1⟩⟩
  · intro h
    obtain ⟨hz, hr⟩ := mem_beforeSet.mp (Finset.mem_erase.mp h).2
    apply mem_beforeSet.mpr
    refine ⟨hz, ?_⟩
    rw [branchSwap_elsewhere hba hd hx hza hzx, branchSwap_at_a]
    exact lt_of_le_of_ne (hx.2.2 z hz hr) (fun e => hzx (R.inj e))

theorem exists_lastBefore [Fintype α] {R : Ranking α n} {a : α} {S : α → Prop}
    (h : (beforeSet R a S).Nonempty) : ∃ x, LastBefore R a x S := by
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image (beforeSet R a S) R.rank h
  have hx' := mem_beforeSet.mp hx
  exact ⟨x, hx'.1, hx'.2, fun z hz hza => hmax z (mem_beforeSet.mpr ⟨hz, hza⟩)⟩

abbrev Bin [Fintype α] (a b : α) (k n : ℕ) :=
  { R : Ranking α n // (beforeSet R a (Branch a b)).card = k }

theorem natCard_bin_succ_le [Fintype α] (a b : α)
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b) (k : ℕ) :
    Nat.card (Bin a b (k + 1) n) ≤ Nat.card (Bin a b k n) := by
  classical
  have hex (R : Bin a b (k + 1) n) :
      ∃ x, LastBefore R.val a x (Branch a b) := by
    apply exists_lastBefore
    apply Finset.card_pos.mp
    simpa only [R.property] using (Nat.zero_lt_succ k)
  let x (R : Bin a b (k + 1) n) := Classical.choose (hex R)
  have hx (R : Bin a b (k + 1) n) : LastBefore R.val a (x R) (Branch a b) :=
    Classical.choose_spec (hex R)
  let f (R : Bin a b (k + 1) n) : Bin a b k n :=
    ⟨branchSwap R.val hba hd (hx R), by
      change (beforeSet (branchSwap R.val hba hd (hx R)) a (Branch a b)).card = k
      rw [branchSwap_erases hba hd (hx R)]
      have hm : x R ∈ beforeSet R.val a (Branch a b) :=
        mem_beforeSet.mpr ⟨(hx R).1, (hx R).2.1⟩
      have hc := Finset.card_erase_add_one hm
      have hs : (beforeSet R.val a (Branch a b)).card = k + 1 := R.property
      omega⟩
  apply Nat.card_le_card_of_injective f
  intro R T h
  have hr : (f R).val = (f T).val := congrArg Subtype.val h
  have hfirstR : FirstAfter (f R).val a (x R) (Branch a b) :=
    branchSwap_firstAfter hba hd (hx R)
  have hfirstT : FirstAfter (f T).val a (x T) (Branch a b) :=
    branchSwap_firstAfter hba hd (hx T)
  rw [← hr] at hfirstT
  have hxt : x R = x T := FirstAfter.unique hfirstR hfirstT
  apply Subtype.ext
  apply Ranking.eq_of_rank_eq
  intro z
  letI := Classical.decEq α
  have he := congrArg (fun V : Ranking α n => V.rank (Equiv.swap a (x R) z)) hr
  change R.val.rank (Equiv.swap a (x R) (Equiv.swap a (x R) z)) =
    T.val.rank (Equiv.swap a (x T) (Equiv.swap a (x R) z)) at he
  rw [← hxt] at he
  simpa only [Equiv.swap_apply_self] using he

end WidthThree

#print axioms WidthThree.natCard_bin_succ_le
