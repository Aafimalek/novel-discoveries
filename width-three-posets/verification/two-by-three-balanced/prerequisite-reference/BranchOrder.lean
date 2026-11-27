import BranchSwap

namespace WidthThree

variable {α : Type*} [PartialOrder α] {n : ℕ}

private theorem branch_gap {R : Ranking α n} {a b x z : α}
    (hx : LastBefore R a x (Branch a b)) (hz : Branch a b z)
    (hza : z ≠ a) (hzx : z ≠ x) :
    (R.rank x < R.rank z ↔ R.rank a < R.rank z) ∧
      (R.rank z < R.rank a ↔ R.rank z < R.rank x) := by
  have hza' : R.rank z ≠ R.rank a := fun e => hza (R.inj e)
  have hzx' : R.rank z ≠ R.rank x := fun e => hzx (R.inj e)
  constructor
  · constructor
    · intro h
      apply lt_of_le_of_ne _ hza'.symm
      exact le_of_not_gt (fun h' => (not_lt_of_ge (hx.2.2 z hz h')) h)
    · exact fun h => hx.2.1.trans h
  · exact ⟨fun h => lt_of_le_of_ne (hx.2.2 z hz h) hzx',
      fun h => h.trans hx.2.1⟩

/-- The swap changes the number of branch elements before a, but does not
permute the branch elements in their induced order. -/
theorem branchSwap_preserves_branchOrder {R : Ranking α n} {a b x u v : α}
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b)
    (hx : LastBefore R a x (Branch a b)) (hu : Branch a b u)
    (hv : Branch a b v) :
    (branchSwap R hba hd hx).rank u < (branchSwap R hba hd hx).rank v ↔
      R.rank u < R.rank v := by
  classical
  by_cases hux : u = x
  · subst u
    by_cases hvx : v = x
    · subst v
      simp
    have hva : v ≠ a := by
      intro e
      subst v
      exact hba hv.1
    rw [branchSwap_at_x, branchSwap_elsewhere hba hd hx hva hvx]
    exact (branch_gap hx hv hva hvx).1.symm
  have hua : u ≠ a := by
    intro e
    subst u
    exact hba hu.1
  by_cases hvx : v = x
  · subst v
    rw [branchSwap_elsewhere hba hd hx hua hux, branchSwap_at_x]
    exact (branch_gap hx hu hua hux).2
  have hva : v ≠ a := by
    intro e
    subst v
    exact hba hv.1
  rw [branchSwap_elsewhere hba hd hx hua hux, branchSwap_elsewhere hba hd hx hva hvx]

def BranchOrderInvariant (a b : α) (E : Ranking α n → Prop) : Prop :=
  ∀ R T, (∀ u v, Branch a b u → Branch a b v →
    (R.rank u < R.rank v ↔ T.rank u < T.rank v)) → E R → E T

abbrev BinGiven [Fintype α] (a b : α) (k : ℕ) (E : Ranking α n → Prop) :=
  { R : Ranking α n // (beforeSet R a (Branch a b)).card = k ∧ E R }

/-- Count monotonicity remains true on every fiber defined by the branch order. -/
theorem natCard_binGiven_succ_le [Fintype α] (a b : α)
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b) (k : ℕ)
    (E : Ranking α n → Prop) (hE : BranchOrderInvariant a b E) :
    Nat.card (BinGiven a b (k + 1) E) ≤ Nat.card (BinGiven a b k E) := by
  classical
  have hex (R : BinGiven a b (k + 1) E) :
      ∃ x, LastBefore R.val a x (Branch a b) := by
    apply exists_lastBefore
    apply Finset.card_pos.mp
    simpa only [R.property.1] using (Nat.zero_lt_succ k)
  let x (R : BinGiven a b (k + 1) E) := Classical.choose (hex R)
  have hx (R : BinGiven a b (k + 1) E) : LastBefore R.val a (x R) (Branch a b) :=
    Classical.choose_spec (hex R)
  let f (R : BinGiven a b (k + 1) E) : BinGiven a b k E :=
    ⟨branchSwap R.val hba hd (hx R), by
      constructor
      · change (beforeSet (branchSwap R.val hba hd (hx R)) a (Branch a b)).card = k
        rw [branchSwap_erases hba hd (hx R)]
        have hm : x R ∈ beforeSet R.val a (Branch a b) :=
          mem_beforeSet.mpr ⟨(hx R).1, (hx R).2.1⟩
        have hc := Finset.card_erase_add_one hm
        have hs : (beforeSet R.val a (Branch a b)).card = k + 1 := R.property.1
        omega
      · exact hE R.val _ (fun _ _ hu hv =>
          (branchSwap_preserves_branchOrder hba hd (hx R) hu hv).symm) R.property.2⟩
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

#print axioms WidthThree.natCard_binGiven_succ_le
