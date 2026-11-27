import NineSeparatedSubsetSums.SearchPruning

namespace NineSeparatedSubsetSums

/-- An executable conservative lower bound for an upward-closed predicate.
Fuel exhaustion keeps the current lower endpoint, so it cannot discard a candidate. -/
def monotoneLowerCut (p : ℕ → Prop) [DecidablePred p] : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel+1, lo, hi =>
    if hi ≤ lo then lo else
      let mid := (lo + hi) / 2
      if p mid then min mid (monotoneLowerCut p fuel lo mid)
      else monotoneLowerCut p fuel (mid+1) hi

theorem monotoneLowerCut_sound (p : ℕ → Prop) [DecidablePred p]
    (mono : ∀ {x y}, x ≤ y → p x → p y) (fuel lo hi x : ℕ)
    (hlo : lo ≤ x) (hhi : x ≤ hi) (hx : p x) :
    monotoneLowerCut p fuel lo hi ≤ x := by
  induction fuel generalizing lo hi with
  | zero => exact hlo
  | succ fuel ih =>
    rw [monotoneLowerCut]
    split
    · exact hlo
    · dsimp only
      split
      · by_cases hw : x ≤ (lo+hi)/2
        · exact (Nat.min_le_right _ _).trans (ih lo ((lo+hi)/2) hlo hw)
        · exact (Nat.min_le_left _ _).trans (by omega)
      · rename_i hn
        have hw : (lo+hi)/2+1 ≤ x := by
          by_contra! h
          exact hn (mono (by omega) hx)
        exact ih ((lo+hi)/2+1) hi hw hhi

theorem length_le_of_descending_positive (xs : List ℕ) (h : ℕ)
    (d : xs.Pairwise (· > ·)) (b : ∀ x ∈ xs, x ≤ h)
    (p : ∀ x ∈ xs, 0 < x) : xs.length ≤ h := by
  induction xs generalizing h with
  | nil => exact Nat.zero_le h
  | cons x tail ih =>
    obtain ⟨hx, hd⟩ := List.pairwise_cons.mp d
    have l := ih (x-1) hd (fun y hy => by have := hx y hy; omega)
      (fun y hy => p y (List.mem_cons_of_mem _ hy))
    have hp := p x List.mem_cons_self
    have hb := b x List.mem_cons_self
    simp only [List.length_cons]
    omega

/-- Lower endpoint for the next choice, calculated before any subset-mask test. -/
def capacityWindow (k hi s q minSum minSq : ℕ) : ℕ :=
  monotoneLowerCut (fun a => minSum ≤ s + topSum k a ∧ minSq ≤ q + topSquare k a)
    (Nat.log2 hi + 1) k hi

theorem capacityWindow_sound (xs : List ℕ) (hi a s q minSum minSq : ℕ)
    (d : xs.Pairwise (· > ·)) (b : ∀ x ∈ xs, x ≤ a)
    (p : ∀ x ∈ xs, 0 < x) (aHi : a ≤ hi)
    (hs : minSum ≤ s + xs.sum) (hq : minSq ≤ q + (xs.map (· ^ 2)).sum) :
    capacityWindow xs.length hi s q minSum minSq ≤ a := by
  unfold capacityWindow
  apply monotoneLowerCut_sound
  · intro x y h hxy
    exact ⟨hxy.1.trans (Nat.add_le_add_left (topSum_mono xs.length h) s),
      hxy.2.trans (Nat.add_le_add_left (topSquare_mono xs.length h) q)⟩
  · exact length_le_of_descending_positive xs a d b p
  · exact aHi
  · exact capacity_cut_sound xs a s q minSum minSq d b hs hq

#print axioms monotoneLowerCut_sound
#print axioms capacityWindow_sound
end NineSeparatedSubsetSums
