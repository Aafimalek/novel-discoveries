import EulerAllUsedProfile

namespace LatinGap
open Finset

/-- Each coordinate has exactly one label of frequency two and all
five remaining labels have frequency three in the all-used branch. -/
theorem all_used_profile {D : Design 6} (hD : Linear D) (hsize : D.card = 17)
    (hm : ∀ x : Label 6, 2 ≤ freq D x)
    (hall : ∀ (i j : Coord) (a b : Fin 6), i ≠ j →
      freq D (i,a) = 2 → freq D (j,b) = 2 → Used D (i,a) (j,b))
    (i : Coord) :
    ∃ a : Fin 6, freq D (i,a) = 2 ∧ ∀ b : Fin 6, b ≠ a → freq D (i,b) = 3 := by
  obtain ⟨a,ha,hunique⟩ := all_used_unique_low hD hsize hm hall i
  refine ⟨a,ha,?_⟩
  let E := (univ : Finset (Fin 6)).erase a
  have hg (b : Fin 6) (hb : b ∈ E) : 3 ≤ freq D (i,b) := by
    have hne := (mem_erase.mp hb).1
    have hw := hm (i,b)
    have ht : freq D (i,b) ≠ 2 := fun h => hne (hunique b h)
    omega
  have hE : E.card = 5 := by
    simp [E]
  have ht : ∑ b ∈ E, freq D (i,b) = 15 := by
    have h := sum_erase_add (univ : Finset (Fin 6)) (fun b => freq D (i,b)) (mem_univ a)
    change (∑ b ∈ E, freq D (i,b)) + freq D (i,a) = ∑ b : Fin 6, freq D (i,b) at h
    rw [sum_freq,hsize,ha] at h
    omega
  intro b hb
  have hbE : b ∈ E := mem_erase.mpr ⟨hb,mem_univ _⟩
  have hlow := hg b hbE
  by_contra! h
  have hstrict : 3 < freq D (i,b) := by omega
  have z : (∑ _b ∈ E, (3:ℕ)) < ∑ b ∈ E, freq D (i,b) :=
    sum_lt_sum hg ⟨b,hbE,hstrict⟩
  have h15 : (∑ _b ∈ E, (3:ℕ)) = 15 := by simp [hE]
  rw [ht,h15] at z
  exact (Nat.lt_irrefl 15) z

#print axioms all_used_profile
end LatinGap

namespace LatinGap
open Finset

/-- There are four distinct words outside the central all-low word,
each containing just its corresponding low label. -/
theorem all_used_four_outer_words {n : ℕ} {D : Design n} (hD : Linear D)
    (a : Word n) (ha : a ∈ D) (hl : ∀ i, freq D (i,a i) = 2) :
    ∃ outer : Coord → Word n, Function.Injective outer ∧
      ∀ i, outer i ∈ D ∧ outer i i = a i ∧
        ∀ j, j ≠ i → outer i j ≠ a j := by
  classical
  have find (i : Coord) : ∃ w : Word n, w ∈ D ∧ w i = a i ∧ w ≠ a := by
    let I := incident D (i,a i)
    have mem : a ∈ I := mem_filter.mpr ⟨ha,rfl⟩
    have hb : (I.erase a).card = 1 := by
      rw [card_erase_of_mem mem]
      change freq D (i,a i) - 1 = 1
      simp [hl]
    obtain ⟨w,hw⟩ := card_pos.mp (show 0 < (I.erase a).card by omega)
    obtain ⟨hne,hI⟩ := mem_erase.mp hw
    obtain ⟨hD', hmatch⟩ := mem_filter.mp hI
    exact ⟨w,hD',hmatch,hne⟩
  choose w hw hwi hwne using find
  have noOther (i j : Coord) (hne : j ≠ i) : w i j ≠ a j := fun h =>
    hwne i (hD (hw i) ha hne.symm (hwi i) h)
  refine ⟨w,?_,fun i => ⟨hw i,hwi i,noOther i⟩⟩
  intro i j e
  by_contra hn
  apply noOther i j (fun h => hn h.symm)
  exact (congrFun e j).trans (hwi j)
#print axioms all_used_four_outer_words
end LatinGap
