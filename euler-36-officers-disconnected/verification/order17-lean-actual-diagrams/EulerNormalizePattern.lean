import EulerRename

namespace LatinGap

private theorem move_fix (p : Equiv.Perm (Fin 6)) (a : Fin 6) (b : Fin 6)
    (x : Fin 6) (ha : x ≠ a) (hb : p x ≠ b) :
    (p.trans (Equiv.swap (p a) b)) x = p x := by
  exact Equiv.swap_apply_of_ne_of_ne (p.injective.ne ha) hb

/-- After fixing a low symbol as zero, the first three encountered nonzero
symbols can be relabeled by their order of first occurrence. -/
theorem first_occurrence_pattern (d a b c : Fin 6)
    (ha : a ≠ d) (hb : b ≠ d) (hc : c ≠ d) :
    ∃ p : Equiv.Perm (Fin 6), p d = 0 ∧ p a = 1 ∧
      p b = (if b = a then 1 else 2) ∧
      p c = (if c = a then 1 else if c = b then (if b = a then 1 else 2)
        else if b = a then 2 else 3) := by
  let r : Equiv.Perm (Fin 6) := Equiv.swap d 0
  have rd : r d = 0 := Equiv.swap_apply_left _ _
  let s : Equiv.Perm (Fin 6) := r.trans (Equiv.swap (r a) 1)
  have sd : s d = 0 := (move_fix r a 1 d ha.symm (by rw [rd]; decide)).trans rd
  have sa : s a = 1 := Equiv.swap_apply_left _ _
  by_cases ba : b = a
  · subst b
    by_cases ca : c = a
    · subst c
      exact ⟨s,sd,sa,by simpa using sa,by simpa using sa⟩
    · let t : Equiv.Perm (Fin 6) := s.trans (Equiv.swap (s c) 2)
      have td : t d = 0 := (move_fix s c 2 d hc.symm (by rw [sd]; decide)).trans sd
      have ta : t a = 1 := (move_fix s c 2 a (fun h => ca h.symm) (by rw [sa]; decide)).trans sa
      have tc : t c = 2 := Equiv.swap_apply_left _ _
      exact ⟨t,td,ta,by simpa using ta,by simpa [ca] using tc⟩
  · let t : Equiv.Perm (Fin 6) := s.trans (Equiv.swap (s b) 2)
    have td : t d = 0 := (move_fix s b 2 d hb.symm (by rw [sd]; decide)).trans sd
    have ta : t a = 1 := (move_fix s b 2 a (fun h => ba h.symm) (by rw [sa]; decide)).trans sa
    have tb : t b = 2 := Equiv.swap_apply_left _ _
    by_cases ca : c = a
    · subst c
      exact ⟨t,td,ta,by simpa [ba] using tb,by simpa using ta⟩
    · by_cases cb : c = b
      · subst c
        exact ⟨t,td,ta,by simpa [ba] using tb,by simpa [ba] using tb⟩
      · let u : Equiv.Perm (Fin 6) := t.trans (Equiv.swap (t c) 3)
        have ud : u d = 0 := (move_fix t c 3 d hc.symm (by rw [td]; decide)).trans td
        have ua : u a = 1 := (move_fix t c 3 a (fun h => ca h.symm) (by rw [ta]; decide)).trans ta
        have ub : u b = 2 := (move_fix t c 3 b (fun h => cb h.symm) (by rw [tb]; decide)).trans tb
        have uc : u c = 3 := Equiv.swap_apply_left _ _
        exact ⟨u,ud,ua,by simpa [ba] using ub,by simpa [ba,ca,cb] using uc⟩
#print axioms first_occurrence_pattern
end LatinGap
