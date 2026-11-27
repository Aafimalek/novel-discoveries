import OrbitCheck

namespace G449OrbitArithmetic

abbrev Coeff12 := Fin 12 → Int

def restrict12 (v : V) : Coeff12 := fun i => v i.val

/-- Turn the finite, checked orbit forest into a proof by decreasing rank.
The geometry is kept out of this computational data check. -/
theorem transport_of_orbit_roots (P : Coeff12 → Prop)
    (root_ok : ∀ k, roots.contains k = true → P (restrict12 (dirs k)))
    (spin_ok : ∀ v, P (restrict12 v) → P (restrict12 (spin v)))
    (neg_ok : ∀ v : Coeff12, P v → P (fun i => -v i)) :
    ∀ k < 49, P (restrict12 (dirs k)) := by
  suffices K : ∀ r, ∀ j : Nat, j < 49 → (parent j).rank = r →
      P (restrict12 (dirs j)) by
    intro k hk
    exact K _ k hk rfl
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro j hj hr
    have chk := List.all_eq_true.mp all_steps_arithmetic j (List.mem_range.mpr hj)
    rcases orbitStepBool_sound dirs parent roots j chk with base | ⟨hp,hd,heq⟩
    · exact root_ok j base
    have hlt : (parent (parent j).prev).rank < r := hr ▸ hd
    have nb := ih _ hlt _ hp rfl
    have ns := spin_ok (dirs (parent j).prev) nb
    cases hf : (parent j).spinNeg with
    | false =>
      have e : restrict12 (dirs j) = restrict12 (spin (dirs (parent j).prev)) := by
        funext t
        exact (heq t.val t.isLt).trans (by simp [restrict12,hf])
      rwa [e]
    | true =>
      have e : restrict12 (dirs j) = fun t => -restrict12 (spin (dirs (parent j).prev)) t := by
        funext t
        exact (heq t.val t.isLt).trans (by simp [restrict12,hf])
      rw [e]
      exact neg_ok _ ns

#print axioms transport_of_orbit_roots
end G449OrbitArithmetic
