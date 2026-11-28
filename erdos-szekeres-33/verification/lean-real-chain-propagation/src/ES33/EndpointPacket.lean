import ES33.LocalCNF

namespace ES33

/-- The six ternary packet clauses in Baek–Balko's endpoint-DP generator.
The two forbidden values of each repeated endpoint sign give a clause each. -/
def EndpointPacket (a b c d : Bool) : Prop :=
  (a = true ∧ d = true → b = true) ∧
  (b = true ∧ d = true → c = true) ∧
  (a = true ∧ c = true → b = true) ∧
  (a = false ∧ d = false → b = false) ∧
  (b = false ∧ d = false → c = false) ∧
  (a = false ∧ c = false → b = false)

/-- No loss of four-point signotope information relative to the geometric reduction. -/
theorem endpointPacket_iff (a b c d : Bool) :
    EndpointPacket a b c d ↔ packetAllowed (a, b, c, d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [EndpointPacket, packetAllowed]

theorem endpointPacket_of_ordered_quad (a b c d : Plane)
    (hab : a.1 < b.1) (hbc : b.1 < c.1) (hcd : c.1 < d.1) :
    EndpointPacket (positiveBit (orient a b c)) (positiveBit (orient a b d))
      (positiveBit (orient a c d)) (positiveBit (orient b c d)) :=
  (endpointPacket_iff _ _ _ _).mpr (ordered_quad_signotope a b c d hab hbc hcd)

/-- A signotope packet with equal outside signs is constant. This is the
local closure step for a monochromatic cup or cap. -/
theorem endpointPacket_eq_of_outer_eq {a b c d : Bool}
    (h : EndpointPacket a b c d) (had : a = d) : b = a ∧ c = a := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [EndpointPacket]

/-- In an increasing chain of triples, agreement of consecutive signs
implies agreement of every triple sign. This is the closure needed by
endpoint cup/cap recurrences, after reindexing to the selected chain. -/
theorem chain_sign_of_consecutive (χ : ℕ → ℕ → ℕ → Bool) (bound : ℕ) (v : Bool)
    (hp : ∀ a b c d, a < b → b < c → c < d → d < bound →
      EndpointPacket (χ a b c) (χ a b d) (χ a c d) (χ b c d))
    (hc : ∀ j, j + 2 < bound → χ j (j + 1) (j + 2) = v) :
    ∀ i j k, i < j → j < k → k < bound → χ i j k = v := by
  have aux (span : ℕ) : ∀ i j k, k-i = span → i < j → j < k →
      k < bound → χ i j k = v := by
    induction span using Nat.strong_induction_on with
    | ind span ih =>
      intro i j k hspan hij hjk hk
      by_cases hnext : j+1 < k
      · have h₁ := ih (j+1-i) (by omega) i j (j+1) rfl hij (by omega) (by omega)
        have h₂ := ih (k-j) (by omega) j (j+1) k rfl (by omega) hnext hk
        exact (endpointPacket_eq_of_outer_eq (hp i j (j+1) k hij (by omega) hnext hk)
          (h₁.trans h₂.symm)).1.trans h₁
      · by_cases hprev : i+1 < j
        · have h₁ := ih (j-i) (by omega) i (i+1) j rfl (by omega) hprev (by omega)
          have h₂ := ih (k-(i+1)) (by omega) (i+1) j k rfl hprev hjk hk
          exact (endpointPacket_eq_of_outer_eq (hp i (i+1) j k (by omega) hprev hjk hk)
            (h₁.trans h₂.symm)).2.trans h₁
        · have e₁ : j = i+1 := by omega
          have e₂ : k = i+2 := by omega
          subst j
          subst k
          exact hc i hk
  intro i j k hij hjk hk
  exact aux (k-i) i j k rfl hij hjk hk

/-- The chain theorem applies to any increasing selection of vertices, not
just intervals in the ambient ordering. -/
theorem selected_chain_sign_of_consecutive {n : ℕ}
    (χ : Fin n → Fin n → Fin n → Bool) (hχ : SignotopeConstraints n χ)
    (f : ℕ → Fin n) (bound : ℕ) (v : Bool)
    (hf : ∀ i j, i < j → j < bound → f i < f j)
    (hc : ∀ j, j + 2 < bound → χ (f j) (f (j+1)) (f (j+2)) = v) :
    ∀ i j k, i < j → j < k → k < bound → χ (f i) (f j) (f k) = v := by
  refine chain_sign_of_consecutive (fun i j k => χ (f i) (f j) (f k)) bound v ?_ hc
  intro a b c d hab hbc hcd hd
  apply (endpointPacket_iff _ _ _ _).mpr
  exact hχ _ _ _ _ (hf a b hab (by omega)) (hf b c hbc (by omega)) (hf c d hcd hd)

/-- Opposite monochromatic chains with common endpoints cannot share an
interior vertex. In particular their lengths can be added, subtracting
only the two endpoints, in the signotope relaxation. -/
theorem opposite_chains_no_shared_interior {n : ℕ}
    (χ : Fin n → Fin n → Fin n → Bool) (hχ : SignotopeConstraints n χ)
    (f g : ℕ → Fin n) (s t : ℕ)
    (hf : ∀ i j, i < j → j < s + 1 → f i < f j)
    (hg : ∀ i j, i < j → j < t + 1 → g i < g j)
    (hcf : ∀ j, j + 2 < s + 1 → χ (f j) (f (j+1)) (f (j+2)) = true)
    (hcg : ∀ j, j + 2 < t + 1 → χ (g j) (g (j+1)) (g (j+2)) = false)
    (hl : f 0 = g 0) (hr : f s = g t)
    {i j : ℕ} (hi : 0 < i) (his : i < s) (hj : 0 < j) (hjt : j < t) :
    f i ≠ g j := by
  intro h
  have h₁ := selected_chain_sign_of_consecutive χ hχ f (s+1) true hf hcf
    0 i s hi his (by omega)
  have h₂ := selected_chain_sign_of_consecutive χ hχ g (t+1) false hg hcg
    0 j t hj hjt (by omega)
  rw [hl, h, hr, h₂] at h₁
  contradiction

#print axioms opposite_chains_no_shared_interior
#print axioms selected_chain_sign_of_consecutive
#print axioms chain_sign_of_consecutive
#print axioms endpointPacket_iff
#print axioms endpointPacket_of_ordered_quad
#print axioms endpointPacket_eq_of_outer_eq

end ES33
