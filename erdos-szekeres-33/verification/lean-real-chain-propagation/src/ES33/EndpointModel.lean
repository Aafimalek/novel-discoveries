import ES33.EndpointRecurrence

namespace ES33.Endpoint

/-- Views of the four auxiliary families. These propositions need not equal
true chain existence; the one-way implications suffice to force actual
witnesses. A semantic assignment gives an exact model when one exists. -/
structure States (n : ℕ) where
  capLast : ℕ → Fin n → Fin n → Fin n → Prop
  cupFirst : ℕ → Fin n → Fin n → Fin n → Prop
  capPair : ℕ → Fin n → Fin n → Prop
  cupPair : ℕ → Fin n → Fin n → Prop

/-- Typed propagation constraints for the endpoint-chain scheme. In this
presentation out-of-span states are not omitted. No DIMACS IDs are asserted. -/
structure Propagation {n : ℕ} (χ : Signs n) (A B : ℕ) (M : States n) : Prop where
  capTwo : ∀ a c, a < c → M.capPair 2 a c
  cupTwo : ∀ a c, a < c → M.cupPair 2 a c
  capThree : ∀ a b c, 3 ≤ A → a < b → b < c → χ a b c = false → M.capLast 3 a b c
  cupThree : ∀ a b c, 3 ≤ B → a < b → b < c → χ a b c = true → M.cupFirst 3 a b c
  capStep : ∀ d a b c e, 3 ≤ d → d+1 ≤ A →
    M.capLast d a b c → c < e → χ b c e = false → M.capLast (d+1) a c e
  cupStep : ∀ d a b c e, 3 ≤ d → d+1 ≤ B →
    M.cupFirst d b c e → a < b → χ a b c = true → M.cupFirst (d+1) a b e
  capProject : ∀ d a b c, 3 ≤ d → d ≤ A →
    M.capLast d a b c → M.capPair d a c
  cupProject : ∀ d a b c, 3 ≤ d → d ≤ B →
    M.cupFirst d a b c → M.cupPair d a c
  capShorten : ∀ d a c, 2 ≤ d → d+1 ≤ A → M.capPair (d+1) a c → M.capPair d a c
  cupShorten : ∀ d a c, 2 ≤ d → d+1 ≤ B → M.cupPair (d+1) a c → M.cupPair d a c

def actual {n : ℕ} (χ : Signs n) : States n where
  capLast := EndState χ false
  cupFirst := StartState χ true
  capPair := Ends χ false
  cupPair := Ends χ true

/-- Actual chain existence gives a model of all structural clauses. -/
theorem actual_propagates {n : ℕ} {χ : Signs n}
    (hχ : SignotopeConstraints n χ) (A B : ℕ) : Propagation χ A B (actual χ) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact fun a c h => (ends_two_iff χ false a c).mpr h
  · exact fun a c h => (ends_two_iff χ true a c).mpr h
  · exact fun a b c _ hab hbc h => (end_base χ false a b c).mpr ⟨hab,hbc,h⟩
  · exact fun a b c _ hab hbc h => (start_base χ true a b c).mpr ⟨hab,hbc,h⟩
  · exact fun d a b c e hd _ h hce hcol =>
      (end_succ χ false a c e hd).mpr ⟨b,h,hce,hcol⟩
  · exact fun d a b c e hd _ h hab hcol =>
      (start_succ χ true a b e hd).mpr ⟨c,h,hab,hcol⟩
  · rintro d a b c _ _ ⟨f,hf,ha,_,hc⟩
    exact ⟨f,hf,ha,hc⟩
  · rintro d a b c _ _ ⟨f,hf,ha,_,hc⟩
    exact ⟨f,hf,ha,hc⟩
  · exact fun d a c hd _ h => Ends.shorten hχ hd h
  · exact fun d a c hd _ h => Ends.shorten hχ hd h

theorem Propagation.forward_forced {n A B : ℕ} {χ : Signs n} {M : States n}
    (P : Propagation χ A B M) (d : ℕ) (a b c : Fin n)
    (hd : d+3 ≤ A) (h : forward χ false d a b c) : M.capLast (d+3) a b c := by
  induction d generalizing a b c with
  | zero =>
    obtain ⟨hab,hbc,hcol⟩ := h
    exact P.capThree a b c hd hab hbc hcol
  | succ d ih =>
    obtain ⟨x,hx,hbc,hcol⟩ := h
    have H := P.capStep (d+3) a x b c (by omega) (by omega)
      (ih a x b (by omega) hx) hbc hcol
    simpa only [show d+1+3=d+3+1 by omega] using H

theorem Propagation.backward_forced {n A B : ℕ} {χ : Signs n} {M : States n}
    (P : Propagation χ A B M) (d : ℕ) (a b c : Fin n)
    (hd : d+3 ≤ B) (h : backward χ true d a b c) : M.cupFirst (d+3) a b c := by
  induction d generalizing a b c with
  | zero =>
    obtain ⟨hab,hbc,hcol⟩ := h
    exact P.cupThree a b c hd hab hbc hcol
  | succ d ih =>
    obtain ⟨x,hx,hab,hcol⟩ := h
    have H := P.cupStep (d+3) a b x c (by omega) (by omega)
      (ih b x c (by omega) hx) hab hcol
    simpa only [show d+1+3=d+3+1 by omega] using H

/-- Every cap that actually exists is forced in any model of the one-way
structural constraints, including the base two-chain. -/
theorem Propagation.cap_forced {n A B d : ℕ} {χ : Signs n} {M : States n}
    (P : Propagation χ A B M) {a c : Fin n} (h₂ : 2 ≤ d) (hd : d ≤ A)
    (h : Ends χ false d a c) : M.capPair d a c := by
  by_cases he : d=2
  · subst d
    exact P.capTwo a c ((ends_two_iff χ false a c).mp h)
  have he' : d-3+3=d := by omega
  have h' : Ends χ false (d-3+3) a c := by simpa only [he'] using h
  obtain ⟨b,hf⟩ := (ends_iff_forward χ false (d-3) a c).mp h'
  have H := P.forward_forced (d-3) a b c (by omega) hf
  exact P.capProject d a b c (by omega) hd (by simpa only [he'] using H)

/-- Every cup that actually exists is forced in any auxiliary model. -/
theorem Propagation.cup_forced {n A B d : ℕ} {χ : Signs n} {M : States n}
    (P : Propagation χ A B M) {a c : Fin n} (h₂ : 2 ≤ d) (hd : d ≤ B)
    (h : Ends χ true d a c) : M.cupPair d a c := by
  by_cases he : d=2
  · subst d
    exact P.cupTwo a c ((ends_two_iff χ true a c).mp h)
  have he' : d-3+3=d := by omega
  have h' : Ends χ true (d-3+3) a c := by simpa only [he'] using h
  obtain ⟨b,hf⟩ := (ends_iff_backward χ true (d-3) a c).mp h'
  have H := P.backward_forced (d-3) a b c (by omega) hf
  exact P.cupProject d a b c (by omega) hd (by simpa only [he'] using H)

/-- Exclusion clauses on the endpoint variables: no threshold cap/cup and
no pair of opposite-color chains with enough total vertices. -/
def Exclusions {n : ℕ} (K A B : ℕ) (M : States n) : Prop :=
  (∀ a c, ¬ M.capPair A a c) ∧ (∀ a c, ¬ M.cupPair B a c) ∧
    (∀ s t a c, 2 ≤ s → s ≤ A → 2 ≤ t → t ≤ B → s+t=K+2 →
      ¬ (M.capPair s a c ∧ M.cupPair t a c))

/-- The one-way typed recurrence has exactly the intended existential
semantics, after projecting out auxiliary states. The upstream gap-based
omission and DIMACS serialization are separate. -/
theorem typed_model_iff_actual {n : ℕ} {χ : Signs n} (hχ : SignotopeConstraints n χ)
    (K A B : ℕ) (hA : 2 ≤ A) (hB : 2 ≤ B) :
    (∃ M, Propagation χ A B M ∧ Exclusions K A B M) ↔ Exclusions K A B (actual χ) := by
  constructor
  · rintro ⟨M,P,hcap,hcup,hboth⟩
    refine ⟨?_,?_,?_⟩
    · exact fun a c h => hcap a c (P.cap_forced hA le_rfl h)
    · exact fun a c h => hcup a c (P.cup_forced hB le_rfl h)
    · rintro s t a c h₂s hs h₂t ht hst ⟨h₁,h₂⟩
      exact hboth s t a c h₂s hs h₂t ht hst ⟨P.cap_forced h₂s hs h₁,P.cup_forced h₂t ht h₂⟩
  · exact fun H => ⟨actual χ, actual_propagates hχ A B, H⟩

#print axioms actual_propagates
#print axioms Propagation.cap_forced
#print axioms Propagation.cup_forced
#print axioms typed_model_iff_actual

end ES33.Endpoint
