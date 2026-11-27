import Lean

namespace ES33.EndpointGuard

abbrev Signs (n : Nat) := Fin n → Fin n → Fin n → Bool

structure States (n : Nat) where
  capLast : Nat → Fin n → Fin n → Fin n → Prop
  cupFirst : Nat → Fin n → Fin n → Fin n → Prop
  capPair : Nat → Fin n → Fin n → Prop
  cupPair : Nat → Fin n → Fin n → Prop

/-- Typed propagation constraints for the endpoint-chain scheme. In this
presentation out-of-span states are not omitted. No DIMACS IDs are asserted. -/
structure Propagation {n : Nat} (χ : Signs n) (A B : Nat) (M : States n) : Prop where
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

def Exclusions {n : Nat} (K A B : Nat) (M : States n) : Prop :=
  (∀ a c, ¬ M.capPair A a c) ∧ (∀ a c, ¬ M.cupPair B a c) ∧
    (∀ s t a c, 2 ≤ s → s ≤ A → 2 ≤ t → t ≤ B → s+t=K+2 →
      ¬ (M.capPair s a c ∧ M.cupPair t a c))

/-- Exactly the interval capacity tests used by the endpoint generator. -/
def PairFits {n : Nat} (d : Nat) (a c : Fin n) : Prop :=
  a < c ∧ 2 ≤ d ∧ d ≤ c.val-a.val+1

def CapFits {n : Nat} (d : Nat) (a b c : Fin n) : Prop :=
  a < b ∧ b < c ∧ 3 ≤ d ∧ d ≤ b.val-a.val+2

def CupFits {n : Nat} (d : Nat) (a b c : Fin n) : Prop :=
  a < b ∧ b < c ∧ 3 ≤ d ∧ d ≤ c.val-b.val+2

/-- Upstream-style guard placement: omit out-of-span cells and instantiate
clauses only on the ordered references that remain. Size thresholds are
separate from span guards. This is still a typed family of clauses. -/
structure PrunedPropagation {n : Nat} (χ : Signs n) (A B : Nat) (M : States n) : Prop where
  capTwo : ∀ a c, a<c → M.capPair 2 a c
  cupTwo : ∀ a c, a<c → M.cupPair 2 a c
  capThree : ∀ a b c, 3≤A → a<b → b<c → χ a b c=false → M.capLast 3 a b c
  cupThree : ∀ a b c, 3≤B → a<b → b<c → χ a b c=true → M.cupFirst 3 a b c
  capStep : ∀ d a b c e, CapFits d a b c → d+1≤A →
    M.capLast d a b c → c<e → χ b c e=false → M.capLast (d+1) a c e
  cupStep : ∀ d a b c e, CupFits d b c e → d+1≤B →
    M.cupFirst d b c e → a<b → χ a b c=true → M.cupFirst (d+1) a b e
  capProject : ∀ d a b c, CapFits d a b c → d≤A → M.capLast d a b c → M.capPair d a c
  cupProject : ∀ d a b c, CupFits d a b c → d≤B → M.cupFirst d a b c → M.cupPair d a c
  capShorten : ∀ d a c, 2≤d → PairFits (d+1) a c → d+1≤A → M.capPair (d+1) a c → M.capPair d a c
  cupShorten : ∀ d a c, 2≤d → PairFits (d+1) a c → d+1≤B → M.cupPair (d+1) a c → M.cupPair d a c

def PrunedExclusions {n : Nat} (K A B : Nat) (M : States n) : Prop :=
  (∀ a c, PairFits A a c → ¬ M.capPair A a c) ∧
  (∀ a c, PairFits B a c → ¬ M.cupPair B a c) ∧
  (∀ s t a c, PairFits s a c → PairFits t a c → s≤A → t≤B → s+t=K+2 →
      ¬ (M.capPair s a c ∧ M.cupPair t a c))

def restrict {n : Nat} (M : States n) : States n where
  capLast d a b c := CapFits d a b c ∧ M.capLast d a b c
  cupFirst d a b c := CupFits d a b c ∧ M.cupFirst d a b c
  capPair d a c := PairFits d a c ∧ M.capPair d a c
  cupPair d a c := PairFits d a c ∧ M.cupPair d a c

private theorem pair_two {n : Nat} {a c : Fin n} (h : a<c) : PairFits 2 a c := by
  have H : a.val<c.val := h
  exact ⟨h,by decide,by omega⟩

private theorem cap_three {n : Nat} {a b c : Fin n} (h : a<b) (h' : b<c) : CapFits 3 a b c := by
  have H : a.val<b.val := h
  exact ⟨h,h',by decide,by omega⟩

private theorem cup_three {n : Nat} {a b c : Fin n} (h : a<b) (h' : b<c) : CupFits 3 a b c := by
  have H : b.val<c.val := h'
  exact ⟨h,h',by decide,by omega⟩

private theorem cap_step {n d : Nat} {a b c e : Fin n} (h : CapFits d a b c) (h' : c<e) :
    CapFits (d+1) a c e := by
  have h₁ : a.val < b.val := h.1
  have h₂ : b.val < c.val := h.2.1
  have h₃ := h.2.2.1
  have h₄ := h.2.2.2
  exact ⟨(show _ < _ from Nat.lt_trans h.1 h.2.1),h',by omega,by omega⟩

private theorem cup_step {n d : Nat} {a b c e : Fin n} (h : CupFits d b c e) (h' : a<b) :
    CupFits (d+1) a b e := by
  have h₁ : b.val < c.val := h.1
  have h₂ : c.val < e.val := h.2.1
  have h₃ := h.2.2.1
  have h₄ := h.2.2.2
  exact ⟨h',(show _ < _ from Nat.lt_trans h.1 h.2.1),by omega,by omega⟩

private theorem cap_project {n d : Nat} {a b c : Fin n} (h : CapFits d a b c) :
    PairFits d a c := by
  have h₁ : a.val < b.val := h.1
  have h₂ : b.val < c.val := h.2.1
  have h₃ := h.2.2.1
  have h₄ := h.2.2.2
  exact ⟨(show _ < _ from Nat.lt_trans h.1 h.2.1),by omega,by omega⟩

private theorem cup_project {n d : Nat} {a b c : Fin n} (h : CupFits d a b c) :
    PairFits d a c := by
  have h₁ : a.val < b.val := h.1
  have h₂ : b.val < c.val := h.2.1
  have h₃ := h.2.2.1
  have h₄ := h.2.2.2
  exact ⟨(show _ < _ from Nat.lt_trans h.1 h.2.1),by omega,by omega⟩

private theorem pair_shorten {n d : Nat} {a c : Fin n} (h : PairFits (d+1) a c)
    (h' : 2≤d) : PairFits d a c := ⟨h.1,h',by have := h.2.2; omega⟩

/-- Missing cells may be filled with false without invalidating the
unpruned one-way structure. Every instantiation from a legal source
reference stays within the target's interval capacity. -/
theorem PrunedPropagation.to_full {n A B : Nat} {χ : Signs n} {M : States n}
    (P : PrunedPropagation χ A B M) : Propagation χ A B (restrict M) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact fun a c h => ⟨pair_two h,P.capTwo a c h⟩
  · exact fun a c h => ⟨pair_two h,P.cupTwo a c h⟩
  · exact fun a b c hd hab hbc h => ⟨cap_three hab hbc,P.capThree a b c hd hab hbc h⟩
  · exact fun a b c hd hab hbc h => ⟨cup_three hab hbc,P.cupThree a b c hd hab hbc h⟩
  · rintro d a b c e _ hd ⟨hf,h⟩ hce hcol
    exact ⟨cap_step hf hce,P.capStep d a b c e hf hd h hce hcol⟩
  · rintro d a b c e _ hd ⟨hf,h⟩ hab hcol
    exact ⟨cup_step hf hab,P.cupStep d a b c e hf hd h hab hcol⟩
  · rintro d a b c _ hd ⟨hf,h⟩
    exact ⟨cap_project hf,P.capProject d a b c hf hd h⟩
  · rintro d a b c _ hd ⟨hf,h⟩
    exact ⟨cup_project hf,P.cupProject d a b c hf hd h⟩
  · rintro d a c h₂ hd ⟨hf,h⟩
    exact ⟨pair_shorten hf h₂,P.capShorten d a c h₂ hf hd h⟩
  · rintro d a c h₂ hd ⟨hf,h⟩
    exact ⟨pair_shorten hf h₂,P.cupShorten d a c h₂ hf hd h⟩

theorem Propagation.to_pruned {n A B : Nat} {χ : Signs n} {M : States n}
    (P : Propagation χ A B M) : PrunedPropagation χ A B M := by
  refine ⟨P.capTwo,P.cupTwo,P.capThree,P.cupThree,?_,?_,?_,?_,?_,?_⟩
  · exact fun d a b c e hf => P.capStep d a b c e hf.2.2.1
  · exact fun d a b c e hf => P.cupStep d a b c e hf.2.2.1
  · exact fun d a b c hf => P.capProject d a b c hf.2.2.1
  · exact fun d a b c hf => P.cupProject d a b c hf.2.2.1
  · exact fun d a c h₂ _ => P.capShorten d a c h₂
  · exact fun d a c h₂ _ => P.cupShorten d a c h₂

theorem PrunedExclusions.to_full {n K A B : Nat} {M : States n}
    (H : PrunedExclusions K A B M) : Exclusions K A B (restrict M) := by
  obtain ⟨hc,hu,hb⟩ := H
  refine ⟨?_,?_,?_⟩
  · rintro a c ⟨hf,h⟩
    exact hc a c hf h
  · rintro a c ⟨hf,h⟩
    exact hu a c hf h
  · rintro s t a c _ hs _ ht he ⟨⟨hfs,hn⟩,⟨hft,hp⟩⟩
    exact hb s t a c hfs hft hs ht he ⟨hn,hp⟩

theorem Exclusions.to_pruned {n K A B : Nat} {M : States n}
    (H : Exclusions K A B M) : PrunedExclusions K A B M := by
  obtain ⟨hc,hu,hb⟩ := H
  exact ⟨fun a c _ => hc a c,fun a c _ => hu a c,
    fun s t a c hfs hft hs ht he => hb s t a c hfs.2.1 hs hft.2.1 ht he⟩

/-- Guard-pruning preserves exactly the projected solution space.
DIMACS IDs and the clause serialization are still external. -/
theorem pruned_iff_full_model {n : Nat} (χ : Signs n) (K A B : Nat) :
    (∃ M : States n, PrunedPropagation χ A B M ∧ PrunedExclusions K A B M) ↔
      (∃ M : States n, Propagation χ A B M ∧ Exclusions K A B M) := by
  constructor
  · rintro ⟨M,P,H⟩
    exact ⟨restrict M,P.to_full,H.to_full⟩
  · rintro ⟨M,P,H⟩
    exact ⟨M,P.to_pruned,H.to_pruned⟩

#print axioms PrunedPropagation.to_full
#print axioms pruned_iff_full_model

end ES33.EndpointGuard
