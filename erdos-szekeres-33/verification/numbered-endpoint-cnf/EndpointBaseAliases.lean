import EndpointGuardCore

namespace ES33.EndpointGuard

/-- The upstream serialization does not allocate separate tertiary
states: a 3-cap is the negative sign literal and a 3-cup the positive
sign literal. Pair states, including length three, are never aliased. -/
def baseAliases {n : Nat} (χ : Signs n) (M : States n) : States n where
  capLast d a b c := if d = 3 then χ a b c = false else M.capLast d a b c
  cupFirst d a b c := if d = 3 then χ a b c = true else M.cupFirst d a b c
  capPair := M.capPair
  cupPair := M.cupPair

private theorem old_cap {n A B : Nat} {χ : Signs n} {M : States n}
    (P : PrunedPropagation χ A B M) (d : Nat) (a b c : Fin n)
    (h : a<b) (h' : b<c) (hb : d≤A) :
    (baseAliases χ M).capLast d a b c → M.capLast d a b c := by
  by_cases hd : d = 3
  · subst d
    simpa [baseAliases] using P.capThree a b c hb h h'
  · simp [baseAliases,hd]

private theorem old_cup {n A B : Nat} {χ : Signs n} {M : States n}
    (P : PrunedPropagation χ A B M) (d : Nat) (a b c : Fin n)
    (h : a<b) (h' : b<c) (hb : d≤B) :
    (baseAliases χ M).cupFirst d a b c → M.cupFirst d a b c := by
  by_cases hd : d = 3
  · subst d
    simpa [baseAliases] using P.cupThree a b c hb h h'
  · simp [baseAliases,hd]

theorem PrunedPropagation.baseAliases {n A B : Nat} {χ : Signs n} {M : States n}
    (P : PrunedPropagation χ A B M) :
    PrunedPropagation χ A B (ES33.EndpointGuard.baseAliases χ M) := by
  refine ⟨P.capTwo,P.cupTwo,?_,?_,?_,?_,?_,?_,P.capShorten,P.cupShorten⟩
  · intro a b c hd hab hbc h
    simpa [ES33.EndpointGuard.baseAliases] using h
  · intro a b c hd hab hbc h
    simpa [ES33.EndpointGuard.baseAliases] using h
  · intro d a b c e hf hb hh hce hs
    have X := old_cap P d a b c hf.1 hf.2.1 (by omega) hh
    have Y := P.capStep d a b c e hf hb X hce hs
    have hd := hf.2.2.1
    have ne : d+1 ≠ 3 := by omega
    simpa [ES33.EndpointGuard.baseAliases,ne] using Y
  · intro d a b c e hf hb hh hab hs
    have X := old_cup P d b c e hf.1 hf.2.1 (by omega) hh
    have Y := P.cupStep d a b c e hf hb X hab hs
    have hd := hf.2.2.1
    have ne : d+1 ≠ 3 := by omega
    simpa [ES33.EndpointGuard.baseAliases,ne] using Y
  · intro d a b c hf hb hh
    exact P.capProject d a b c hf hb (old_cap P d a b c hf.1 hf.2.1 hb hh)
  · intro d a b c hf hb hh
    exact P.cupProject d a b c hf hb (old_cup P d a b c hf.1 hf.2.1 hb hh)

theorem pruned_base_aliases_equisat {n : Nat} (χ : Signs n) (K A B : Nat) :
    (∃ M, PrunedPropagation χ A B (baseAliases χ M) ∧
        PrunedExclusions K A B (baseAliases χ M)) ↔
      (∃ M, PrunedPropagation χ A B M ∧ PrunedExclusions K A B M) := by
  constructor
  · rintro ⟨M,P,E⟩
    exact ⟨baseAliases χ M,P,E⟩
  · rintro ⟨M,P,E⟩
    exact ⟨M,P.baseAliases,E⟩

#print axioms PrunedPropagation.baseAliases
#print axioms pruned_base_aliases_equisat

end ES33.EndpointGuard
