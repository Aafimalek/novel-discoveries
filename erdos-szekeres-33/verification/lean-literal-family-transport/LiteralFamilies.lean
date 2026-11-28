/- Static draft. Implements local literal semantics and the forward
conditional transport; not compiled, and not a DIMACS exhaustiveness proof. -/
import EndpointConcreteSpec

namespace ES33.EndpointConcrete

open ES33.Numbering ES33.EndpointGuard
open VerificationGoals

abbrev SatRow {n : Nat} (v : Key n → Bool) (row : List (Cell n)) : Prop :=
  ∃ x ∈ row, x.holds v

private theorem flip_holds {n : Nat} (v : Key n → Bool) (l : Cell n) :
    (flip l).holds v ↔ ¬ l.holds v := by
  rcases l with ⟨k,p⟩
  cases p <;> cases h : v k <;> simp [flip,Lit.holds,h]

private theorem unit {n : Nat} {v : Key n → Bool} (l : Cell n)
    (h : l.holds v) : SatRow v [l] := ⟨l,by simp,h⟩

private theorem deny {n : Nat} {v : Key n → Bool} (l : Cell n)
    (h : ¬l.holds v) : SatRow v [flip l] :=
  unit (flip l) ((flip_holds v l).mpr h)

private theorem imp2 {n : Nat} {v : Key n → Bool} (a b : Cell n)
    (h : a.holds v → b.holds v) : SatRow v [flip a,b] := by
  by_cases ha : a.holds v
  · exact ⟨b,by simp,h ha⟩
  · exact ⟨flip a,by simp,(flip_holds v a).mpr ha⟩

private theorem imp3 {n : Nat} {v : Key n → Bool} (a b c : Cell n)
    (h : a.holds v → b.holds v → c.holds v) : SatRow v [flip a,flip b,c] := by
  by_cases ha : a.holds v
  · by_cases hb : b.holds v
    · exact ⟨c,by simp,h ha hb⟩
    · exact ⟨flip b,by simp,(flip_holds v b).mpr hb⟩
  · exact ⟨flip a,by simp,(flip_holds v a).mpr ha⟩

private theorem denyBoth {n : Nat} {v : Key n → Bool} (a b : Cell n)
    (h : ¬ (a.holds v ∧ b.holds v)) : SatRow v [flip a,flip b] := by
  by_cases ha : a.holds v
  · exact ⟨flip b,by simp,(flip_holds v b).mpr (fun hb => h ⟨ha,hb⟩)⟩
  · exact ⟨flip a,by simp,(flip_holds v a).mpr ha⟩

def Mapped {n : Nat} (v : Key n → Bool) : States n :=
  baseAliases (signVal v) (stateVal v)

private theorem capState {n : Nat} (v : Key n → Bool) (d : Nat) (a b c : Fin n) :
    (stateLit .cap d a b c).holds v ↔ (Mapped v).capLast d a b c := by
  by_cases hd : d=3 <;>
    simp [stateLit,sign,signVal,stateKey,Mapped,baseAliases,stateVal,Lit.holds,hd]

private theorem cupState {n : Nat} (v : Key n → Bool) (d : Nat) (a b c : Fin n) :
    (stateLit .cup d a b c).holds v ↔ (Mapped v).cupFirst d a b c := by
  by_cases hd : d=3 <;>
    simp [stateLit,sign,signVal,stateKey,Mapped,baseAliases,stateVal,Lit.holds,hd]

private theorem capPair {n : Nat} (v : Key n → Bool) (d : Nat) (a c : Fin n) :
    (pairLit .cap d a c).holds v ↔ (Mapped v).capPair d a c := Iff.rfl

private theorem cupPair {n : Nat} (v : Key n → Bool) (d : Nat) (a c : Fin n) :
    (pairLit .cup d a c).holds v ↔ (Mapped v).cupPair d a c := Iff.rfl

/-- Each structural clause family as literal syntax, with its semantic
guard. Length-three triple state aliases are represented as sign literals,
not as fresh variables or unit clauses. -/
inductive Rule {n : Nat} (K A B : Nat) : List (Cell n) → Prop
  | capTwo (a c : Fin n) (h : a<c) : Rule K A B [pairLit .cap 2 a c]
  | cupTwo (a c : Fin n) (h : a<c) : Rule K A B [pairLit .cup 2 a c]
  | capThreshold (a c : Fin n) (h : PairFits A a c) :
      Rule K A B [flip (pairLit .cap A a c)]
  | cupThreshold (a c : Fin n) (h : PairFits B a c) :
      Rule K A B [flip (pairLit .cup B a c)]
  | capShorten (d : Nat) (a c : Fin n) (h₂ : 2≤d) (h : PairFits (d+1) a c)
      (hb : d+1≤A) : Rule K A B [flip (pairLit .cap (d+1) a c),pairLit .cap d a c]
  | cupShorten (d : Nat) (a c : Fin n) (h₂ : 2≤d) (h : PairFits (d+1) a c)
      (hb : d+1≤B) : Rule K A B [flip (pairLit .cup (d+1) a c),pairLit .cup d a c]
  | capProject (d : Nat) (a b c : Fin n) (h : CapFits d a b c) (hb : d≤A) :
      Rule K A B [flip (stateLit .cap d a b c),pairLit .cap d a c]
  | cupProject (d : Nat) (a b c : Fin n) (h : CupFits d a b c) (hb : d≤B) :
      Rule K A B [flip (stateLit .cup d a b c),pairLit .cup d a c]
  | capExtend (d : Nat) (a b c e : Fin n) (h : CapFits d a b c) (hb : d+1≤A)
      (he : c<e) :
      Rule K A B [flip (stateLit .cap d a b c),sign b c e,stateLit .cap (d+1) a c e]
  | cupExtend (d : Nat) (e a b c : Fin n) (h : CupFits d a b c) (hb : d+1≤B)
      (he : e<a) :
      Rule K A B [flip (stateLit .cup d a b c),sign e a b false,stateLit .cup (d+1) e a c]
  | opposite (s t : Nat) (a c : Fin n) (hs : PairFits s a c) (ht : PairFits t a c)
      (hA : s≤A) (hB : t≤B) (hk : s+t=K+2) :
      Rule K A B [flip (pairLit .cap s a c),flip (pairLit .cup t a c)]

theorem rule_sat {n K A B : Nat} {v : Key n → Bool} {row : List (Cell n)}
    (P : PrunedPropagation (signVal v) A B (Mapped v))
    (X : PrunedExclusions K A B (Mapped v)) (h : Rule K A B row) :
    SatRow v row := by
  cases h with
  | capTwo a c h => exact unit _ ((capPair v 2 a c).mpr (P.capTwo a c h))
  | cupTwo a c h => exact unit _ ((cupPair v 2 a c).mpr (P.cupTwo a c h))
  | capThreshold a c h => exact deny _ (fun hh => X.1 a c h ((capPair v A a c).mp hh))
  | cupThreshold a c h => exact deny _ (fun hh => X.2.1 a c h ((cupPair v B a c).mp hh))
  | capShorten d a c h₂ h hb =>
    exact imp2 _ _ (fun hh => (capPair v d a c).mpr
        (P.capShorten d a c h₂ h hb ((capPair v (d+1) a c).mp hh)))
  | cupShorten d a c h₂ h hb =>
    exact imp2 _ _ (fun hh => (cupPair v d a c).mpr
        (P.cupShorten d a c h₂ h hb ((cupPair v (d+1) a c).mp hh)))
  | capProject d a b c h hb =>
    exact imp2 _ _ (fun hh => (capPair v d a c).mpr
        (P.capProject d a b c h hb ((capState v d a b c).mp hh)))
  | cupProject d a b c h hb =>
    exact imp2 _ _ (fun hh => (cupPair v d a c).mpr
        (P.cupProject d a b c h hb ((cupState v d a b c).mp hh)))
  | capExtend d a b c e h hb he =>
    exact imp3 (stateLit .cap d a b c) (sign b c e false) _ (fun hh hc =>
      (capState v (d+1) a c e).mpr (P.capStep d a b c e h hb
        ((capState v d a b c).mp hh) he hc))
  | cupExtend d e a b c h hb he =>
    exact imp3 (stateLit .cup d a b c) (sign e a b) _ (fun hh hc =>
      (cupState v (d+1) e a c).mpr (P.cupStep d e a b c h hb
        ((cupState v d a b c).mp hh) he hc))
  | opposite s t a c hs ht hA hB hk =>
    exact denyBoth _ _ (fun hboth => X.2.2 s t a c hs ht hA hB hk
      ⟨(capPair v s a c).mp hboth.1,(cupPair v t a c).mp hboth.2⟩)

/-- The six packet clauses are established separately by monotonicity,
not by treating the target table as an assumption. -/
private theorem six (p q r s : Bool)
    (h : (p≤q ∧ q≤r ∧ r≤s) ∨ (s≤r ∧ r≤q ∧ q≤p)) :
    (p=true → s=true → q=true) ∧ (q=true → s=true → r=true) ∧
    (p=true → r=true → q=true) ∧
    (p=false → s=false → q=false) ∧ (q=false → s=false → r=false) ∧
    (p=false → r=false → q=false) := by
  cases p <;> cases q <;> cases r <;> cases s <;> simp_all
  all_goals exact (by decide : ¬ (true ≤ false)) h

theorem packet_sat {n : Nat} {v : Key n → Bool} {a b c e : Fin n}
    (S : signotope n (signVal v)) (hab : a<b) (hbc : b<c) (hce : c<e)
    {row : List (Cell n)} (h : row ∈ packetRows a b c e) : SatRow v row := by
  have P := six _ _ _ _ (S a b c e hab hbc hce)
  obtain ⟨hpq,hqr,hpr,hnpq,hnqr,hnpr⟩ := P
  simp only [packetRows,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl
  · exact imp3 (sign a b c) (sign b c e) (sign a b e) hpq
  · exact imp3 (sign a b e) (sign b c e) (sign a c e) hqr
  · exact imp3 (sign a b c) (sign a c e) (sign a b e) hpr
  · exact imp3 (sign a b c false) (sign b c e false) (sign a b e false) hnpq
  · exact imp3 (sign a b e false) (sign b c e false) (sign a c e false) hnqr
  · exact imp3 (sign a b c false) (sign a c e false) (sign a b e false) hnpr

/-- Remaining generated-row membership proof, isolated from all local
meaning and signed arithmetic. It is not asserted in this draft. -/
def GoodRows (n K A B : Nat) : Prop :=
  ∀ row ∈ typedRows n K A B, Rule K A B row ∨
    ∃ a b c e : Fin n, a<b ∧ b<c ∧ c<e ∧ row ∈ packetRows a b c e

theorem typed_of_guarded {n K A B : Nat} {v : Key n → Bool}
    (good : GoodRows n K A B)
    (S : signotope n (signVal v))
    (P : PrunedPropagation (signVal v) A B (Mapped v))
    (X : PrunedExclusions K A B (Mapped v)) :
    Satisfies v (typedRows n K A B) := by
  intro row hr
  rcases good row hr with r|⟨a,b,c,e,h₁,h₂,h₃,hm⟩
  · exact rule_sat P X r
  · exact packet_sat S h₁ h₂ h₃ hm

theorem numbered_of_guarded {n K A B : Nat} {v : Key n → Bool}
    (coverage : covered n K A B) (good : GoodRows n K A B)
    (S : signotope n (signVal v))
    (P : PrunedPropagation (signVal v) A B (Mapped v))
    (X : PrunedExclusions K A B (Mapped v)) :
    ∃ a, NumberedSatisfies a
      (compile (dictionary n A B) (typedRows n K A B) coverage) :=
  (compile_equisat _ _ coverage).mpr ⟨v,typed_of_guarded good S P X⟩

#print axioms rule_sat
#print axioms packet_sat
#print axioms numbered_of_guarded

end ES33.EndpointConcrete
