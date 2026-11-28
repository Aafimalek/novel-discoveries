/- Static coverage scaffolding. This file gives sufficient key-membership
conditions and the span changes needed by the concrete rows; the final
covered theorem is not asserted here. -/
import ActualGoodRows

namespace ES33.EndpointConcrete

open ES33.EndpointGuard
open ES33.Numbering

theorem pairs_contains {n : Nat} {a c : Fin n} (h : a<c) :
    (a,c) ∈ pairs n := by
  unfold pairs
  exact List.mem_flatMap.mpr ⟨a,List.mem_finRange a,
    List.mem_map.mpr ⟨c,List.mem_filter.mpr ⟨List.mem_finRange c,decide_eq_true h⟩,rfl⟩⟩

theorem triples_contains {n : Nat} {a b c : Fin n} (hab : a<b) (hbc : b<c) :
    (a,b,c) ∈ triples n := by
  unfold triples
  exact List.mem_flatMap.mpr ⟨(a,b),pairs_contains hab,
    List.mem_map.mpr ⟨c,List.mem_filter.mpr ⟨List.mem_finRange c,decide_eq_true hbc⟩,rfl⟩⟩

theorem sign_key_present {n A B : Nat} {a b c : Fin n} (hab : a<b) (hbc : b<c) :
    EndpointVar.sign a b c ∈ dictionary n A B := by
  simp only [dictionary,List.mem_append,or_assoc]
  exact Or.inl (List.mem_map.mpr ⟨(a,b,c),triples_contains hab hbc,rfl⟩)

theorem pair_key_present {n A B : Nat} (side : Side) {d : Nat} {a c : Fin n}
    (hac : a<c) (lo : 2≤d) (lim : d≤sideLimit side A B) (span : d≤width2 a c) :
    pairKey side d a c ∈ dictionary n A B := by
  have H : pairKey side d a c ∈ sideDictionary n (sideLimit side A B) side := by
    unfold sideDictionary
    apply List.mem_append.mpr
    exact Or.inl (List.mem_flatMap.mpr ⟨(a,c),pairs_contains hac,
      List.mem_map.mpr ⟨d,mem_inclusive_iff.mpr ⟨lo,Nat.le_min.mpr ⟨lim,span⟩⟩,rfl⟩⟩)
  simp only [dictionary,List.mem_append,or_assoc]
  cases side
  · exact Or.inr (Or.inl H)
  · exact Or.inr (Or.inr H)

theorem triple_state_key_present {n A B : Nat} (side : Side) {d : Nat} {a b c : Fin n}
    (hab : a<b) (hbc : b<c) (lo : 4≤d) (lim : d≤sideLimit side A B)
    (span : d≤width3 side a b c) :
    stateKey side d a b c ∈ dictionary n A B := by
  have H : stateKey side d a b c ∈ sideDictionary n (sideLimit side A B) side := by
    unfold sideDictionary
    apply List.mem_append.mpr
    exact Or.inr (List.mem_flatMap.mpr ⟨(a,b,c),triples_contains hab hbc,
      List.mem_map.mpr ⟨d,mem_inclusive_iff.mpr ⟨lo,Nat.le_min.mpr ⟨lim,span⟩⟩,rfl⟩⟩)
  simp only [dictionary,List.mem_append,or_assoc]
  cases side
  · exact Or.inr (Or.inl H)
  · exact Or.inr (Or.inr H)

/-- A length-three state uses the sign dictionary, higher lengths use the
corresponding triple-state dictionary. Literal polarity does not change it. -/
theorem state_literal_present {n A B : Nat} (side : Side) {d : Nat} {a b c : Fin n}
    (hab : a<b) (hbc : b<c) (lo : 3≤d) (lim : d≤sideLimit side A B)
    (span : d≤width3 side a b c) :
    (stateLit side d a b c).var ∈ dictionary n A B := by
  by_cases h : d=3
  · simpa only [stateLit,ite_eq_left h,sign] using
      (sign_key_present (A:=A) (B:=B) hab hbc)
  · simpa only [stateLit,ite_eq_right h] using
      (triple_state_key_present side hab hbc (by omega) lim span)

theorem width2_pair_base {n : Nat} {a c : Fin n} (h : a<c) : 2≤width2 a c := by
  have H : a.val<c.val := h
  unfold width2
  omega

theorem width2_project {n : Nat} (side : Side) {a b c : Fin n}
    (hab : a<b) (hbc : b<c) : width3 side a b c≤width2 a c := by
  have Ha : a.val<b.val := hab
  have Hb : b.val<c.val := hbc
  cases side <;> simp only [width2,width3] <;> omega

theorem cap_extension_width {n : Nat} {a b c e : Fin n} (hab : a<b) (hbc : b<c) :
    width3 .cap a b c+1≤width3 .cap a c e := by
  have Ha : a.val<b.val := hab
  have Hb : b.val<c.val := hbc
  simp only [width3]
  omega

theorem cup_extension_width {n : Nat} {e a b c : Fin n} (hab : a<b) (hbc : b<c) :
    width3 .cup a b c+1≤width3 .cup e a c := by
  have Ha : a.val<b.val := hab
  have Hb : b.val<c.val := hbc
  simp only [width3]
  omega

#print axioms state_literal_present
#print axioms width2_project
#print axioms cap_extension_width
#print axioms cup_extension_width

end ES33.EndpointConcrete
