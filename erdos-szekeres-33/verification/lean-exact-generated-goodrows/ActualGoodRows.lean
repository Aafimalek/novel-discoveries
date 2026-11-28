/- Constructor exhaustiveness for the actual EndpointConcreteSpec generator. -/
import LiteralFamilies

namespace ES33.EndpointConcrete

open ES33.EndpointGuard
open ES33.Numbering

theorem mem_inclusive_iff {lo hi d : Nat} :
    d ∈ inclusive lo hi ↔ lo ≤ d ∧ d ≤ hi := by
  unfold inclusive
  constructor
  · intro hm
    obtain ⟨i,hi',rfl⟩ := List.mem_map.mp hm
    have hi'' := List.mem_range.mp hi'
    omega
  · rintro ⟨hlo,hhi⟩
    exact List.mem_map.mpr ⟨d-lo,List.mem_range.mpr (by omega),by omega⟩

theorem pair_order {n : Nat} {t : Fin n × Fin n} (hm : t ∈ pairs n) :
    t.1<t.2 := by
  unfold pairs at hm
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hm
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  exact of_decide_eq_true (List.mem_filter.mp hj).2

theorem triple_order {n : Nat} {t : Fin n × Fin n × Fin n}
    (hm : t ∈ triples n) : t.1<t.2.1 ∧ t.2.1<t.2.2 := by
  unfold triples at hm
  obtain ⟨⟨i,j⟩,hij,hi⟩ := List.mem_flatMap.mp hm
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hi
  exact ⟨pair_order hij,of_decide_eq_true (List.mem_filter.mp hk).2⟩

theorem packet_order {n : Nat} {t : Fin n × Fin n × Fin n × Fin n}
    (hm : t ∈ packets n) : t.1<t.2.1 ∧ t.2.1<t.2.2.1 ∧
      t.2.2.1<t.2.2.2 := by
  unfold packets at hm
  obtain ⟨⟨a,b,c⟩,habc,hi⟩ := List.mem_flatMap.mp hm
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hi
  exact ⟨(triple_order habc).1,(triple_order habc).2,
    of_decide_eq_true (List.mem_filter.mp he).2⟩

def sideLimit (side : Side) (A B : Nat) : Nat :=
  match side with
  | .cap => A
  | .cup => B

private theorem pair_rule {n K A B : Nat} (side : Side)
    (hA : 2≤A) (hB : 2≤B) {a c : Fin n} (hac : a<c)
    {row : List (Cell n)} (hr : row ∈ pairRows side (sideLimit side A B) a c) :
    Rule K A B row := by
  let L := sideLimit side A B
  have hL : 2≤L := by
    dsimp [L]
    cases side
    · exact hA
    · exact hB
  change row ∈ pairRows side L a c at hr
  simp only [pairRows,List.mem_append,List.mem_singleton,or_assoc] at hr
  rcases hr with e | h | h
  · subst row
    cases side
    · exact Rule.capTwo a c hac
    · exact Rule.cupTwo a c hac
  · by_cases hLw : L≤width2 a c
    · have e : row=[flip (pairLit side L a c)] := by
        simpa only [ite_eq_left hLw,List.mem_singleton] using h
      have hf : PairFits L a c := ⟨hac,hL,hLw⟩
      subst row
      cases side
      · exact Rule.capThreshold a c hf
      · exact Rule.cupThreshold a c hf
    · simp only [ite_eq_right hLw,List.not_mem_nil] at h
  · obtain ⟨l,hl,rfl⟩ := List.mem_map.mp h
    have rr := mem_inclusive_iff.mp hl
    have e : l-1+1=l := by omega
    have hf : PairFits (l-1+1) a c := by
      rw [e]
      exact ⟨hac,by omega,Nat.le_trans rr.2 (Nat.min_le_right _ _)⟩
    have hlim : l-1+1≤L := by rw [e]; exact Nat.le_trans rr.2 (Nat.min_le_left _ _)
    have hsmall : 2≤l-1 := by omega
    cases side
    · simpa only [e] using (Rule.capShorten (K:=K) (A:=A) (B:=B)
        (l-1) a c hsmall hf hlim)
    · simpa only [e] using (Rule.cupShorten (K:=K) (A:=A) (B:=B)
        (l-1) a c hsmall hf hlim)

private theorem triple_rule {n K A B : Nat} (side : Side)
    {a b c : Fin n} (hab : a<b) (hbc : b<c)
    {row : List (Cell n)} (hr : row ∈ tripleRows side (sideLimit side A B) a b c) :
    Rule K A B row := by
  let L := sideLimit side A B
  change row ∈ tripleRows side L a b c at hr
  unfold tripleRows at hr
  obtain ⟨d,hd,hr⟩ := List.mem_flatMap.mp hr
  have rr := mem_inclusive_iff.mp hd
  have hL : d≤L := Nat.le_trans rr.2 (Nat.min_le_left _ _)
  have hW : d≤width3 side a b c := Nat.le_trans rr.2 (Nat.min_le_right _ _)
  rcases List.mem_append.mp hr with h | h
  · have e : row=[flip (stateLit side d a b c),pairLit side d a c] :=
      List.mem_singleton.mp h
    subst row
    cases side
    · exact Rule.capProject d a b c ⟨hab,hbc,rr.1,hW⟩ hL
    · exact Rule.cupProject d a b c ⟨hab,hbc,rr.1,hW⟩ hL
  · by_cases hs : d<L
    · have hNext : d+1≤L := hs
      have hsRow : row ∈ stepRows side d a b c := by
        simpa only [ite_eq_left hs] using h
      cases side
      · unfold stepRows at hsRow
        obtain ⟨e,he,rfl⟩ := List.mem_map.mp hsRow
        exact Rule.capExtend d a b c e ⟨hab,hbc,rr.1,hW⟩ hNext
          (of_decide_eq_true (List.mem_filter.mp he).2)
      · unfold stepRows at hsRow
        obtain ⟨e,he,rfl⟩ := List.mem_map.mp hsRow
        exact Rule.cupExtend d e a b c ⟨hab,hbc,rr.1,hW⟩ hNext
          (of_decide_eq_true (List.mem_filter.mp he).2)
    · simp only [ite_eq_right hs,List.not_mem_nil] at h

private theorem side_rule {n K A B : Nat} (side : Side)
    (hA : 2≤A) (hB : 2≤B) {row : List (Cell n)}
    (hr : row ∈ sideRows n (sideLimit side A B) side) : Rule K A B row := by
  unfold sideRows at hr
  rcases List.mem_append.mp hr with h | h
  · obtain ⟨⟨a,c⟩,hac,hr⟩ := List.mem_flatMap.mp h
    exact pair_rule side hA hB (pair_order hac) hr
  · obtain ⟨⟨a,b,c⟩,habc,hr⟩ := List.mem_flatMap.mp h
    obtain ⟨hab,hbc⟩ := triple_order habc
    exact triple_rule side hab hbc hr

private theorem cross_rule {n K A B : Nat} {row : List (Cell n)}
    (hr : row ∈ crossRows n K A B) : Rule K A B row := by
  unfold crossRows at hr
  obtain ⟨⟨a,c⟩,hac,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨s,hs,he⟩ := List.mem_filterMap.mp hr
  have src := mem_inclusive_iff.mp hs
  let t := K+2-s
  change (if s≤min A (width2 a c) ∧ 2≤t ∧ t≤min B (width2 a c) then
      some [flip (pairLit .cap s a c),flip (pairLit .cup t a c)] else none) =
      some row at he
  by_cases h : s≤min A (width2 a c) ∧ 2≤t ∧ t≤min B (width2 a c)
  · have e : [flip (pairLit .cap s a c),flip (pairLit .cup t a c)]=row := by
      simpa only [ite_eq_left h,Option.some.injEq] using he
    subst row
    exact Rule.opposite s t a c
      ⟨pair_order hac,src.1,Nat.le_trans h.1 (Nat.min_le_right _ _)⟩
      ⟨pair_order hac,h.2.1,Nat.le_trans h.2.2 (Nat.min_le_right _ _)⟩
      (Nat.le_trans h.1 (Nat.min_le_left _ _))
      (Nat.le_trans h.2.2 (Nat.min_le_left _ _)) (by dsimp [t]; omega)
  · simp [h] at he

/-- Constructor exhaustiveness for the *actual* ordered typed generator.
The two size lower bounds ensure emitted threshold guards and are both
automatic for the target (32,7,7,6). -/
theorem actual_goodRows (n K A B : Nat) (hA : 2≤A) (hB : 2≤B) :
    GoodRows n K A B := by
  intro row hr
  simp only [typedRows,List.mem_append,or_assoc] at hr
  rcases hr with hc | hu | hx | hp
  · exact Or.inl (side_rule .cap hA hB hc)
  · exact Or.inl (side_rule .cup hA hB hu)
  · exact Or.inl (cross_rule hx)
  · obtain ⟨⟨a,b,c,e⟩,horder,hm⟩ := List.mem_flatMap.mp hp
    obtain ⟨hab,hbc,hce⟩ := packet_order horder
    exact Or.inr ⟨a,b,c,e,hab,hbc,hce,hm⟩

theorem target32_goodRows : GoodRows 32 7 7 6 :=
  actual_goodRows 32 7 7 6 (by decide) (by decide)

#print axioms actual_goodRows
#print axioms target32_goodRows

end ES33.EndpointConcrete
