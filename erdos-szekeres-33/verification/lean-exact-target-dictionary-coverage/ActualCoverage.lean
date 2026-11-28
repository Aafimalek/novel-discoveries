/- Static draft. No compiler has been run on this module. -/
import CoverageInequalities

namespace ES33.EndpointConcrete

open ES33.EndpointGuard ES33.Numbering
open VerificationGoals

private abbrev InDictionary {n : Nat} (A B : Nat) (l : Cell n) : Prop :=
  l.var ∈ dictionary n A B

private theorem one {n : Nat} {A B : Nat} {x : Cell n}
    (hx : InDictionary A B x) : ∀ l ∈ [x], InDictionary A B l := by
  intro l hl
  have e : l=x := List.mem_singleton.mp hl
  subst l
  exact hx

private theorem two {n : Nat} {A B : Nat} {x y : Cell n}
    (hx : InDictionary A B x) (hy : InDictionary A B y) :
    ∀ l ∈ [x,y], InDictionary A B l := by
  intro l hl
  rcases List.mem_cons.mp hl with e | hm
  · subst l
    exact hx
  · exact one hy l hm

private theorem three {n : Nat} {A B : Nat} {x y z : Cell n}
    (hx : InDictionary A B x) (hy : InDictionary A B y) (hz : InDictionary A B z) :
    ∀ l ∈ [x,y,z], InDictionary A B l := by
  intro l hl
  rcases List.mem_cons.mp hl with e | hm
  · subst l
    exact hx
  · exact two hy hz l hm

private theorem in_flip {n : Nat} {A B : Nat} {l : Cell n}
    (h : InDictionary A B l) : InDictionary A B (flip l) := h

private theorem in_sign {n A B : Nat} {a b c : Fin n}
    (hab : a<b) (hbc : b<c) {p : Bool} :
    InDictionary A B (sign a b c p) := sign_key_present hab hbc

private theorem in_pair {n A B : Nat} (side : Side) {d : Nat} {a c : Fin n}
    (hac : a<c) (lo : 2≤d) (lim : d≤sideLimit side A B) (span : d≤width2 a c) :
    InDictionary A B (pairLit side d a c) := pair_key_present side hac lo lim span

private theorem rule_coverage {n K A B : Nat} (hA : 2≤A) (hB : 2≤B)
    {row : List (Cell n)} (h : Rule K A B row) :
    ∀ l ∈ row, InDictionary A B l := by
  cases h with
  | capTwo a c h =>
    exact one (in_pair .cap h (Nat.le_refl _) hA (width2_pair_base h))
  | cupTwo a c h =>
    exact one (in_pair .cup h (Nat.le_refl _) hB (width2_pair_base h))
  | capThreshold a c h =>
    obtain ⟨hac,hlo,hspan⟩ := h
    exact one (in_flip (in_pair .cap hac hlo (Nat.le_refl _) hspan))
  | cupThreshold a c h =>
    obtain ⟨hac,hlo,hspan⟩ := h
    exact one (in_flip (in_pair .cup hac hlo (Nat.le_refl _) hspan))
  | capShorten d a c lo h hb =>
    obtain ⟨hac,hlo,hspan⟩ := h
    have hn : d≤d+1 := Nat.le_succ d
    exact two (in_flip (in_pair .cap hac hlo hb hspan))
      (in_pair .cap hac lo (Nat.le_trans hn hb) (Nat.le_trans hn hspan))
  | cupShorten d a c lo h hb =>
    obtain ⟨hac,hlo,hspan⟩ := h
    have hn : d≤d+1 := Nat.le_succ d
    exact two (in_flip (in_pair .cup hac hlo hb hspan))
      (in_pair .cup hac lo (Nat.le_trans hn hb) (Nat.le_trans hn hspan))
  | capProject d a b c h hb =>
    obtain ⟨hab,hbc,hlo,hspan⟩ := h
    exact two (in_flip (state_literal_present .cap hab hbc hlo hb hspan))
      (in_pair .cap (Fin.lt_trans hab hbc) (by omega) hb
        (Nat.le_trans hspan (width2_project .cap hab hbc)))
  | cupProject d a b c h hb =>
    obtain ⟨hab,hbc,hlo,hspan⟩ := h
    exact two (in_flip (state_literal_present .cup hab hbc hlo hb hspan))
      (in_pair .cup (Fin.lt_trans hab hbc) (by omega) hb
        (Nat.le_trans hspan (width2_project .cup hab hbc)))
  | capExtend d a b c e h hb he =>
    obtain ⟨hab,hbc,hlo,hspan⟩ := h
    have hd : d≤A := Nat.le_trans (Nat.le_succ d) hb
    have hnext : d+1 ≤ width3 .cap a c e :=
      Nat.le_trans (Nat.add_le_add_right hspan 1) (cap_extension_width hab hbc)
    exact three (in_flip (state_literal_present .cap hab hbc hlo hd hspan)) (in_sign hbc he)
      (state_literal_present .cap (Fin.lt_trans hab hbc) he (by omega) hb hnext)
  | cupExtend d e a b c h hb he =>
    obtain ⟨hab,hbc,hlo,hspan⟩ := h
    have hd : d≤B := Nat.le_trans (Nat.le_succ d) hb
    have hnext : d+1 ≤ width3 .cup e a c :=
      Nat.le_trans (Nat.add_le_add_right hspan 1) (cup_extension_width hab hbc)
    exact three (in_flip (state_literal_present .cup hab hbc hlo hd hspan)) (in_sign he hab)
      (state_literal_present .cup he (Fin.lt_trans hab hbc) (by omega) hb hnext)
  | opposite s t a c hs ht ha hb _ =>
    obtain ⟨hac,hsl,hss⟩ := hs
    obtain ⟨_,htl,hts⟩ := ht
    exact two (in_flip (in_pair .cap hac hsl ha hss))
      (in_flip (in_pair .cup hac htl hb hts))

private theorem packet_coverage {n A B : Nat} {a b c e : Fin n}
    (hab : a<b) (hbc : b<c) (hce : c<e) {row : List (Cell n)}
    (hr : row ∈ packetRows a b c e) : ∀ l ∈ row, InDictionary A B l := by
  have hp : InDictionary A B (sign a b c) := in_sign hab hbc
  have hq : InDictionary A B (sign a b e) := in_sign hab (Fin.lt_trans hbc hce)
  have hr' : InDictionary A B (sign a c e) := in_sign (Fin.lt_trans hab hbc) hce
  have hs : InDictionary A B (sign b c e) := in_sign hbc hce
  simp only [packetRows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact three (in_flip hp) (in_flip hs) hq
  · exact three (in_flip hq) (in_flip hs) hr'
  · exact three (in_flip hp) (in_flip hr') hq
  · exact three hp hs (in_flip hq)
  · exact three hq hs (in_flip hr')
  · exact three hp hr' (in_flip hq)

/-- Every variable in the actual typed rows occurs in the actual dictionary.
No additional hypotheses beyond the two documented size limits are needed. -/
theorem actual_covered (n K A B : Nat) (hA : 2≤A) (hB : 2≤B) :
    covered n K A B := by
  intro row hr
  rcases actual_goodRows n K A B hA hB row hr with h | ⟨a,b,c,e,hab,hbc,hce,hm⟩
  · exact rule_coverage hA hB h
  · exact packet_coverage hab hbc hce hm

theorem target32_covered : covered 32 7 7 6 :=
  actual_covered 32 7 7 6 (by decide) (by decide)

/-- The actual typed generator and numbering now have no structural meta-premises.
Semantic assumptions about the chosen orientation/auxiliary valuation remain. -/
theorem target32_numbered_of_guarded {v : Key 32 → Bool}
    (S : signotope 32 (signVal v))
    (P : PrunedPropagation (signVal v) 7 6 (Mapped v))
    (X : PrunedExclusions 7 7 6 (Mapped v)) :
    ∃ a, NumberedSatisfies a
      (compile (dictionary 32 7 6) (typedRows 32 7 7 6) target32_covered) :=
  numbered_of_guarded target32_covered target32_goodRows S P X

#print axioms actual_covered
#print axioms target32_covered
#print axioms target32_numbered_of_guarded

end ES33.EndpointConcrete
