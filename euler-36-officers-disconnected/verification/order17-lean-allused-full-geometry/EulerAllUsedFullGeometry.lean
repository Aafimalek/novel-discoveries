import EulerLexGeometry

namespace LatinGap.PairEncoding
open EulerAllUsedDiagrams

def archiveAllUsedCNF (codes : List ℕ) : List (List ℤ) :=
  archiveAllUsedNonLex codes ++ archiveAllUsedLex codes

private theorem wordUnit_present {D : Design 6} {v : ℕ → Bool}
    {W : Coord → Word 6} {w : Word 6} (hv : AllUsedPinCommon D W v)
    (h : NumberedHolds v (wordUnit w)) : w ∈ D := by
  obtain ⟨l,hm,_,he⟩ := h
  simp only [wordUnit,List.mem_singleton] at hm
  subst l
  obtain ⟨_,hn,hbit⟩ := literal_spec (id := wordNumber w) (wordNumber_bounds w).1 true
  rw [hn,hbit,show v (wordNumber w) = (encode D).select w from hv.core (.word w)] at he
  exact (select_encode D w).mp he

/-- Every actual all-used size-17 design gives a numbered valuation of
one entire modeled original archived CNF. This is a geometry reduction,
not an UNSAT proof. Byte agreement of model and originals is a separate
external audit. -/
theorem allUsed_geometry_full_archive {D : Design 6} (lin : Linear D) (sat : Saturated D)
    (size : D.card=17) (min : ∀ x : Label 6, 2 ≤ freq D x)
    (allused : ∀ (i j : Coord) (a b : Fin 6), i ≠ j →
      freq D (i,a)=2 → freq D (j,b)=2 → Used D (i,a) (j,b)) :
    ∃ codes ∈ published, ∃ v : ℕ → Bool, ∀ c ∈ archiveAllUsedCNF codes, NumberedHolds v c := by
  obtain ⟨G,W,v,hG,hsG,hcG,pub,prof,hv,_⟩ := allUsed_geometry_nonLex lin sat size min allused
  have zeroG : (fun _ => 0) ∈ G := by
    apply wordUnit_present hv
    have w0 : decimalWord 0 = (fun _ => 0) := by funext j; fin_cases j <;> decide
    exact hv.anchors _ (by simp [archiveAllUsedAnchorUnits,wordUnit,w0])
  have pins (i : Coord) : W i ∈ G := by
    apply wordUnit_present hv
    have c : decimalCode (W i) ∈ actualRowCodes W :=
      actualRowCodes_eq W ▸ List.mem_ofFn.mpr ⟨i,rfl⟩
    apply hv.pins
    apply List.mem_append.mpr
    left
    exact List.mem_map.mpr ⟨_,c,by simp [wordUnit]⟩
  obtain ⟨H,hH,hsH,hcH,zeroH,profH,pinsH,order⟩ :=
    normalize_geometry_allUsed_lex hG hsG zeroG prof W pins
  obtain ⟨v',hv'⟩ := actual_allUsed_pin_common hH hsH (hcH.trans hcG) zeroH profH W pinsH pub
  refine ⟨_,pub,v',?_⟩
  intro c hc
  rcases List.mem_append.mp hc with hn | hl
  · exact actual_allUsed_nonLex_holds hH hsH v' W hv' profH c hn
  · apply archiveAllUsedLex_holds _ v' ?_ c hl
    intro g a b lab
    have e (x y : Fin 6) : v' (degreePairNumber g x y) = geometricIncidence H g x y :=
      hv'.core (.pair (degreeNeighborPair g x y))
    unfold ArchivedIncidenceLE
    simp_rw [e]
    exact order g a b lab

#print axioms allUsed_geometry_full_archive
end LatinGap.PairEncoding
