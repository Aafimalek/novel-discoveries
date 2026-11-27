import EulerMinTwoCandidateRectangle
import EulerAllUsedGeometryPinLink

namespace LatinGap.PairEncoding
open EulerAllUsedDiagrams

/-- The all-used geometric reduction also satisfies the exact additional
minimum-two rectangle propagation block in the same numbered valuation. -/
theorem allUsed_geometry_with_rectangle {D : Design 6} (lin : Linear D)
    (sat : Saturated D) (size : D.card=17)
    (min : ∀ x : Label 6, 2 ≤ freq D x)
    (allused : ∀ (i j : Coord) (a b : Fin 6), i ≠ j →
      freq D (i,a)=2 → freq D (j,b)=2 → Used D (i,a) (j,b)) :
    ∃ (G : Design 6) (W : Coord → Word 6) (v : ℕ → Bool),
      Linear G ∧ Saturated G ∧ G.card=17 ∧ actualRowCodes W ∈ published ∧
      AllUsedPinCommon G W v ∧
      ∀ c ∈ archiveMinTwoCandidateRectangleBlock, NumberedHolds v c := by
  obtain ⟨G,W,v,hG,hs,hc,hpub,hv⟩ := allUsed_geometry_pin_link lin sat size min allused
  exact ⟨G,W,v,hG,hs,hc,hpub,hv,
    geometry_satisfies_archiveMinTwoCandidateRectangleBlock hG hs v
      (fun p => hv.core (.pair p)) hv.degrees⟩

#print axioms allUsed_geometry_with_rectangle
end LatinGap.PairEncoding
