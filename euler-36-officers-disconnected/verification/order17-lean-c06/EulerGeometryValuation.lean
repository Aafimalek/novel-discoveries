import EulerRectangleCut

namespace LatinGap.PairEncoding

/-- Core bit numbers never overlap the degree block. -/
theorem varNumber_le_1512 (x : Var 6) : varNumber x ≤ 1512 := by
  cases x with
  | word w =>
      have h := (wordNumber_bounds w).2
      change wordNumber w ≤ 1512
      omega
  | pair p => exact (pairNumber_bounds p).2

/-- The common word/pair/degree valuation, prior to adding the independent
sequential-counter states and case-specific auxiliary bits. -/
noncomputable def designNumeric (D : Design 6) (i : ℕ) : Bool := by
  classical
  exact decide
    ((∃ x : Var 6, varNumber x = i ∧ (encode D).eval x = true) ∨
     (∃ (g : Coord) (a : Fin 6) (d : Fin 7),
       degreeThresholdNumber g a d = i ∧ d.val ≤ freq D (g,a)))

theorem designNumeric_core (D : Design 6) (x : Var 6) :
    designNumeric D (varNumber x) = (encode D).eval x := by
  have he : ((∃ y : Var 6, varNumber y = varNumber x ∧ (encode D).eval y = true) ∨
      (∃ (g : Coord) (a : Fin 6) (d : Fin 7), degreeThresholdNumber g a d = varNumber x ∧
        d.val ≤ freq D (g,a))) ↔ (encode D).eval x = true := by
    constructor
    · rintro (⟨y,hy,hv⟩ | ⟨g,a,d,hd,_⟩)
      · exact (varNumber_injective hy) ▸ hv
      · have hu := varNumber_le_1512 x
        have hl := (degreeThresholdNumber_bounds g a d).1
        omega
    · intro hx
      exact Or.inl ⟨x,rfl,hx⟩
  apply Bool.eq_iff_iff.mpr
  simpa [designNumeric] using he

theorem designNumeric_lifts (D : Design 6) : liftNumbers (designNumeric D) = encode D := by
  have hw : (liftNumbers (designNumeric D)).select = (encode D).select := by
    funext w
    exact designNumeric_core D (.word w)
  have hp : (liftNumbers (designNumeric D)).pair = (encode D).pair := by
    funext p
    exact designNumeric_core D (.pair p)
  cases h : liftNumbers (designNumeric D)
  cases h2 : encode D
  simp only [h,h2] at hw hp
  congr

theorem designNumeric_degree (D : Design 6) (g : Coord) (a : Fin 6) (d : Fin 7) :
    designNumeric D (degreeThresholdNumber g a d) = decide (d.val ≤ freq D (g,a)) := by
  have he : ((∃ x : Var 6, varNumber x = degreeThresholdNumber g a d ∧ (encode D).eval x = true) ∨
      (∃ (h : Coord) (b : Fin 6) (e : Fin 7), degreeThresholdNumber h b e = degreeThresholdNumber g a d ∧
        e.val ≤ freq D (h,b))) ↔ d.val ≤ freq D (g,a) := by
    constructor
    · rintro (⟨x,hx,_⟩ | ⟨h,b,e,hd,hv⟩)
      · have hu := varNumber_le_1512 x
        have hl := (degreeThresholdNumber_bounds g a d).1
        omega
      · obtain ⟨rfl,rfl,rfl⟩ := degreeThresholdNumber_injective h g b a e d hd
        exact hv
    · intro hx
      exact Or.inr ⟨g,a,d,rfl,hx⟩
  apply Bool.eq_iff_iff.mpr
  simpa [designNumeric] using he

theorem designNumeric_degreeBlocks {D : Design 6} (hD : Linear D)
    (minimum : ℕ) (hmin : ∀ x : Label 6, minimum ≤ freq D x)
    (hzero : freq D (0,0) = minimum)
    (g : Coord) (a : Fin 6) (C : List Int) (hc : C ∈ degreeBlock minimum g a) :
    NumberedHolds (designNumeric D) C := by
  apply degreeBlock_holds _ minimum g a (freq D (g,a)) ?_ (designNumeric_degree D g a) ?_ C hc
  · convert patternCount_eq_freq hD g a using 2
    funext b
    exact designNumeric_core D (.pair (degreeNeighborPair g a b))
  · refine ⟨hmin (g,a),?_⟩
    rintro ⟨rfl,rfl⟩
    exact hzero

theorem designNumeric_rectangles {D : Design 6} (hD : Linear D) (hM : Saturated D)
    (m : ℕ) (hmin : ∀ z : Label 6, m ≤ freq D z) (p : PairKey 6) (da db : Fin 6)
    (hr : 0 < 6-da.val-db.val)
    (hs : D.card < (6-da.val-db.val)^2 + (6-(6-da.val-db.val))*m) :
    NumberedHolds (designNumeric D) (rectangleCut p da db) :=
  rectangleCut_holds hD hM m hmin p da db (designNumeric D) (designNumeric_core D (.pair p))
    (designNumeric_degree D p.i p.a da.succ) (designNumeric_degree D p.j p.b db.succ) hr hs

#print axioms designNumeric_core
#print axioms designNumeric_lifts
#print axioms designNumeric_degree
#print axioms designNumeric_degreeBlocks
#print axioms designNumeric_rectangles

end LatinGap.PairEncoding
