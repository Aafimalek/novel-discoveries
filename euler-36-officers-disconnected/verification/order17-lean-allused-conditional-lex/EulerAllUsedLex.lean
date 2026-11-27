import EulerAllUsedNonLex

namespace LatinGap.PairEncoding

/-- Bool membership in the shared row prefix is read in Python product
order (most significant bit first). -/
def lexPrefixBit (k : Fin 6) (bits b : Nat) : Bool :=
  bits.testBit (k.val-1-b)

def degreePairNumber (g : Coord) (a b : Fin 6) : Nat :=
  pairNumber (degreeNeighborPair g a b)

def lexMatchPrefix (g : Coord) (a k : Fin 6) (bits : Nat) : List ℤ :=
  (List.range k.val).attach.map fun ⟨b,hb⟩ =>
    let h := List.mem_range.mp hb
    literal (degreePairNumber g a ⟨b,by omega⟩) (!(lexPrefixBit k bits b))

def archiveMinTwoLexClause (g : Coord) (a b k : Fin 6) (bits : ℕ) (d : Fin 7) :
    List ℤ :=
  [literal (degreeThresholdNumber g a d) false] ++
  (if hd : d.val < 6 then [literal (degreeThresholdNumber g b ⟨d.val+1,by omega⟩) true] else []) ++
  lexMatchPrefix g a k bits ++ lexMatchPrefix g b k bits ++
  [literal (degreePairNumber g a k) false, literal (degreePairNumber g b k) true]

def archiveLexLabelPairs (codes : List ℕ) (g : Coord) : List (Fin 6 × Fin 6) :=
  let start := archivePinnedPrefix codes g
  ((List.range (5-start)).attach.map fun ⟨r,hr⟩ =>
    have h : r < 5-start := List.mem_range.mp hr
    (⟨start+r,by omega⟩,⟨start+r+1,by omega⟩))

def archiveMinTwoLexRow (g : Coord) (a b : Fin 6) : List (List Int) :=
  (List.ofFn fun k : Fin 6 => k).flatMap fun k =>
    (List.range (2^k.val)).flatMap fun bits =>
      (thresholdIndices 2).map fun d => archiveMinTwoLexClause g a b k bits d

def archiveAllUsedLex (codes : List ℕ) : List (List ℤ) :=
  (List.ofFn fun g : Coord => g).flatMap fun g =>
    (archiveLexLabelPairs codes g).flatMap fun (a,b) => archiveMinTwoLexRow g a b

/-- The left incidence row is no larger than the right in Boolean order.
This formulation matches each possible first difference directly. -/
def ArchivedIncidenceLE (v : ℕ → Bool) (g : Coord) (a b : Fin 6) : Prop :=
  ∀ k : Fin 6,
    (∀ t : Fin 6, t < k → v (degreePairNumber g a t) = v (degreePairNumber g b t)) →
    v (degreePairNumber g a k) = true → v (degreePairNumber g b k) = true

theorem mem_lexMatchPrefix (g : Coord) (a k : Fin 6) (bits : ℕ)
    (t : Fin 6) (ht : t<k) :
    literal (degreePairNumber g a t) (!(lexPrefixBit k bits t.val)) ∈ lexMatchPrefix g a k bits := by
  let x : {z // z ∈ List.range k.val} := ⟨t.val,List.mem_range.mpr ht⟩
  exact List.mem_map.mpr ⟨x, by simp, rfl⟩

theorem archiveMinTwoLexClause_holds (v : ℕ → Bool) (g : Coord) (a b k : Fin 6)
    (bits : ℕ) (d : Fin 7) (horder : ArchivedIncidenceLE v g a b) :
    NumberedHolds v (archiveMinTwoLexClause g a b k bits d) := by
  classical
  by_contra h
  have pos (x y : Fin 6) : 0 < degreePairNumber g x y := by
    have := (pairNumber_bounds (degreeNeighborPair g x y)).1
    unfold degreePairNumber
    omega
  have agree (x t : Fin 6)
      (hm : literal (degreePairNumber g x t) (!(lexPrefixBit k bits t.val)) ∈
        archiveMinTwoLexClause g a b k bits d) :
      v (degreePairNumber g x t) = lexPrefixBit k bits t.val := by
    by_contra! e
    have flip (c e : Bool) (hn : c≠e) : c = !e := by cases c <;> cases e <;> simp_all
    exact h (holds_literal_of_mem hm (pos x t) (flip _ _ e))
  have earlier (t : Fin 6) (ht : t<k) :
      v (degreePairNumber g a t) = v (degreePairNumber g b t) := by
    have ha := mem_lexMatchPrefix g a k bits t ht
    have hb := mem_lexMatchPrefix g b k bits t ht
    refine (agree a t ?_).trans (agree b t ?_).symm
    · simp only [archiveMinTwoLexClause,List.mem_append]
      tauto
    · simp only [archiveMinTwoLexClause,List.mem_append]
      tauto
  have la : v (degreePairNumber g a k) = true := by
    cases eq : v (degreePairNumber g a k)
    · exact (h (holds_literal_of_mem (id := degreePairNumber g a k) (b := false)
        (by simp [archiveMinTwoLexClause]) (pos a k) eq)).elim
    · rfl
  have lb := horder k earlier la
  exact h (holds_literal_of_mem (id := degreePairNumber g b k) (b := true)
    (by simp [archiveMinTwoLexClause]) (pos b k) lb)

/-- Conditional soundness of the exact free-label lex suffix. Geometric
existence of a relabeling satisfying all these incidence inequalities
is a separate normalization theorem. -/
theorem archiveAllUsedLex_holds (codes : List ℕ) (v : ℕ → Bool)
    (horder : ∀ (g : Coord) (a b : Fin 6),
      (a,b) ∈ archiveLexLabelPairs codes g → ArchivedIncidenceLE v g a b) :
    ∀ c ∈ archiveAllUsedLex codes, NumberedHolds v c := by
  intro c hc
  obtain ⟨g,_,hg⟩ := List.mem_flatMap.mp hc
  obtain ⟨⟨a,b⟩,hab,habc⟩ := List.mem_flatMap.mp hg
  obtain ⟨k,_,hk⟩ := List.mem_flatMap.mp habc
  obtain ⟨bits,_,hbits⟩ := List.mem_flatMap.mp hk
  obtain ⟨d,_,rfl⟩ := List.mem_map.mp hbits
  exact archiveMinTwoLexClause_holds v g a b k bits d (horder g a b hab)

#print axioms archiveMinTwoLexClause_holds
#print axioms archiveAllUsedLex_holds
end LatinGap.PairEncoding
