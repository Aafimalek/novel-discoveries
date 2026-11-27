import LatinGap
import Mathlib.Data.Fintype.Pi

/-!
# A Boolean word/pair encoding of maximal partial orthogonal Latin squares

This file checks the abstract core only. A variable for a word means that
the word is selected; a variable for a coordinate pair and its values
means that the pair is used. This does not check DIMACS numbering, the
PySAT cardinality encoders, extra geometric cuts, or DRAT certificates.
-/

namespace LatinGap.PairEncoding

open Finset

/-- Two values on an increasing pair of coordinates. This indexes one used-pair bit. -/
structure PairKey (n : ℕ) where
  i : Coord
  j : Coord
  increasing : i < j
  a : Fin n
  b : Fin n

/-- This word projects to the specified pair of values. -/
def Matches {n : ℕ} (p : PairKey n) (w : Word n) : Prop :=
  w p.i = p.a ∧ w p.j = p.b

/-- The two groups of Boolean variables in the abstract core. -/
structure Assignment (n : ℕ) where
  select : Word n → Bool
  pair : PairKey n → Bool

variable {n : ℕ}

/-- Recover the chosen words from their Boolean values. -/
def Assignment.words (A : Assignment n) : Design n :=
  univ.filter fun w => A.select w = true

@[simp] theorem mem_words {A : Assignment n} {w : Word n} :
    w ∈ A.words ↔ A.select w = true := by
  simp [Assignment.words]

/-- At most one chosen word touches a specified pair. -/
def AtMostOneSupport (A : Assignment n) : Prop :=
  ∀ p : PairKey n, ∀ u v : Word n,
    A.select u = true → A.select v = true → Matches p u → Matches p v → u = v

/-- A chosen word sets each of its six pair variables. -/
def WordImpliesPair (A : Assignment n) : Prop :=
  ∀ p : PairKey n, ∀ w : Word n,
    A.select w = true → Matches p w → A.pair p = true

/-- Every set pair variable has a chosen word supporting it. -/
def PairHasSupport (A : Assignment n) : Prop :=
  ∀ p : PairKey n, A.pair p = true → ∃ w : Word n, A.select w = true ∧ Matches p w

/-- The positive pair disjunction holds for each candidate unchanged. -/
def EveryCandidateTouched (A : Assignment n) : Prop :=
  ∀ w : Word n, ∃ p : PairKey n, A.pair p = true ∧ Matches p w

/-- The abstract Boolean constraints with exact word cardinality. -/
structure Satisfies (A : Assignment n) (k : ℕ) : Prop where
  exactCardinality : A.words.card = k
  atMostOne : AtMostOneSupport A
  wordImpliesPair : WordImpliesPair A
  pairHasSupport : PairHasSupport A
  touched : EveryCandidateTouched A

/-- The intended geometry yields both implications for a pair bit. -/
theorem pair_constraints_iff (A : Assignment n) :
    WordImpliesPair A ∧ PairHasSupport A ↔
      ∀ p : PairKey n, A.pair p = true ↔ Used A.words (p.i, p.a) (p.j, p.b) := by
  constructor
  · rintro ⟨hforward, hback⟩ p
    constructor
    · intro hp
      obtain ⟨w, hw, hm⟩ := hback p hp
      exact ⟨ne_of_lt p.increasing, w, mem_words.mpr hw, hm⟩
    · rintro ⟨_, w, hw, hm⟩
      exact hforward p w (mem_words.mp hw) hm
  · intro h
    constructor
    · intro p w hw hm
      exact (h p).mpr ⟨ne_of_lt p.increasing, w, mem_words.mpr hw, hm⟩
    · intro p hp
      obtain ⟨_, w, hw, hm⟩ := (h p).mp hp
      exact ⟨w, mem_words.mp hw, hm⟩

/-- Pair support is unique exactly when the chosen words are linear. -/
theorem atMostOne_iff_linear (A : Assignment n) :
    AtMostOneSupport A ↔ Linear A.words := by
  constructor
  · intro h u hu v hv i j hij hi hj
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · let p : PairKey n := ⟨i, j, hij', u i, u j⟩
      exact h p u v (mem_words.mp hu) (mem_words.mp hv)
        ⟨rfl, rfl⟩ ⟨hi.symm, hj.symm⟩
    · let p : PairKey n := ⟨j, i, hji', u j, u i⟩
      exact h p u v (mem_words.mp hu) (mem_words.mp hv)
        ⟨rfl, rfl⟩ ⟨hj.symm, hi.symm⟩
  · intro h p u v hu hv ⟨hui, huj⟩ ⟨hvi, hvj⟩
    exact h (mem_words.mpr hu) (mem_words.mpr hv) (ne_of_lt p.increasing)
      (hui.trans hvi.symm) (huj.trans hvj.symm)

/-- Given faithful pair bits, the candidate disjunctions express saturation. -/
theorem touched_iff_saturated (A : Assignment n)
    (hbit : ∀ p : PairKey n, A.pair p = true ↔ Used A.words (p.i, p.a) (p.j, p.b)) :
    EveryCandidateTouched A ↔ Saturated A.words := by
  constructor
  · intro h w
    obtain ⟨p, hp, hi, hj⟩ := h w
    refine ⟨p.i, p.j, ?_⟩
    rw [hi, hj]
    exact (hbit p).mp hp
  · intro h w
    obtain ⟨i, j, hij⟩ := h w
    rcases lt_or_gt_of_ne (used_coord_ne hij) with hij' | hji'
    · let p : PairKey n := ⟨i, j, hij', w i, w j⟩
      exact ⟨p, (hbit p).mpr hij, rfl, rfl⟩
    · let p : PairKey n := ⟨j, i, hji', w j, w i⟩
      exact ⟨p, (hbit p).mpr (used_symm hij), rfl, rfl⟩

/-- The abstract Boolean constraints are equivalent to the intended geometry
together with the statement that every pair variable is faithful. -/
theorem satisfies_iff_geometry (A : Assignment n) (k : ℕ) :
    Satisfies A k ↔
      Linear A.words ∧ Saturated A.words ∧ A.words.card = k ∧
      ∀ p : PairKey n, A.pair p = true ↔ Used A.words (p.i, p.a) (p.j, p.b) := by
  constructor
  · intro h
    have hb := (pair_constraints_iff A).mp ⟨h.wordImpliesPair, h.pairHasSupport⟩
    exact ⟨(atMostOne_iff_linear A).mp h.atMostOne,
      (touched_iff_saturated A hb).mp h.touched, h.exactCardinality, hb⟩
  · rintro ⟨hl, hs, hc, hb⟩
    obtain ⟨hf, hr⟩ := (pair_constraints_iff A).mpr hb
    exact ⟨hc, (atMostOne_iff_linear A).mpr hl, hf, hr,
      (touched_iff_saturated A hb).mpr hs⟩

/-- Every true pair bit has precisely one selected word supporting it. -/
theorem unique_support {A : Assignment n} {k : ℕ} (h : Satisfies A k)
    (p : PairKey n) (hp : A.pair p = true) :
    ∃! w : Word n, A.select w = true ∧ Matches p w := by
  obtain ⟨w, hw, hm⟩ := h.pairHasSupport p hp
  exact ⟨w, ⟨hw, hm⟩, fun v hv => h.atMostOne p v w hv.1 hw hv.2 hm⟩

/-- The Boolean assignment induced by an actual design. -/
noncomputable def encode (D : Design n) : Assignment n := by
  classical
  exact ⟨fun w => decide (w ∈ D), fun p => decide (Used D (p.i, p.a) (p.j, p.b))⟩

@[simp] theorem select_encode (D : Design n) (w : Word n) :
    (encode D).select w = true ↔ w ∈ D := by
  classical
  simp [encode]

@[simp] theorem pair_encode (D : Design n) (p : PairKey n) :
    (encode D).pair p = true ↔ Used D (p.i, p.a) (p.j, p.b) := by
  classical
  simp [encode]

@[simp] theorem words_encode (D : Design n) : (encode D).words = D := by
  ext w
  simp

/-- An exact-cardinality linear saturated design supplies a satisfying assignment. -/
theorem encode_satisfies {D : Design n} {k : ℕ}
    (hL : Linear D) (hS : Saturated D) (hC : D.card = k) :
    Satisfies (encode D) k := by
  apply (satisfies_iff_geometry _ _).mpr
  simpa only [words_encode, pair_encode] using
    (show Linear D ∧ Saturated D ∧ D.card = k ∧
      ∀ p : PairKey n, Used D (p.i, p.a) (p.j, p.b) ↔ Used D (p.i, p.a) (p.j, p.b)
    from ⟨hL, hS, hC, fun _ => Iff.rfl⟩)

/-- The exact order-six, size-seventeen transfer in both directions. -/
theorem exists_seventeen_iff :
    (∃ D : Design 6, Linear D ∧ Saturated D ∧ D.card = 17) ↔
      ∃ A : Assignment 6, Satisfies A 17 := by
  constructor
  · rintro ⟨D, hL, hS, hC⟩
    exact ⟨encode D, encode_satisfies hL hS hC⟩
  · rintro ⟨A, hA⟩
    obtain ⟨hL, hS, hC, _⟩ := (satisfies_iff_geometry _ _).mp hA
    exact ⟨A.words, hL, hS, hC⟩

end LatinGap.PairEncoding

#print axioms LatinGap.PairEncoding.satisfies_iff_geometry
#print axioms LatinGap.PairEncoding.exists_seventeen_iff
