import EulerPairEncoding

/-!
# Symbolic CNF clause families for the word/pair core

These are actual finite clauses over typed word and pair symbols, but the extra
exact-cardinality condition remains a finset cardinality. No solver integer
numbering, cardinality auxiliaries, branch-specific cuts, or certificate parser
is modeled here.
-/

namespace LatinGap.PairEncoding

open Finset

/-- A typed variable, before any numbering for a DIMACS file. -/
inductive Var (n : ℕ)
  | word : Word n → Var n
  | pair : PairKey n → Var n

variable {n : ℕ}

/-- A literal in which the Boolean is the required truth value. -/
abbrev Lit (n : ℕ) := Var n × Bool

/-- A finite disjunction of literals. -/
abbrev Clause (n : ℕ) := List (Lit n)

def Assignment.eval (A : Assignment n) : Var n → Bool
  | .word w => A.select w
  | .pair p => A.pair p

def Holds (A : Assignment n) (C : Clause n) : Prop :=
  ∃ l ∈ C, A.eval l.1 = l.2

@[simp] theorem holds_nil (A : Assignment n) : ¬ Holds A [] := by simp [Holds]

@[simp] theorem holds_cons (A : Assignment n) (l : Lit n) (ls : Clause n) :
    Holds A (l :: ls) ↔ A.eval l.1 = l.2 ∨ Holds A ls := by
  simp [Holds]

private theorem false_or_iff_imp (b : Bool) (P : Prop) :
    (b = false ∨ P) ↔ (b = true → P) := by cases b <;> simp

/-- One implication from a selected word to a pair it matches. -/
def wordPairClause (p : PairKey n) (w : Word n) : Clause n :=
  [(.word w, false), (.pair p, true)]

theorem wordPairClause_iff (A : Assignment n) (p : PairKey n) (w : Word n) :
    Holds A (wordPairClause p w) ↔ (A.select w = true → A.pair p = true) := by
  simpa [wordPairClause, Assignment.eval] using
    (false_or_iff_imp (A.select w) (A.pair p = true))

/-- A pairwise cardinality-one clause on two different supporting words. -/
def collisionClause (u v : Word n) : Clause n :=
  [(.word u, false), (.word v, false)]

theorem collisionClause_iff (A : Assignment n) (u v : Word n) :
    Holds A (collisionClause u v) ↔ ¬ (A.select u = true ∧ A.select v = true) := by
  cases hu : A.select u <;> cases hv : A.select v <;>
    simp [collisionClause, Assignment.eval, hu, hv]

/-- The words matching a pair, whether selected or not. -/
noncomputable def supportingWords (p : PairKey n) : Finset (Word n) := by
  classical
  exact univ.filter (Matches p)

@[simp] theorem mem_supportingWords (p : PairKey n) (w : Word n) :
    w ∈ supportingWords p ↔ Matches p w := by
  simp [supportingWords]

/-- A true pair variable implies a disjunction of every possible support. -/
noncomputable def supportClause (p : PairKey n) : Clause n :=
  (.pair p, false) :: (supportingWords p).toList.map (fun w => (.word w, true))

theorem supportClause_iff (A : Assignment n) (p : PairKey n) :
    Holds A (supportClause p) ↔
      (A.pair p = true → ∃ w : Word n, A.select w = true ∧ Matches p w) := by
  rw [supportClause, holds_cons, Assignment.eval, false_or_iff_imp]
  simp [Holds, Assignment.eval, and_comm]

/-- The six increasing coordinate pairs. -/
abbrev CoordPair := {ij : Coord × Coord // ij.1 < ij.2}

theorem coordPair_card : Fintype.card CoordPair = 6 := by decide

/-- Convert a coordinate pair and candidate word into the corresponding pair bit. -/
def candidatePair (w : Word n) (ij : CoordPair) : PairKey n :=
  ⟨ij.1.1, ij.1.2, ij.2, w ij.1.1, w ij.1.2⟩

/-- A candidate cannot be inserted if at least one of its six pairs is true. -/
noncomputable def candidateClause (w : Word n) : Clause n :=
  (univ : Finset CoordPair).toList.map (fun ij => (.pair (candidatePair w ij), true))

theorem candidateClause_length (w : Word n) : (candidateClause w).length = 6 := by
  simp [candidateClause, coordPair_card]

theorem candidateClause_iff (A : Assignment n) (w : Word n) :
    Holds A (candidateClause w) ↔
      ∃ p : PairKey n, A.pair p = true ∧ Matches p w := by
  constructor
  · intro h
    have h' : ∃ ij : CoordPair, A.pair (candidatePair w ij) = true := by
      simpa [Holds, candidateClause, Assignment.eval] using h
    obtain ⟨ij, hij⟩ := h'
    exact ⟨candidatePair w ij, hij, rfl, rfl⟩
  · rintro ⟨⟨i, j, h, a, b⟩, hp, hi, hj⟩
    have hi' : w i = a := hi
    have hj' : w j = b := hj
    subst a; subst b
    have h' : ∃ ij : CoordPair, A.pair (candidatePair w ij) = true :=
      ⟨⟨(i, j), h⟩, hp⟩
    simpa [Holds, candidateClause, Assignment.eval] using h'

/-- The relevant symbolic clause families, plus the exact count kept separate
from any particular cardinality compiler. -/
structure SatisfiesClauses (A : Assignment n) (k : ℕ) : Prop where
  exactCardinality : A.words.card = k
  collision : ∀ p : PairKey n, ∀ u v : Word n,
    Matches p u → Matches p v → u ≠ v → Holds A (collisionClause u v)
  wordToPair : ∀ p : PairKey n, ∀ w : Word n, Matches p w → Holds A (wordPairClause p w)
  support : ∀ p : PairKey n, Holds A (supportClause p)
  candidate : ∀ w : Word n, Holds A (candidateClause w)

/-- Literal-level semantics agree with the relational Boolean encoding. -/
theorem satisfiesClauses_iff (A : Assignment n) (k : ℕ) :
    SatisfiesClauses A k ↔ Satisfies A k := by
  constructor
  · intro h
    refine ⟨h.exactCardinality, ?_, ?_, ?_, ?_⟩
    · intro p u v hu hv hpu hpv
      by_contra hne
      exact (collisionClause_iff A u v).mp (h.collision p u v hpu hpv hne) ⟨hu, hv⟩
    · intro p w hw hm
      exact (wordPairClause_iff A p w).mp (h.wordToPair p w hm) hw
    · intro p hp
      exact (supportClause_iff A p).mp (h.support p) hp
    · intro w
      exact (candidateClause_iff A w).mp (h.candidate w)
  · intro h
    refine ⟨h.exactCardinality, ?_, ?_, ?_, ?_⟩
    · intro p u v hpu hpv hne
      exact (collisionClause_iff A u v).mpr
        (fun huv => hne (h.atMostOne p u v huv.1 huv.2 hpu hpv))
    · intro p w hm
      exact (wordPairClause_iff A p w).mpr fun hw => h.wordImpliesPair p w hw hm
    · exact fun p => (supportClause_iff A p).mpr (h.pairHasSupport p)
    · exact fun w => (candidateClause_iff A w).mpr (h.touched w)

/-- Size 17 transfers to and from the exact cardinality and typed clauses. -/
theorem exists_seventeen_iff_clauses :
    (∃ D : Design 6, Linear D ∧ Saturated D ∧ D.card = 17) ↔
      ∃ A : Assignment 6, SatisfiesClauses A 17 :=
  exists_seventeen_iff.trans (exists_congr (fun A => (satisfiesClauses_iff A 17).symm))

end LatinGap.PairEncoding

#print axioms LatinGap.PairEncoding.exists_seventeen_iff_clauses
