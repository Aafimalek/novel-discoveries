import EulerPairClauses

/-!
# Order-six DIMACS numbering of the word/pair variables

The base Python construction allocates the words first, then the six
increasing coordinate pairs, with value pairs in lexicographic order.
This file checks the numbering and its semantic transport independently
of any auxiliary variables or certificate.
-/

namespace LatinGap.PairEncoding

/-- One-based word number in the order of Python's Cartesian product. -/
def wordNumber (w : Word 6) : Nat :=
  1 + 216 * (w 0).val + 36 * (w 1).val + 6 * (w 2).val + (w 3).val

/-- Zero-based index of the ordered coordinate pairs 01,02,03,12,13,23. -/
def coordNumber (q : CoordPair) : Nat :=
  if q.1.1 = 0 then q.1.2.val - 1
  else if q.1.1 = 1 then q.1.2.val + 1 else 5

/-- One-based used-pair number, after the 1296 word variables. -/
def pairNumber (p : PairKey 6) : Nat :=
  1297 + 36 * coordNumber ⟨(p.i, p.j), p.increasing⟩ + 6 * p.a.val + p.b.val

/-- The fixed, one-based input DIMACS numbers; auxiliaries are separate. -/
def varNumber : Var 6 → Nat
  | .word w => wordNumber w
  | .pair p => pairNumber p

theorem wordNumber_bounds (w : Word 6) : 1 ≤ wordNumber w ∧ wordNumber w ≤ 1296 := by
  have h0 := (w 0).isLt
  have h1 := (w 1).isLt
  have h2 := (w 2).isLt
  have h3 := (w 3).isLt
  unfold wordNumber
  omega

theorem pairNumber_bounds (p : PairKey 6) : 1297 ≤ pairNumber p ∧ pairNumber p ≤ 1512 := by
  have hr : ∀ q : CoordPair, coordNumber q ≤ 5 := by decide
  have ha := p.a.isLt
  have hb := p.b.isLt
  have h := hr ⟨(p.i,p.j),p.increasing⟩
  unfold pairNumber
  omega

theorem wordNumber_injective : Function.Injective wordNumber := by
  intro u v h
  have hu0 := (u 0).isLt
  have hu1 := (u 1).isLt
  have hu2 := (u 2).isLt
  have hu3 := (u 3).isLt
  have hv0 := (v 0).isLt
  have hv1 := (v 1).isLt
  have hv2 := (v 2).isLt
  have hv3 := (v 3).isLt
  unfold wordNumber at h
  have h0 : (u 0).val = (v 0).val := by omega
  have h1 : (u 1).val = (v 1).val := by omega
  have h2 : (u 2).val = (v 2).val := by omega
  have h3 : (u 3).val = (v 3).val := by omega
  funext i
  fin_cases i
  all_goals apply Fin.ext
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem coordNumber_injective : Function.Injective coordNumber := by
  have h : ∀ x y : CoordPair, coordNumber x = coordNumber y → x = y := by decide
  intro x y he; exact h x y he

theorem pairNumber_injective : Function.Injective pairNumber := by
  rintro ⟨i,j,hij,a,b⟩ ⟨i',j',hij',a',b'⟩ h
  change 1297 + 36 * coordNumber ⟨(i,j),hij⟩ + 6*a.val+b.val =
      1297 + 36 * coordNumber ⟨(i',j'),hij'⟩ + 6*a'.val+b'.val at h
  have ha := a.isLt
  have hb := b.isLt
  have ha' := a'.isLt
  have hb' := b'.isLt
  have hc : (⟨(i,j),hij⟩ : CoordPair) = ⟨(i',j'),hij'⟩ := by
    apply coordNumber_injective
    omega
  have e : (i,j) = (i',j') := congrArg Subtype.val hc
  have ei : i = i' := congrArg Prod.fst e
  have ej : j = j' := congrArg Prod.snd e
  subst i'; subst j'
  have ea : a = a' := by apply Fin.ext; omega
  have eb : b = b' := by apply Fin.ext; omega
  subst a'; subst b'
  rfl

theorem varNumber_injective : Function.Injective varNumber := by
  intro x y h
  cases x with
  | word u =>
    cases y with
    | word v => exact congrArg Var.word (wordNumber_injective h)
    | pair p =>
      have hw := (wordNumber_bounds u).2
      have hp := (pairNumber_bounds p).1
      change wordNumber u = pairNumber p at h
      omega
  | pair p =>
    cases y with
    | pair q => exact congrArg Var.pair (pairNumber_injective h)
    | word v =>
      have hw := (wordNumber_bounds v).2
      have hp := (pairNumber_bounds p).1
      change pairNumber p = wordNumber v at h
      omega

/-- Interpret an ordinary valuation of DIMACS numbers as a typed valuation. -/
def liftNumbers (v : Nat → Bool) : Assignment 6 :=
  ⟨fun w => v (wordNumber w), fun p => v (pairNumber p)⟩

theorem eval_liftNumbers (v : Nat → Bool) (x : Var 6) :
    (liftNumbers v).eval x = v (varNumber x) := by cases x <;> rfl

/-- DIMACS signed integer form; every core variable number is positive. -/
def signNumber (l : Lit 6) : Int :=
  if l.2 then (varNumber l.1 : Int) else -(varNumber l.1 : Int)

def NumberedHolds (v : Nat → Bool) (c : List Int) : Prop :=
  ∃ l ∈ c, l ≠ 0 ∧ v l.natAbs = decide (0 < l)

theorem varNumber_pos (x : Var 6) : 0 < varNumber x := by
  cases x with
  | word w => exact (wordNumber_bounds w).1
  | pair p =>
    have h := (pairNumber_bounds p).1
    exact Nat.lt_of_lt_of_le (by decide : 0 < 1297) h

theorem signNumber_spec (l : Lit 6) :
    signNumber l ≠ 0 ∧ (signNumber l).natAbs = varNumber l.1 ∧
      decide (0 < signNumber l) = l.2 := by
  rcases l with ⟨x,b⟩
  have hp := varNumber_pos x
  cases b <;> simp [signNumber] <;> omega

/-- Numbering and DIMACS signs preserve every typed clause. -/
theorem numberedHolds_iff (v : Nat → Bool) (c : Clause 6) :
    NumberedHolds v (c.map signNumber) ↔ Holds (liftNumbers v) c := by
  unfold NumberedHolds Holds
  constructor
  · rintro ⟨_, hl, _, hv⟩
    obtain ⟨l, hm, rfl⟩ := List.mem_map.mp hl
    rw [(signNumber_spec l).2.1, (signNumber_spec l).2.2] at hv
    exact ⟨l, hm, (eval_liftNumbers v l.1).trans hv⟩
  · rintro ⟨l, hm, hl⟩
    obtain ⟨hn, hi, hb⟩ := signNumber_spec l
    exact ⟨signNumber l, List.mem_map_of_mem hm, hn,
      by rw [hi, hb]; exact (eval_liftNumbers v l.1).symm.trans hl⟩

/-- In particular the numbered positive candidate clause is a saturation clause. -/
theorem numberedCandidate_iff (v : Nat → Bool) (w : Word 6) :
    NumberedHolds v ((candidateClause w).map signNumber) ↔
      ∃ p : PairKey 6, v (pairNumber p) = true ∧ Matches p w := by
  exact (numberedHolds_iff _ _).trans (candidateClause_iff _ _)

end LatinGap.PairEncoding

#print axioms LatinGap.PairEncoding.varNumber_injective
#print axioms LatinGap.PairEncoding.numberedHolds_iff
#print axioms LatinGap.PairEncoding.numberedCandidate_iff
