import Lean

namespace ES33.ReflectionLex

/-- Boolean lexicographic comparison, with false before true. -/
def LexLE : List Bool → List Bool → Prop
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => (x = false ∧ y = true) ∨ (x = y ∧ LexLE xs ys)

theorem lex_total (xs ys : List Bool) : LexLE xs ys ∨ LexLE ys xs := by
  induction xs generalizing ys with
  | nil => exact Or.inl trivial
  | cons x xs ih =>
    cases ys with
    | nil => exact Or.inr trivial
    | cons y ys =>
      cases x <;> cases y
      · simpa [LexLE] using ih ys
      · exact Or.inl (Or.inl ⟨rfl,rfl⟩)
      · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
      · simpa [LexLE] using ih ys

/-- Abstract symmetry breaking. All geometry is confined to the external
hypotheses: a reflection preserves the witness property, and twice applying
it gives the same serialized sign word. -/
theorem exists_lex_representative {X : Type} (bad : X → Prop)
    (reflect : X → X) (word : X → List Bool)
    (closed : ∀ p, bad p → bad (reflect p))
    (twice : ∀ p, word (reflect (reflect p)) = word p) :
    (∃ p, bad p ∧ LexLE (word p) (word (reflect p))) ↔ ∃ p, bad p := by
  constructor
  · rintro ⟨p,h,_⟩
    exact ⟨p,h⟩
  · rintro ⟨p,h⟩
    rcases lex_total (word p) (word (reflect p)) with hl | hr
    · exact ⟨p,h,hl⟩
    · refine ⟨reflect p,closed p h,?_⟩
      rw [twice]
      exact hr

/-- The comparison condition under a guard; its CNF row is
`¬g ∨ ¬a ∨ b`. -/
def Compare (g a b : Bool) : Prop := g = true → a = true → b = true

/-- The next-guard condition; it emits two implication clauses, one for
each common value of the two sign bits. -/
def Advance (g a b next : Bool) : Prop := g = true → a = b → next = true

theorem compare_clause (g a b : Bool) :
    Compare g a b ↔ (g = false ∨ a = false ∨ b = true) := by
  cases g <;> cases a <;> cases b <;> simp [Compare]

theorem advance_clauses (g a b next : Bool) :
    Advance g a b next ↔
      ((g = false ∨ a = true ∨ b = true ∨ next = true) ∧
       (g = false ∨ a = false ∨ b = false ∨ next = true)) := by
  cases g <;> cases a <;> cases b <;> cases next <;> simp [Advance]

/-- Existential next-guard bits in order. On the last pair the extra
existential bit can always be set true, so it needs no physical variable
or advance clauses. -/
def Leader : Bool → List (Bool × Bool) → Prop
  | _, [] => True
  | g, (a,b) :: xs =>
    Compare g a b ∧ ∃ next : Bool, Advance g a b next ∧ Leader next xs

theorem leader_last (g a b : Bool) : Leader g [(a,b)] ↔ Compare g a b := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h,true,(fun _ _ => rfl),trivial⟩

theorem leader_false (pairs : List (Bool × Bool)) : Leader false pairs := by
  induction pairs with
  | nil => exact trivial
  | cons p xs ih =>
    obtain ⟨a,b⟩ := p
    exact ⟨(fun h _ => Bool.noConfusion h), false,
      (fun h _ => Bool.noConfusion h), ih⟩

/-- Existence of guards is exactly lex order of the two represented
vectors. No backward equality constraints on the guards are needed. -/
theorem leader_iff_lex (pairs : List (Bool × Bool)) :
    Leader true pairs ↔ LexLE (pairs.map Prod.fst) (pairs.map Prod.snd) := by
  induction pairs with
  | nil => exact Iff.rfl
  | cons p xs ih =>
    obtain ⟨a,b⟩ := p
    cases a <;> cases b
    · change
        ((true = true → false = true → false = true) ∧
          ∃ next : Bool, (true = true → false = false → next = true) ∧ Leader next xs)
          ↔ LexLE (false :: xs.map Prod.fst) (false :: xs.map Prod.snd)
      simp [LexLE, ← ih]
    · constructor
      · intro _
        exact Or.inl ⟨rfl,rfl⟩
      · intro _
        exact ⟨(fun _ h => Bool.noConfusion h),false,
          (fun _ h => Bool.noConfusion h),leader_false xs⟩
    · constructor
      · intro h
        exact Bool.noConfusion (h.1 rfl rfl)
      · intro h
        rcases h with ⟨hr,_⟩ | ⟨hr,_⟩ <;> exact Bool.noConfusion hr
    · change
        ((true = true → true = true → true = true) ∧
          ∃ next : Bool, (true = true → true = true → next = true) ∧ Leader next xs)
          ↔ LexLE (true :: xs.map Prod.fst) (true :: xs.map Prod.snd)
      simp [LexLE, ← ih]

/-- Specialization to orbit-paired signs. Reflection exchanges the
two bits of every orbit without reordering the chosen orbit list. -/
theorem exists_leader_representative {X : Type} (bad : X → Prop)
    (reflect : X → X) (pairs : X → List (Bool × Bool))
    (closed : ∀ p, bad p → bad (reflect p))
    (swap : ∀ p, pairs (reflect p) = (pairs p).map Prod.swap) :
    (∃ p, bad p ∧ Leader true (pairs p)) ↔ ∃ p, bad p := by
  constructor
  · rintro ⟨p,h,_⟩
    exact ⟨p,h⟩
  · rintro ⟨p,h⟩
    rcases lex_total ((pairs p).map Prod.fst) ((pairs p).map Prod.snd) with hl | hr
    · exact ⟨p,h,(leader_iff_lex _).mpr hl⟩
    · refine ⟨reflect p,closed p h,(leader_iff_lex _).mpr ?_⟩
      rw [swap p]
      simpa [List.map_map, Function.comp_def] using hr

#print axioms exists_lex_representative
#print axioms compare_clause
#print axioms advance_clauses
#print axioms leader_last
#print axioms leader_iff_lex
#print axioms exists_leader_representative

end ES33.ReflectionLex
