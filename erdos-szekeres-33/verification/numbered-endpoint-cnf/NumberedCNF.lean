import Lean

namespace ES33.Numbering

/-- A typed literal: `true` means positive. -/
structure Lit (V : Type) where
  var : V
  pos : Bool
  deriving Repr

abbrev CNF (V : Type) := List (List (Lit V))
abbrev NumberedCNF := List (List Int)

def Lit.holds {V : Type} (a : V → Bool) (l : Lit V) : Prop :=
  a l.var = l.pos

def Satisfies {V : Type} (a : V → Bool) (F : CNF V) : Prop :=
  ∀ c ∈ F, ∃ l ∈ c, l.holds a

/-- Signed magnitude DIMACS semantics. Zero is only a line terminator,
not a literal, and is false under either Boolean assignment. -/
def numberedHolds (a : Nat → Bool) (l : Int) : Prop :=
  l ≠ 0 ∧ a l.natAbs = decide (0 < l)

def NumberedSatisfies (a : Nat → Bool) (F : NumberedCNF) : Prop :=
  ∀ c ∈ F, ∃ l ∈ c, numberedHolds a l

def signed {V : Type} (id : V → Nat) (l : Lit V) : Int :=
  if l.pos then (id l.var : Int) else -(id l.var : Int)

def encode {V : Type} (id : V → Nat) (F : CNF V) : NumberedCNF :=
  F.map (fun c => c.map (signed id))

theorem signed_abs {V : Type} (id : V → Nat) (l : Lit V) :
    (signed id l).natAbs = id l.var := by
  unfold signed
  split <;> simp

theorem signed_pos {V : Type} (id : V → Nat) (nz : ∀ v, id v > 0) (l : Lit V) :
    decide (0 < signed id l) = l.pos := by
  have hi := nz l.var
  unfold signed
  cases l.pos <;> simp <;> omega

theorem signed_nonzero {V : Type} (id : V → Nat) (nz : ∀ v, id v > 0) (l : Lit V) :
    signed id l ≠ 0 := by
  intro h
  have hn := signed_abs id l
  rw [h] at hn
  have hi := nz l.var
  omega

theorem holds_iff {V : Type} (id : V → Nat) (nz : ∀ v, id v > 0)
    (a : Nat → Bool) (l : Lit V) :
    numberedHolds a (signed id l) ↔ l.holds (fun v => a (id v)) := by
  simp [numberedHolds,Lit.holds,signed_abs,signed_pos id nz,signed_nonzero id nz]

theorem satisfies_iff {V : Type} (id : V → Nat) (nz : ∀ v, id v > 0)
    (a : Nat → Bool) (F : CNF V) :
    NumberedSatisfies a (encode id F) ↔ Satisfies (fun v => a (id v)) F := by
  constructor
  · intro H c hc
    obtain ⟨p,hp,h⟩ := H (c.map (signed id)) (List.mem_map.mpr ⟨c,hc,rfl⟩)
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
    exact ⟨l,hl,(holds_iff id nz a l).mp h⟩
  · intro H nc hnc
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hnc
    obtain ⟨l,hl,h⟩ := H c hc
    exact ⟨signed id l,List.mem_map.mpr ⟨l,hl,rfl⟩,(holds_iff id nz a l).mpr h⟩

/-- The finite variable table is layout-independent. Numbering uses first
occurrences, so even a table with duplicates cannot alias distinct variables. -/
abbrev Indexed {V : Type} (keys : List V) := {v : V // v ∈ keys}

def index {V : Type} [BEq V] (keys : List V) (v : Indexed keys) : Nat :=
  keys.idxOf v.val + 1

theorem index_pos {V : Type} [BEq V] (keys : List V) (v : Indexed keys) :
    index keys v > 0 := Nat.succ_pos _

theorem index_bound {V : Type} [BEq V] [LawfulBEq V] (keys : List V) (v : Indexed keys) :
    index keys v ≤ keys.length :=
  List.idxOf_lt_length_of_mem v.property

def lookup {V : Type} (keys : List V) (a : Indexed keys → Bool) (i : Nat) : Bool :=
  if h : i-1 < keys.length then
    a ⟨keys[i-1], List.getElem_mem h⟩
  else false

theorem lookup_index {V : Type} [BEq V] [LawfulBEq V] (keys : List V)
    (a : Indexed keys → Bool) (v : Indexed keys) : lookup keys a (index keys v) = a v := by
  have h : keys.idxOf v.val < keys.length := List.idxOf_lt_length_of_mem v.property
  have e := List.getElem_idxOf h
  have ha : (⟨keys[keys.idxOf v.val], List.getElem_mem h⟩ : Indexed keys) = v :=
    Subtype.ext e
  simp only [lookup,index,Nat.add_sub_cancel, dite_eq_left h,ha]

theorem index_injective {V : Type} [BEq V] [LawfulBEq V] (keys : List V) :
    Function.Injective (index keys) := by
  intro a b h
  let distinguish (v : Indexed keys) : Bool := a.val == v.val
  have Q : distinguish a = distinguish b := by
    rw [← lookup_index keys distinguish a, ← lookup_index keys distinguish b, h]
  have A : distinguish a = true := by simp [distinguish]
  exact Subtype.ext (beq_iff_eq.mp (Q.symm.trans A))

theorem finite_encoding_equisat {V : Type} [BEq V] [LawfulBEq V] (keys : List V)
    (F : CNF (Indexed keys)) :
    (∃ a, NumberedSatisfies a (encode (index keys) F)) ↔ ∃ a, Satisfies a F := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨_,(satisfies_iff _ (index_pos keys) a F).mp ha⟩
  · rintro ⟨a,ha⟩
    refine ⟨lookup keys a, (satisfies_iff _ (index_pos keys) _ _).mpr ?_⟩
    simpa only [lookup_index] using ha

theorem every_numbered_literal_legal {V : Type} [BEq V] [LawfulBEq V] (keys : List V)
    (F : CNF (Indexed keys)) (c : List Int) (l : Int)
    (hc : c ∈ encode (index keys) F) (hl : l ∈ c) : l ≠ 0 ∧ l.natAbs ≤ keys.length := by
  obtain ⟨tc,hc,rfl⟩ := List.mem_map.mp hc
  obtain ⟨tl,hl,rfl⟩ := List.mem_map.mp hl
  exact ⟨signed_nonzero _ (index_pos keys) _, (signed_abs _ _).symm ▸ index_bound keys tl.var⟩

/-- Every literal in the input appears in the finite table. -/
def Supports {V : Type} (keys : List V) (F : CNF V) : Prop :=
  ∀ c ∈ F, ∀ l ∈ c, l.var ∈ keys

def scopeClause {V : Type} (keys : List V) (c : List (Lit V))
    (hc : ∀ l ∈ c, l.var ∈ keys) : List (Lit (Indexed keys)) :=
  c.attach.map fun l => ⟨⟨l.val.var, hc l.val l.property⟩, l.val.pos⟩

def scope {V : Type} (keys : List V) (F : CNF V)
    (covered : Supports keys F) : CNF (Indexed keys) :=
  F.attach.map fun c => scopeClause keys c.val (covered c.val c.property)

def extendDefault {V : Type} [DecidableEq V] (keys : List V)
    (a : Indexed keys → Bool) (v : V) : Bool :=
  if h : v ∈ keys then a ⟨v,h⟩ else false

theorem scope_satisfies_iff {V : Type} [DecidableEq V] (keys : List V) (F : CNF V)
    (covered : Supports keys F) (a : Indexed keys → Bool) :
    Satisfies a (scope keys F covered) ↔ Satisfies (extendDefault keys a) F := by
  constructor
  · intro H c hc
    have hs : scopeClause keys c (covered c hc) ∈ scope keys F covered :=
      List.mem_map.mpr ⟨⟨c,hc⟩,List.mem_attach F _,rfl⟩
    obtain ⟨w,hw,v⟩ := H _ hs
    obtain ⟨l,_,rfl⟩ := List.mem_map.mp hw
    refine ⟨l.val,l.property,?_⟩
    simpa [extendDefault,Lit.holds,covered _ hc _ l.property] using v
  · intro H s hs
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hs
    obtain ⟨l,hl,v⟩ := H c.val c.property
    refine ⟨⟨⟨l.var,covered _ c.property _ hl⟩,l.pos⟩,
      List.mem_map.mpr ⟨⟨l,hl⟩,List.mem_attach _ _,rfl⟩,?_⟩
    simpa [extendDefault,Lit.holds,covered _ c.property _ hl] using v

theorem scope_equisat {V : Type} [DecidableEq V] (keys : List V) (F : CNF V)
    (covered : Supports keys F) :
    (∃ a, Satisfies a (scope keys F covered)) ↔ ∃ a, Satisfies a F := by
  constructor
  · rintro ⟨a,h⟩
    exact ⟨_,(scope_satisfies_iff keys F covered a).mp h⟩
  · rintro ⟨a,h⟩
    refine ⟨fun v => a v.val, (scope_satisfies_iff keys F covered _).mpr ?_⟩
    intro c hc
    obtain ⟨l,hl,v⟩ := h c hc
    refine ⟨l,hl,?_⟩
    simpa [extendDefault,Lit.holds,covered _ hc _ hl] using v

def compile {V : Type} [BEq V] (keys : List V) (F : CNF V)
    (covered : Supports keys F) : NumberedCNF :=
  encode (index keys) (scope keys F covered)

/-- Exact end-to-end renaming theorem for any finite typed formula plus a
covering dictionary; the order of the table is arbitrary. -/
theorem compile_equisat {V : Type} [DecidableEq V] [BEq V] [LawfulBEq V]
    (keys : List V) (F : CNF V) (covered : Supports keys F) :
    (∃ a, NumberedSatisfies a (compile keys F covered)) ↔ ∃ a, Satisfies a F :=
  (finite_encoding_equisat keys (scope keys F covered)).trans
    (scope_equisat keys F covered)

def variableTable {V : Type} [BEq V] (F : CNF V) : List V :=
  (F.flatMap (List.map Lit.var)).eraseDups

theorem variableTable_supports {V : Type} [BEq V] [LawfulBEq V] (F : CNF V) :
    Supports (variableTable F) F := by
  intro c hc l hl
  exact List.mem_eraseDups.mpr <|
    List.mem_flatMap.mpr ⟨c,hc,List.mem_map.mpr ⟨l,hl,rfl⟩⟩

/-- After a text frontend has separated the header and integer tokens,
these fields retain the DIMACS variable bound, clause count, and rows.
Each row must contain exactly one terminal zero. -/
structure TokenDocument where
  numVars : Nat
  numClauses : Nat
  rows : List (List Int)

def TokenDocument.emit (v : Nat) (F : NumberedCNF) : TokenDocument :=
  ⟨v,F.length,F.map (fun c => c ++ [0])⟩

def parseTokenRow (v : Nat) (row : List Int) : Option (List Int) :=
  match row.reverse with
  | [] => none
  | last :: rev =>
    if last = 0 ∧ rev.all (fun l => decide (l ≠ 0 ∧ l.natAbs ≤ v)) = true then
      some rev.reverse
    else none

def TokenDocument.parse (d : TokenDocument) : Option NumberedCNF :=
  if d.rows.length = d.numClauses then d.rows.mapM (parseTokenRow d.numVars)
  else none

theorem token_row_roundtrip (v : Nat) (c : List Int)
    (H : ∀ l ∈ c, l ≠ 0 ∧ l.natAbs ≤ v) :
    parseTokenRow v (c ++ [0]) = some c := by
  simpa [parseTokenRow,List.reverse_append] using H

private theorem token_rows_roundtrip (v : Nat) (F : NumberedCNF)
    (H : ∀ c ∈ F, ∀ l ∈ c, l ≠ 0 ∧ l.natAbs ≤ v) :
    (F.map (fun c => c ++ [0])).mapM (parseTokenRow v) = some F := by
  induction F with
  | nil => rfl
  | cons c cs ih =>
    have A := token_row_roundtrip v c (H c (by simp))
    have B := ih (fun q h => H q (by simp [h]))
    rw [List.map_cons,List.mapM_cons,A,B]
    rfl

theorem token_document_roundtrip (v : Nat) (F : NumberedCNF)
    (H : ∀ c ∈ F, ∀ l ∈ c, l ≠ 0 ∧ l.natAbs ≤ v) :
    (TokenDocument.emit v F).parse = some F := by
  have A := token_rows_roundtrip v F H
  simp [TokenDocument.emit,TokenDocument.parse,A]

def emit {V : Type} [BEq V] (keys : List V) (F : CNF V)
    (covered : Supports keys F) : TokenDocument :=
  TokenDocument.emit keys.length (compile keys F covered)

theorem compile_roundtrip {V : Type} [BEq V] [LawfulBEq V]
    (keys : List V) (F : CNF V) (covered : Supports keys F) :
    (emit keys F covered).parse = some (compile keys F covered) :=
  token_document_roundtrip keys.length _ <|
    fun c hc l hl => every_numbered_literal_legal keys (scope keys F covered) c l hc hl

/-- Checked transport from an unsatisfiability result about the *same*
parsed numbered clauses; a parser for untrusted text is a separate layer. -/
theorem of_checked_numbered_unsat {V : Type} [DecidableEq V] [BEq V] [LawfulBEq V]
    (keys : List V) (F : CNF V) (covered : Supports keys F)
    (C : NumberedCNF) (same : (emit keys F covered).parse = some C)
    (unsat : ¬ ∃ a, NumberedSatisfies a C) :
    ¬ ∃ a, Satisfies a F := by
  rw [compile_roundtrip] at same
  have hc := Option.some.inj same
  subst C
  exact fun h => unsat ((compile_equisat keys F covered).mpr h)

/-- The five typed state families before numbering. The exponent/width
parameter is an ordinary natural; the checked table only includes states
the concrete generator needs. No implicit aliasing between families. -/
inductive EndpointVar (n : Nat)
  | sign (a b c : Fin n)
  | capLast (d : Nat) (a b c : Fin n)
  | cupFirst (d : Nat) (a b c : Fin n)
  | capPair (d : Nat) (a c : Fin n)
  | cupPair (d : Nat) (a c : Fin n)
  deriving DecidableEq, Repr

#print axioms finite_encoding_equisat
#print axioms every_numbered_literal_legal
#print axioms index_injective
#print axioms compile_equisat
#print axioms variableTable_supports
#print axioms compile_roundtrip
#print axioms of_checked_numbered_unsat

end ES33.Numbering
