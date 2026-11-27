import Mathlib.Tactic.Sat.FromLRAT

namespace ES33.NumberedPilot

open Lean Elab Term Meta
open Mathlib.Tactic.Sat

/-- Glue two already proved clause inclusions. -/
theorem subsumes_and (f a b : Sat.Fmla)
    (ha : f.subsumes a) (hb : f.subsumes b) : f.subsumes (a.and b) :=
  ⟨fun c h => (List.mem_append.mp h).elim (ha.1 c) (hb.1 c)⟩

/-- A proof of the empty clause on a subformula refutes the larger formula. -/
theorem empty_of_subsumes (f g : Sat.Fmla)
    (inc : f.subsumes g) (unsat : g.proof Sat.Clause.nil) :
    f.proof Sat.Clause.nil :=
  fun v hv => unsat v ⟨fun c hc => hv.1 c (inc.1 c hc)⟩

private inductive FTree where
  | leaf (expr : Expr)
  | node (expr : Expr) (left right : FTree)

private def FTree.expr : FTree → Expr
  | .leaf e => e
  | .node e _ _ => e

private def aliasFormula (name : Name) (value : Expr) : MetaM Expr := do
  addDecl <| Declaration.defnDecl {
    name := name
    levelParams := []
    type := mkConst ``Sat.Fmla
    value := value
    hints := ReducibilityHints.regular 0
    safety := DefinitionSafety.safe
  }
  return mkConst name

/-- Balanced chunks keep the full CNF expression small enough for kernel checking. -/
private partial def buildTree (arr : Array (Array Int)) (start stop : Nat) : MetaM FTree := do
  let len := stop - start
  if len = 0 then throwError "empty interval"
  if len = 1 then
    return .leaf (mkApp (mkConst ``Sat.Fmla.one) (buildClause arr[start]!))
  let mid := start + len / 2
  let a ← buildTree arr start mid
  let b ← buildTree arr mid stop
  let bare := mkApp2 (mkConst ``Sat.Fmla.and) a.expr b.expr
  let e ← if len ≥ 128 then aliasFormula (← mkAuxDeclName `numberedCnfChunk) bare else pure bare
  return .node e a b

/-- Find a proved singleton inclusion by following its full formula path. -/
private partial def singletonInclude
    (full : Expr) (t : FTree) (start stop idx : Nat) (h : Expr) : Expr :=
  match t with
  | .leaf _ => h
  | .node _ a b =>
    let mid := start + (stop - start) / 2
    if idx < mid then
      singletonInclude full a start mid idx (mkApp4 (mkConst ``Sat.Fmla.subsumes_left)
        full a.expr b.expr h)
    else
      singletonInclude full b mid stop idx (mkApp4 (mkConst ``Sat.Fmla.subsumes_right)
        full a.expr b.expr h)

/-- Rebuild core inclusion from its singleton paths in the original. -/
private partial def coreInclude (full : Expr) (t : FTree) (fullSize : Nat)
    (lookup : Array Nat) (start stop : Nat) (e : Expr) : Expr :=
  if stop - start = 1 then
    singletonInclude full t 0 fullSize lookup[start]! (mkApp (mkConst ``Sat.Fmla.subsumes_self) full)
  else
    let mid := start + (stop - start) / 2
    let a := e.appFn!.appArg!
    let b := e.appArg!
    mkApp5 (mkConst ``subsumes_and) full a b
      (coreInclude full t fullSize lookup start mid a)
      (coreInclude full t fullSize lookup mid stop b)

private def addClosed (n : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name := n, levelParams := [], type := type, value := value }

elab "prove_numbered_containment " fullId:ident coreId:ident incId:ident unsatId:ident
    ppSpace original:term:max ppSpace core:term:max ppSpace lrat:term:max : command => do
  let ns ← getCurrNamespace
  Command.liftTermElabM do
    let original ← unsafe evalTerm String (mkConst ``String) original
    let core ← unsafe evalTerm String (mkConst ``String) core
    let lrat ← unsafe evalTerm String (mkConst ``String) lrat
    let Std.Internal.Parsec.ParseResult.success e₁ (n₁, a) :=
      Parser.parseDimacs ⟨_, original.startPos⟩ | throwError "full DIMACS failed to parse"
    let Std.Internal.Parsec.ParseResult.success e₂ (n₂, b) :=
      Parser.parseDimacs ⟨_, core.startPos⟩ | throwError "core DIMACS failed to parse"
    unless decide (e₁.2.IsAtEnd ∧ e₂.2.IsAtEnd) do
      throwError "unparsed text in the full or core DIMACS"
    unless n₁ == 5456 && n₁ == n₂ && a.size == 69408 && b.size == 60 do
      throwError "wrong full/core dimensions"
    let mut indices : Std.HashMap (Array Int) Nat := {}
    for i in [:a.size] do
      indices := indices.insert a[i]! i
    let lookup ← b.mapM fun c =>
      match indices[c]? with
      | some i => pure i
      | none => throwError "ordered core clause not found with these exact literals: {c}"
    let (_, coreRef, coreBody, coreProof) ← fromLRATAux core lrat (ns ++ unsatId.getId)
    let k ← aliasFormula (ns ++ coreId.getId) coreRef
    let tree ← buildTree a 0 a.size
    let f ← aliasFormula (ns ++ fullId.getId) tree.expr
    let inc := ns ++ incId.getId
    let pfInc := coreInclude f tree a.size lookup 0 b.size coreBody
    addClosed inc (mkApp2 (mkConst ``Sat.Fmla.subsumes) f k) pfInc
    let unsat := ns ++ unsatId.getId
    addClosed unsat
      (mkApp2 (mkConst ``Sat.Fmla.proof) f (mkConst ``Sat.Clause.nil))
      (mkApp4 (mkConst ``empty_of_subsumes) f k (mkConst inc) coreProof)

set_option maxHeartbeats 0
set_option maxRecDepth 100000

prove_numbered_containment slot32FullFormula slot32CoreFormula slot32ContainsCore slot32FullUnsat
  (include_str "original.cnf") (include_str "core.cnf") (include_str "core.lrat")

/-- The exact parsed full rightmost-slot formula admits no valuation. -/
theorem slot32NoAssignment : ¬ ∃ v : Sat.Valuation, v.satisfies_fmla slot32FullFormula := by
  rintro ⟨v,hv⟩
  exact slot32FullUnsat v hv

#print axioms slot32NoAssignment
#print axioms slot32ContainsCore
#print axioms slot32FullUnsat

end ES33.NumberedPilot
