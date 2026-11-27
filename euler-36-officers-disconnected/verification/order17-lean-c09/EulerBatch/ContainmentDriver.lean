import EulerBatch.FactoredDriver

namespace Euler.Batch.Driver

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
    type := Lean.mkConst ``Sat.Fmla
    value := value
    hints := ReducibilityHints.regular 0
    safety := DefinitionSafety.safe
  }
  return Lean.mkConst name

/-- Balanced chunks keep the full CNF expression small enough for kernel checking. -/
private partial def buildTree (arr : Array (Array Int)) (start stop : Nat) : MetaM FTree := do
  let len := stop - start
  if len = 0 then throwError "empty interval"
  if len = 1 then
    return .leaf (mkApp (Lean.mkConst ``Sat.Fmla.one) (buildClause arr[start]!))
  let mid := start + len / 2
  let a ← buildTree arr start mid
  let b ← buildTree arr mid stop
  let bare := mkApp2 (Lean.mkConst ``Sat.Fmla.and) a.expr b.expr
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
      singletonInclude full a start mid idx (mkApp4 (Lean.mkConst ``Sat.Fmla.subsumes_left)
        full a.expr b.expr h)
    else
      singletonInclude full b mid stop idx (mkApp4 (Lean.mkConst ``Sat.Fmla.subsumes_right)
        full a.expr b.expr h)

private def addClosed (n : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name := n, levelParams := [], type := type, value := value }

/-- Combine original-clause paths, sharing proofs at regular boundaries. -/
private partial def coreInclude (full : Expr) (t : FTree) (fullSize : Nat)
    (lookup : Array Nat) (start stop : Nat) (e : Expr) : MetaM Expr := do
  let len := stop - start
  if len = 1 then
    return singletonInclude full t 0 fullSize lookup[start]! (mkApp (Lean.mkConst ``Sat.Fmla.subsumes_self) full)
  let mid := start + len / 2
  let a := e.appFn!.appArg!
  let b := e.appArg!
  let p ← coreInclude full t fullSize lookup start mid a
  let q ← coreInclude full t fullSize lookup mid stop b
  let bare := mkApp5 (Lean.mkConst ``subsumes_and) full a b p q
  if len < 16 then return bare
  let name ← mkAuxDeclName `inclusionChunk
  addClosed name (mkApp2 (Lean.mkConst ``Sat.Fmla.subsumes) full e) bare
  return Lean.mkConst name

elab "prove_numbered_containment " fullId:ident incId:ident unsatId:ident coreId:ident
    vars:num clauses:num coreClauses:num ppSpace original:term:max ppSpace core:term:max : command => do
  let ns ← getCurrNamespace
  Command.liftTermElabM do
    let original ← unsafe evalTerm String (Lean.mkConst ``String) original
    let core ← unsafe evalTerm String (Lean.mkConst ``String) core
    let Std.Internal.Parsec.ParseResult.success e₁ (n₁, a) :=
      Parser.parseDimacs ⟨_, original.startPos⟩ | throwError "full DIMACS failed to parse"
    let Std.Internal.Parsec.ParseResult.success e₂ (n₂, b) :=
      Parser.parseDimacs ⟨_, core.startPos⟩ | throwError "core DIMACS failed to parse"
    unless decide (e₁.2.IsAtEnd ∧ e₂.2.IsAtEnd) do
      throwError "unparsed text in the full or core DIMACS"
    unless n₁ == vars.getNat && n₁ == n₂ && a.size == clauses.getNat && b.size == coreClauses.getNat do
      throwError "wrong full/core dimensions"
    let mut indices : Std.HashMap (Array Int) Nat := {}
    for i in [:a.size] do
      indices := indices.insert a[i]! i
    let lookup ← b.mapM fun c =>
      match indices[c]? with
      | some i => pure i
      | none => throwError "ordered core clause not found with these exact literals: {c}"
    let coreThm := ns ++ coreId.getId
    let coreName := coreThm ++ `cnf
    let k := Lean.mkConst coreName
    let some (.defnInfo d) := (← getEnv).find? coreName
      | throwError "missing checked core formula definition"
    let coreBody := buildConj b 0 b.size
    unless d.value == coreBody do
      throwError "reparsed core differs from the kernel-checked core's formula value"
    IO.eprintln "exact parsed core matched; building balanced full formula"
    let tree ← buildTree a 0 a.size
    let f ← aliasFormula (ns ++ fullId.getId) tree.expr
    IO.eprintln "checking factored containment"
    let inc := ns ++ incId.getId
    let pfInc ← coreInclude f tree a.size lookup 0 b.size coreBody
    addClosed inc (mkApp2 (Lean.mkConst ``Sat.Fmla.subsumes) f k) pfInc
    let unsat := ns ++ unsatId.getId
    addClosed unsat
      (mkApp2 (Lean.mkConst ``Sat.Fmla.proof) f (Lean.mkConst ``Sat.Clause.nil))
      (mkApp4 (Lean.mkConst ``empty_of_subsumes) f k (Lean.mkConst inc) (Lean.mkConst coreThm))

set_option maxHeartbeats 0
set_option maxRecDepth 100000

end Euler.Batch.Driver
