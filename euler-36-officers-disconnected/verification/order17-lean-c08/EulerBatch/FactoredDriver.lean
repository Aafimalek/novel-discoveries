/-
This driver uses the explicit RUP term builder in Mathlib.Tactic.Sat.FromLRAT,
originally authored by Mario Carneiro (Mathlib, Apache License 2.0).
Unlike the one-term driver, it puts each checked RUP step in its own theorem.
-/

import Mathlib.Tactic.Sat.FromLRAT

open Lean Elab Command Term

set_option maxHeartbeats 0
set_option maxRecDepth 50000

elab "factored_rup " n:ident ppSpace cnf:term:max ppSpace lrat:term:max : command =>
  liftTermElabM do
    let ns ← getCurrNamespace
    let cnf ← unsafe evalTerm String (Lean.mkConst ``String) cnf
    let cert ← unsafe evalTerm String (Lean.mkConst ``String) lrat
    let .success _ (_, arr) := Mathlib.Tactic.Sat.Parser.parseDimacs ⟨_, cnf.startPos⟩
      | throwError "CNF parser rejected input"
    let .success _ steps := Mathlib.Tactic.Sat.Parser.parseLRAT ⟨_, cert.startPos⟩
      | throwError "LRAT parser rejected input"
    let name := ns ++ n.getId
    let ctxName := name ++ `cnf
    let ctx := Lean.mkConst ctxName
    let ctx' := Mathlib.Tactic.Sat.buildConj arr 0 arr.size
    addDecl <| .defnDecl {
      name := ctxName, levelParams := [], type := Lean.mkConst ``Sat.Fmla,
      value := ctx', hints := .regular 0, safety := .safe
    }
    let root := mkApp (Lean.mkConst ``Sat.Fmla.subsumes_self) ctx
    let mut db := (Mathlib.Tactic.Sat.buildClauses arr ctx 0 arr.size ctx' root default).2
    let mut c := 0
    for step in steps do
      match step with
      | .del ds => db := ds.foldl (·.erase ·) db
      | .add i ns hints =>
        let e := Mathlib.Tactic.Sat.buildClause ns
        let .ok pf := Mathlib.Tactic.Sat.buildProofStep db ns hints ctx e
          | throwError "RUP proof construction failed at ID {i}"
        let id := if ns.isEmpty then name else Name.num (name ++ `lemmas) i
        addDecl <| .thmDecl {
          name := id, levelParams := [], type := mkApp2 (Lean.mkConst ``Sat.Fmla.proof) ctx e,
          value := pf
        }
        if ns.isEmpty then return
        db := db.insert i { lits := ns, expr := e, proof := Lean.mkConst id }
        c := c + 1
        if c % 25 == 0 then IO.eprintln s!"checked {c} RUP additions"
    throwError "No empty clause was checked"

