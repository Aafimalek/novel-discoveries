import EulerC14IndexedDraft

open Lean Elab Command Term Meta
open Mathlib.Tactic.Sat

namespace Euler.C14.IndexedDraft

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

theorem before_of_blt (a b : Nat) (h : Nat.blt a b = true) : a < b :=
  Eq.mp Nat.blt_eq h

elab "indexed_rup " baseName:ident rowName:ident runnerName:ident inputs:term:max steps:term:max : command => do
  let ns ← getCurrNamespace
  liftTermElabM do
    let base ← elabTerm baseName (some (mkConst ``Sat.Fmla))
    let rowAt ← elabTerm rowName (some (mkConst ``ClauseAt))
    let inTy ← elabType (← `(Array (Nat × Array Int)))
    let traceTy ← elabType (← `(Array (Nat × Array Int × Array Int)))
    let orig ← unsafe evalTerm (Array (Nat × Array Int)) inTy inputs
    let additions ← unsafe evalTerm (Array (Nat × Array Int × Array Int)) traceTy steps
    unless orig.size ≤ 200 && additions.size ≤ 24 do throwError "pilot too large"
    let mut rows : Std.HashMap Nat (Nat × Array Int) := {}
    for k in [:orig.size] do
      let (i, lits) := orig[k]!
      rows := rows.insert i (k, lits)
    let mut thms : Array Expr := #[]
    for k in [:additions.size] do
      let (id,lits,hints) := additions[k]!
      let step := orig.size + k
      if rows.contains id then throwError "repeated original ID"
      let stepThm ← withLocalDeclD `ready
        (mkAppN (mkConst ``GoodBelow) #[base, rowAt, mkNatLit step]) fun ready => do
        let mut db : Std.HashMap Nat Mathlib.Tactic.Sat.Clause := {}
        for h in hints do
          let some (slot, clause) := rows[h.natAbs]? | throwError "forward/missing ID {h}"
          let kx := mkNatLit slot
          let refl ← mkEqRefl (mkConst ``Bool.true)
          let pr := mkApp3 (mkConst ``before_of_blt) kx (mkNatLit step) refl
          let premise : Mathlib.Tactic.Sat.Clause := {
            lits := clause
            expr := buildClause clause
            proof := mkApp2 ready kx pr
          }
          db := db.insert h.natAbs premise
        let .ok proof := buildProofStep db lits hints base (buildClause lits)
          | throwError "RUP term builder failed at {id}"
        mkLambdaFVars #[ready] proof
      let tname := ns ++ Name.mkSimple s!"step_{id}"
      let ty ← mkArrow (mkAppN (mkConst ``GoodBelow) #[base, rowAt, mkNatLit step])
        (mkApp2 (mkConst ``Sat.Fmla.proof) base (mkApp rowAt (mkNatLit step)))
      addDecl <| .thmDecl { name := tname, levelParams := [], type := ty, value := stepThm }
      rows := rows.insert id (step,lits)
      thms := thms.push (mkAppN (mkConst ``extend) #[base,rowAt,mkNatLit step,mkConst tname])
    let some head := thms[0]? | throwError "no steps"
    let mut proof := head
    for k in [1:thms.size] do
      proof := mkAppN (mkConst ``compose)
        #[base,rowAt,mkNatLit orig.size,mkNatLit (orig.size+k),mkNatLit (orig.size+k+1),
          proof,thms[k]!]
    let ty := mkAppN (mkConst ``Slice)
      #[base,rowAt,mkNatLit orig.size,mkNatLit (orig.size+additions.size)]
    addDecl <| .thmDecl { name := ns ++ runnerName.getId, levelParams := [], type := ty, value := proof }

end Euler.C14.IndexedDraft
