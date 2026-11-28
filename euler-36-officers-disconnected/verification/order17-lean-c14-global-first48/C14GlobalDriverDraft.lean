import EulerC14IndexedDraft
import C14GlobalDirectory

open Lean Elab Command Term Meta
open Mathlib.Tactic.Sat

namespace Euler.C14.Production

open Euler.C14.IndexedDraft

set_option maxHeartbeats 2400000
set_option maxRecDepth 18000

theorem smaller (a b : Nat) (h : Nat.blt a b = true) : a < b :=
  Eq.mp Nat.blt_eq h

/-- This uncompiled driver draft proves each slice for a generic base,
    using only the stable global directory plus separately parsed exact
    row/hint data. No earlier proof- or original-row membership module
    is needed to check a slice. -/
elab "global_rup " resultName:ident loTok:num data:term:max : command => do
  let ns ← getCurrNamespace
  liftTermElabM do
    let lo := loTok.getNat
    let dataTy ← elabType (← `(Array (Nat × Nat × Array Int × Array (Nat × Array Int))))
    let additions ← unsafe evalTerm (Array (Nat × Nat × Array Int × Array (Nat × Array Int))) dataTy data
    unless 0 < additions.size && additions.size ≤ 24 do throwError "bad slice size"
    let rowAtExpr := Lean.mkConst ``rowAt
    let st (core : Expr) (bound : Nat) :=
      mkAppN (Lean.mkConst ``GoodBelow) #[core, rowAtExpr, mkNatLit bound]
    let (proof,ty) ← withLocalDeclD `core (Lean.mkConst ``Sat.Fmla) fun core => do
      let mut steps : Array Expr := #[]
      let mut hTypes : Array Expr := #[]
      for k in [:additions.size] do
        let (id,step,lits,hints) := additions[k]!
        unless step == lo+k && step < 13910 && !hints.isEmpty &&
          hints.size ≤ 900 && lits.size ≤ 108 do throwError "bad step metadata at {id}"
        hTypes := hTypes.push (← mkArrow (st core step)
          (mkApp2 (Lean.mkConst ``Sat.Fmla.proof) core (mkApp rowAtExpr (mkNatLit step))))
        let proof ← withLocalDeclD `ready (st core step) fun ready => do
          let mut db : Std.HashMap Nat Mathlib.Tactic.Sat.Clause := {}
          let refl ← mkEqRefl (Lean.mkConst ``Bool.true)
          let mut reindexed : Array Int := #[]
          for (slot,clause) in hints do
            unless slot < step do throwError "non-past slot at {id}"
            let lt := mkApp3 (Lean.mkConst ``smaller) (mkNatLit slot) (mkNatLit step) refl
            let premise : Mathlib.Tactic.Sat.Clause := {
              lits := clause
              expr := buildClause clause
              proof := mkApp2 ready (mkNatLit slot) lt
            }
            db := db.insert slot premise
            reindexed := reindexed.push (Int.ofNat slot)
          let .ok term := buildProofStep db lits reindexed core (buildClause lits)
            | throwError "invalid RUP at {id}"
          mkLambdaFVars #[ready] term
        steps := steps.push (← mkLambdaFVars #[core] proof)
      let mut applied : Array Expr := #[]
      for k in [:steps.size] do
        let (id,slot,_,_) := additions[k]!
        let thm := ns ++ resultName.getId ++ Name.mkSimple s!"step_{id}"
        let ty ← mkForallFVars #[core] hTypes[k]!
        addDecl <| .thmDecl { name := thm, levelParams := [], type := ty, value := steps[k]! }
        applied := applied.push (mkAppN (Lean.mkConst ``extend)
          #[core,rowAtExpr,mkNatLit slot,mkApp (Lean.mkConst thm) core])
      let mut proof := applied[0]!
      for k in [1:applied.size] do
        proof := mkAppN (Lean.mkConst ``compose)
          #[core,rowAtExpr,mkNatLit lo,mkNatLit (lo+k),mkNatLit (lo+k+1),proof,applied[k]!]
      let ty := mkAppN (Lean.mkConst ``Slice)
        #[core,rowAtExpr,mkNatLit lo,mkNatLit (lo+applied.size)]
      return (← mkLambdaFVars #[core] proof, ← mkForallFVars #[core] ty)
    addDecl <| .thmDecl { name := ns ++ resultName.getId, levelParams := [], type := ty, value := proof }

end Euler.C14.Production
