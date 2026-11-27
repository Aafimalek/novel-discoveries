import EulerAllUsedFullGeometry
import Mathlib.Tactic.Sat.FromLRAT

open Lean Elab Command Term Meta

namespace Euler.ArchivedDeclarationAudit

/-- An exact metaprogram audit of the *loaded definition* that the kernel
refutation references. This command adds no theorem to the environment. -/
private partial def walk (rows : Array (List Int)) (decl : Expr) (pos : Nat) :
    MetaM Nat := do
  if let .const id _ := decl then
    let .defnInfo val ← getConstInfo id | throwError "Expected loaded formula definition {id}"
    return ← walk rows val.value pos
  if decl.isAppOfArity ``Sat.Fmla.one 1 then
    let some row := rows[pos]? | throwError "Formula has more than {rows.size} rows"
    let reified := Mathlib.Tactic.Sat.buildClause row.toArray
    unless reified == decl.appArg! do
      throwError "Exact expression for clause #{pos+1} differs from modeled signed clause {row}"
    return pos+1
  if decl.isAppOfArity ``Sat.Fmla.and 2 then
    let pos' ← walk rows decl.appFn!.appArg! pos
    return ← walk rows decl.appArg! pos'
  throwError "Unexpected constructor in loaded checked formula at row {pos+1}"

elab "audit_loaded_archive " f:ident pf:ident ppSpace data:term : command =>
  Command.liftTermElabM do
    let refutation ← getConstInfo pf.getId
    let .thmInfo _ := refutation | throwError "Expected an existing kernel theorem"
    let expectedType := mkApp2 (mkConst ``Sat.Fmla.proof) (mkConst f.getId) (mkConst ``Sat.Clause.nil)
    unless refutation.type == expectedType do
      throwError "The selected kernel theorem refutes a different definition: {refutation.type}"
    let codes ← unsafe evalTerm (List Nat) (mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat)) data
    let rows := (LatinGap.PairEncoding.archiveAllUsedCNF codes).toArray
    let m ← walk rows (mkConst f.getId) 0
    unless m == rows.size do
      throwError "Model has {rows.size} rows; checked formula has {m}"
    logInfo m!"{f.getId}: matched {m} ordered clauses against the actual definition refuted by {pf.getId}; codes {codes}"

end Euler.ArchivedDeclarationAudit
