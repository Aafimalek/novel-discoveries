import EulerC14IndexedInitialize

open Lean Elab Command Term Meta
open Mathlib.Tactic.Sat

namespace Euler.C14.IndexedDraft

set_option maxRecDepth 12000
set_option maxHeartbeats 2400000

theorem subsumes_nil (f : Sat.Fmla) : f.subsumes [] :=
  ⟨fun _ h => False.elim (List.not_mem_nil h)⟩

theorem subsumes_cons (f : Sat.Fmla) (r : Sat.Clause) (rs : Sat.Fmla)
    (hr : f.subsumes (Sat.Fmla.one r)) (hrs : f.subsumes rs) :
    f.subsumes (r :: rs) :=
  ⟨fun c h => (List.mem_cons.mp h).elim
    (fun e => hr.1 c (List.mem_singleton.mpr e))
    (hrs.1 c)⟩

private partial def rowSub (ctx : Expr) (lo hi index : Nat) (f p : Expr) : Expr × Expr :=
  if hi - lo = 1 then (f.appArg!, p)
  else
    let mid := lo + (hi - lo) / 2
    let left := f.appFn!.appArg!
    let right := f.appArg!
    if index < mid then
      rowSub ctx lo mid index left (mkApp4 (mkConst ``Sat.Fmla.subsumes_left) ctx left right p)
    else
      rowSub ctx mid hi index right (mkApp4 (mkConst ``Sat.Fmla.subsumes_right) ctx left right p)

elab "archived_subsumes " coreName:ident resultName:ident target:ident cnf:term:max ids:term:max : command => do
  let ns ← getCurrNamespace
  liftTermElabM do
    let input ← unsafe evalTerm String (mkConst ``String) cnf
    let it ← elabType (← `(Array Nat))
    let ids ← unsafe evalTerm (Array Nat) it ids
    let .success stop (vars, rows) := Parser.parseDimacs ⟨_, input.startPos⟩
      | throwError "DIMACS parse failed"
    unless decide stop.2.IsAtEnd do throwError "unparsed DIMACS suffix"
    unless vars == 10646 && rows.size == 8825 && ids.size == 135 do
      throwError "unexpected C14 source or local slot count"
    let target := Lean.mkConst (ns ++ target.getId)
    let name := ns ++ coreName.getId
    let ctx := Lean.mkConst name
    let fmla := buildConj rows 0 rows.size
    addDecl <| .defnDecl {
      name := name
      levelParams := []
      type := mkConst ``Sat.Fmla
      value := fmla
      hints := .regular 0
      safety := .safe
    }
    let root := mkApp (mkConst ``Sat.Fmla.subsumes_self) ctx
    let mut list := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Sat.Clause)
    let mut proof := mkApp (mkConst ``subsumes_nil) ctx
    for (i,id) in ids.toList.zipIdx.reverse do
      unless i > 0 && i ≤ rows.size do throwError "invalid original ID {i}"
      let (row,p) := rowSub ctx 0 rows.size (i - 1) fmla root
      let memberName := ns ++ Name.mkSimple s!"archived_selected_{id}"
      let memberTy := mkApp2 (mkConst ``Sat.Fmla.subsumes) ctx (mkApp (mkConst ``Sat.Fmla.one) row)
      addDecl <| .thmDecl { name := memberName, levelParams := [], type := memberTy, value := p }
      proof := mkAppN (mkConst ``subsumes_cons) #[ctx,row,list,mkConst memberName,proof]
      list := mkAppN (mkConst ``List.cons [Level.zero]) #[mkConst ``Sat.Clause,row,list]
    let ty := mkApp2 (mkConst ``Sat.Fmla.subsumes) ctx target
    addDecl <| .thmDecl { name := ns ++ resultName.getId, levelParams := [], type := ty, value := proof }

end Euler.C14.IndexedDraft
