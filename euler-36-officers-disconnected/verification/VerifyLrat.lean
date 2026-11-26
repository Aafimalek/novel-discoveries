import Std.Data.HashMap
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

/-!
# Replay the Euler SAT certificates in Lean

The generator exports one clause per line and uses standard one-based
DIMACS literals. Lean's CNF uses zero-based atoms. The LRAT checker
applies the same conversion to the proof literals.
-/

open Std.Sat
open Std.Tactic.BVDecide

/-- Split a generated DIMACS line into its space-separated fields. -/
private def fields (line : String) : List String :=
  (line.trimAscii.toString.splitOn " ").filter (· != "")

/-- Read one clause and check that each literal is in the header's range. -/
private def parseClause (variables : Nat) (line : String) :
    Except String (CNF.Clause Nat) := do
  match (fields line).reverse with
  | "0" :: literals =>
    literals.reverse.foldlM (init := CNF.Clause.empty) fun clause token => do
      let some literal := token.toInt? | throw s!"invalid literal {token}"
      let atom := literal.natAbs
      if atom = 0 || atom > variables then
        throw s!"literal {literal} outside the header's variable range"
      return clause.add (atom - 1) (literal > 0)
  | _ => throw "clause is missing its zero terminator"

/-- Read the exact, one-clause-per-line DIMACS format written by PySAT. -/
def parseCNF (input : String) : Except String (CNF Nat) := do
  let header :: clauses := (input.splitOn "
").filter
    (fun line => !(fields line).isEmpty) | throw "missing DIMACS header"
  let ["p", "cnf", variables, count] := fields header | throw "invalid DIMACS header"
  let some variables := variables.toNat? | throw "invalid variable count"
  let some count := count.toNat? | throw "invalid clause count"
  if clauses.length != count then
    throw "DIMACS header and actual clause count differ"
  clauses.foldlM (init := CNF.emptyWithCapacity count) fun f line => do
    return f.add (← parseClause variables line)


/-- Resolve an LRAT reference against the original clauses or earlier proof steps. -/
private def clauseIndex (original : Nat) (indices : Std.HashMap Nat Nat)
    (id : Nat) : Except String Nat :=
  if id = 0 then
    .error "LRAT references clause zero"
  else if id ≤ original then
    .ok id
  else
    match indices[id]? with
    | some dense => .ok dense
    | none => .error s!"LRAT references unknown clause {id}"

/-- DRAT-trim can leave gaps between proof clause IDs. Rename each added
clause and its later references to the consecutive IDs expected by Lean. -/
private def renumber (original : Nat) (proof : Array LRAT.IntAction) :
    Except String (Array LRAT.IntAction) := do
  let mut result := Array.emptyWithCapacity proof.size
  let mut indices : Std.HashMap Nat Nat := {}
  let mut next := original + 1
  for step in proof do
    let resolve := clauseIndex original indices
    match step with
    | .del ids =>
      result := result.push (.del (← ids.mapM resolve))
    | .addEmpty _ hints =>
      result := result.push (.addEmpty next (← hints.mapM resolve))
      return result
    | .addRup id clause hints =>
      result := result.push (.addRup next clause (← hints.mapM resolve))
      indices := indices.insert id next
      next := next + 1
    | .addRat id clause pivot hints ratHints =>
      let ratHints ← ratHints.mapM fun (source, sources) => do
        return (← resolve source, ← sources.mapM resolve)
      result := result.push (.addRat next clause pivot (← hints.mapM resolve) ratHints)
      indices := indices.insert id next
      next := next + 1
  return result

/-- Turn a successful replay into the proposition that the CNF is unsatisfiable. -/
theorem replay_sound (proof : Array LRAT.IntAction) (cnf : CNF Nat)
    (verified : LRAT.check proof cnf = true) : cnf.Unsat :=
  LRAT.check_sound proof cnf verified

/-- Load each named CNF and replay its LRAT certificate with Lean's checker. -/
def main (args : List String) : IO Unit := do
  let directory :: names := args | throw (IO.userError "expected a directory and case names")
  if names.isEmpty then
    throw (IO.userError "expected at least one case name")
  for name in names do
    let base := (System.FilePath.mk directory) / name
    let input ← IO.FS.readFile (base.addExtension "cnf")
    let cnf ← IO.ofExcept (parseCNF input)
    let proof ← LRAT.loadLRATProof (base.addExtension "lrat")
    let proof ← IO.ofExcept (renumber cnf.clauses.size proof)
    if LRAT.check proof cnf then
      IO.println s!"{name}: Lean LRAT verified ({cnf.clauses.size} clauses)"
    else
      throw (IO.userError s!"{name}: Lean LRAT rejected the certificate")
