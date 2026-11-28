/- Static draft: canonical six-row text parsing, independent of any dictionary. -/
import NumberedCNF

namespace ES33.ExternalPacketPilot

open ES33.Numbering

private def splitChar (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c::cs =>
    let tail := splitChar sep cs
    if c=sep then []::tail else
      match tail with
      | [] => [[c]]
      | h::t => (c::h)::t

private def decimal (c : Char) : Option Nat :=
  let n := c.toNat
  if 48≤n ∧ n≤57 then some (n-48) else none

private def natToken : List Char → Option Nat
  | [] => none
  | c::cs =>
    if c='0' ∧ cs≠[] then none
    else List.foldlM
      (fun acc d => do return 10*acc + (← decimal d)) 0 (c::cs)

private def intToken : List Char → Option Int
  | '-'::cs => do
    let n ← natToken cs
    if n=0 then none else some (-(Int.ofNat n))
  | cs => Int.ofNat <$> natToken cs

private def parseChars (vars rows : Nat) (cs : List Char) : Option NumberedCNF :=
  match (splitChar '\n' cs).reverse with
  | [] => none
  | last::rev =>
    if last≠[] then none else do
      let tokens ← rev.reverse.mapM (fun row => (splitChar ' ' row).mapM intToken)
      (⟨vars,rows,tokens⟩ : TokenDocument).parse

/-- Strict no-comments, one-space, decimal clause-body frontend for this pilot.
This does not parse or assert the full original DIMACS header/file. -/
noncomputable def parseBodyChunk (vars rows : Nat) (s : String) : Option NumberedCNF :=
  parseChars vars rows s.toList

def body : String := include_str "first-packet.rows"

-- This cache is tied to the actual embedded string by kernel equality below;
-- it replaces only UTF-8 decoding, not decimal tokenization or row parsing.
private def asciiWitness : List Char := [
  '-', '1', ' ', '-', '4', '6', '6', ' ', '2', ' ', '0', '\n',
  '-', '2', ' ', '-', '4', '6', '6', ' ', '3', '1', ' ', '0', '\n',
  '-', '1', ' ', '-', '3', '1', ' ', '2', ' ', '0', '\n',
  '1', ' ', '4', '6', '6', ' ', '-', '2', ' ', '0', '\n',
  '2', ' ', '4', '6', '6', ' ', '-', '3', '1', ' ', '0', '\n',
  '1', ' ', '3', '1', ' ', '-', '2', ' ', '0', '\n']

def expected : NumberedCNF :=
  [[-1,-466,2],[-2,-466,31],[-1,-31,2],[1,466,-2],[2,466,-31],[1,31,-2]]

set_option maxRecDepth 4096 in
theorem body_is_asciiWitness : body = String.ofList asciiWitness := by decide

set_option maxRecDepth 4096 in
theorem parsed_body : parseBodyChunk 37365 6 body = some expected := by
  rw [body_is_asciiWitness]
  unfold parseBodyChunk
  rw [String.toList_ofList]
  decide

#print axioms body_is_asciiWitness
#print axioms parsed_body

end ES33.ExternalPacketPilot
