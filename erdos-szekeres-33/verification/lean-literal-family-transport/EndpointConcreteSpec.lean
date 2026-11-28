/-
DRAFT: precise executable endpoint content specification.
No Lean compile of this source has been run. No sorry or asserted theorem.
A separate checkpoint source states the intended small exact check.
-/
import NumberedCNF
import EndpointBaseAliases

namespace ES33.EndpointConcrete

open ES33.Numbering

abbrev Key := EndpointVar
abbrev Cell (n : Nat) := Lit (Key n)

inductive Side | cap | cup
  deriving DecidableEq, Repr

def inclusive (lo hi : Nat) : List Nat :=
  (List.range (hi+1-lo)).map fun d => d+lo

def pairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun a =>
    ((List.finRange n).filter fun b => decide (a<b)).map fun b => (a,b)

def triples (n : Nat) : List (Fin n × Fin n × Fin n) :=
  (pairs n).flatMap fun (a,b) =>
    ((List.finRange n).filter fun c => decide (b<c)).map fun c => (a,b,c)

def packets (n : Nat) : List (Fin n × Fin n × Fin n × Fin n) :=
  (triples n).flatMap fun (a,b,c) =>
    ((List.finRange n).filter fun e => decide (c<e)).map fun e => (a,b,c,e)

def sign {n : Nat} (a b c : Fin n) (p : Bool := true) : Cell n :=
  ⟨.sign a b c,p⟩

def pairKey {n : Nat} (side : Side) (d : Nat) (a c : Fin n) : Key n :=
  match side with
  | .cap => .capPair d a c
  | .cup => .cupPair d a c

def stateKey {n : Nat} (side : Side) (d : Nat) (a b c : Fin n) : Key n :=
  match side with
  | .cap => .capLast d a b c
  | .cup => .cupFirst d a b c

def pairLit {n : Nat} (side : Side) (d : Nat) (a c : Fin n) : Cell n :=
  ⟨pairKey side d a c,true⟩

def stateLit {n : Nat} (side : Side) (d : Nat) (a b c : Fin n) : Cell n :=
  if d=3 then sign a b c (decide (side=.cup))
  else ⟨stateKey side d a b c,true⟩

def flip {n : Nat} (l : Cell n) : Cell n := ⟨l.var,!l.pos⟩

def width2 {n : Nat} (a c : Fin n) : Nat := c.val-a.val+1

def width3 {n : Nat} (side : Side) (a b c : Fin n) : Nat :=
  match side with
  | .cap => b.val-a.val+2
  | .cup => c.val-b.val+2

def sideDictionary (n limit : Nat) (side : Side) : List (Key n) :=
  ((pairs n).flatMap fun (a,c) =>
    (inclusive 2 (min limit (width2 a c))).map fun d => pairKey side d a c) ++
  ((triples n).flatMap fun (a,b,c) =>
    (inclusive 4 (min limit (width3 side a b c))).map fun d => stateKey side d a b c)

def dictionary (n A B : Nat) : List (Key n) :=
  (triples n).map (fun (a,b,c) => .sign a b c) ++
    sideDictionary n A .cap ++ sideDictionary n B .cup

/-- Rows occur in the production order, not just as a set. -/
def pairRows {n : Nat} (side : Side) (limit : Nat) (a c : Fin n) : CNF (Key n) :=
  [[pairLit side 2 a c]] ++
  (if limit ≤ width2 a c then [[flip (pairLit side limit a c)]] else []) ++
  (inclusive 3 (min limit (width2 a c))).map
    (fun d => [flip (pairLit side d a c),pairLit side (d-1) a c])

def stepRows {n : Nat} (side : Side) (d : Nat) (a b c : Fin n) : CNF (Key n) :=
  match side with
  | .cap =>
    ((List.finRange n).filter fun e => decide (c<e)).map fun e =>
      [flip (stateLit .cap d a b c),sign b c e,stateLit .cap (d+1) a c e]
  | .cup =>
    ((List.finRange n).filter fun e => decide (e<a)).map fun e =>
      [flip (stateLit .cup d a b c),sign e a b false,stateLit .cup (d+1) e a c]

def tripleRows {n : Nat} (side : Side) (limit : Nat) (a b c : Fin n) : CNF (Key n) :=
  (inclusive 3 (min limit (width3 side a b c))).flatMap fun d =>
    [[flip (stateLit side d a b c),pairLit side d a c]] ++
      (if d<limit then stepRows side d a b c else [])

def sideRows (n limit : Nat) (side : Side) : CNF (Key n) :=
  ((pairs n).flatMap fun (a,c) => pairRows side limit a c) ++
    ((triples n).flatMap fun (a,b,c) => tripleRows side limit a b c)

def crossRows (n K A B : Nat) : CNF (Key n) :=
  (pairs n).flatMap fun (a,c) =>
    (inclusive 2 K).filterMap fun s =>
      let t := K+2-s
      if s ≤ min A (width2 a c) ∧ 2 ≤ t ∧ t ≤ min B (width2 a c) then
        some [flip (pairLit .cap s a c),flip (pairLit .cup t a c)]
      else none

def packetRows {n : Nat} (a b c e : Fin n) : CNF (Key n) :=
  let p := sign a b c
  let q := sign a b e
  let r := sign a c e
  let s := sign b c e
  [[flip p,flip s,q],[flip q,flip s,r],[flip p,flip r,q],
   [p,s,flip q],[q,s,flip r],[p,r,flip q]]

def typedRows (n K A B : Nat) : CNF (Key n) :=
  sideRows n A .cap ++ sideRows n B .cup ++ crossRows n K A B ++
    (packets n).flatMap (fun (a,b,c,e) => packetRows a b c e)

/-- Tiny/reference executable only: missing names receive index length+1,
which makes the token parser fail. Do not use this linear lookup for 32. -/
def referenceTokens (n K A B : Nat) : TokenDocument :=
  let T := dictionary n A B
  TokenDocument.emit T.length (encode (fun v => T.idxOf v+1) (typedRows n K A B))

namespace VerificationGoals

/-- The exact prerequisites needed to use generic proof transport. -/
def covered (n K A B : Nat) : Prop :=
  Supports (dictionary n A B) (typedRows n K A B)

def duplicateFree (n A B : Nat) : Prop := (dictionary n A B).Nodup

/-- Four monotone signs, in either direction, on each ordered quartet. -/
def signotope (n : Nat) (χ : Fin n → Fin n → Fin n → Bool) : Prop :=
  ∀ a b c e, a<b → b<c → c<e →
    let p := χ a b c
    let q := χ a b e
    let r := χ a c e
    let s := χ b c e
    (p≤q ∧ q≤r ∧ r≤s) ∨ (s≤r ∧ r≤q ∧ q≤p)

def signVal {n : Nat} (v : Key n → Bool) (a b c : Fin n) : Bool :=
  v (.sign a b c)

def stateVal {n : Nat} (v : Key n → Bool) : ES33.EndpointGuard.States n where
  capLast d a b c := v (.capLast d a b c) = true
  cupFirst d a b c := v (.cupFirst d a b c) = true
  capPair d a c := v (.capPair d a c) = true
  cupPair d a c := v (.cupPair d a c) = true

/-- Exact correctness target, NOT asserted. The left side is the actual
ordered list above; the right side is independently defined mathematics. -/
def semantics (n K A B : Nat) : Prop :=
  ∀ v : Key n → Bool,
    Satisfies v (typedRows n K A B) ↔
      (signotope n (signVal v) ∧
       ES33.EndpointGuard.PrunedPropagation (signVal v) A B
         (ES33.EndpointGuard.baseAliases (signVal v) (stateVal v)) ∧
       ES33.EndpointGuard.PrunedExclusions K A B
         (ES33.EndpointGuard.baseAliases (signVal v) (stateVal v)))

/-- Target is evaluated on the certificate checker's exact loaded object,
not on a matching count, name, or SHA string. Actual relation is open. -/
def content32 (t : TokenDocument) (h : covered 32 7 7 6) : Prop :=
  t.numVars = 37365 ∧ t.numClauses = 474144 ∧
  t.parse = some
    (compile (dictionary 32 7 6) (typedRows 32 7 7 6) h)

end VerificationGoals

end ES33.EndpointConcrete
