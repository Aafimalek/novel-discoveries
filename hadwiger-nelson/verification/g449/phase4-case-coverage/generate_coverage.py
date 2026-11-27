#!/usr/bin/env python3
"""Generate a finite coverage certificate for Heule–Przybocki's case split.

Independent witness generation from the six published case patterns. Lean
checks each supplied witness, rather than trusting the generator.
"""
from itertools import permutations,product
from pathlib import Path

RULES=['2222222','2223...','2232..-','223-2--','223--2-','232-2--']
PERMS=list(permutations(range(3)))
WORDS=list(product(range(3),repeat=7))
STATE=3**7
def tr(w,r,p):
    return tuple(PERMS[p][w[(i+r)%7]] for i in range(7))
def canon(w):
    return min(tr(w,r,p) for r in range(7) for p in range(6))
def matches(w,j):
    return all(s=='.' or (s=='-' and x!=0) or (s.isdigit() and x==int(s)-2)
               for s,x in zip(RULES[j],w))
def code(w):
    return sum(c*3**i for i,c in enumerate(w))
seen=set()
forests=[[] for _ in RULES]
accepted={}
signatures={w:canon(w) for w in WORDS}
for case in (0,1,2,4,3,5):
    for w in WORDS:
       if not matches(w,case):continue
       s=signatures[w]
       if s in seen:forests[case].append(code(w))
       else: 
           seen.add(s)
           accepted[w]=case
assert len(accepted)==53 and len(set(signatures.values()))==53
assert [len(x) for x in forests]==[0,2,4,4,3,4]
hints=[None]*STATE
for w in WORDS:
    chosen=None
    for r,p in product(range(7),range(6)):
        target=tr(w,r,p)
        if target in accepted:
            c=accepted[target]
            assert matches(target,c) and code(target) not in forests[c]
            chosen=c*42+r*6+p
            break
    assert chosen is not None
    hints[code(w)] = chosen

def arr(v):return '['+', '.join(map(str,v))+']'
def leb(v):
    return '['+', '.join(arr(x) for x in v)+']'
out='''import Init

namespace G449FiniteCoverage

/-- The ith original label in base 3; labels 0,1,2 stand for colours 2,3,4. -/
def label (w i : Nat) : Nat := (w / 3^i) % 3

def perms : List (List Nat) := '''+leb(PERMS)+'''
def rule : List (List Nat) := '''+leb([[3 if s=='.' else 4 if s=='-' else int(s)-2 for s in v] for v in RULES])+'''
def exclusions : List (List Nat) := '''+leb(forests)+'''

def perm (p a : Nat) : Nat := (perms.getD p []).getD a 0

def transform (w r p : Nat) : Nat :=
  ((List.range 7).map fun i => perm p (label w ((i+r)%7)) * 3^i).sum

def isMatch (c w : Nat) : Bool :=
  (List.range 7).all fun i =>
    let req := (rule.getD c []).getD i 3
    if req == 3 then true else if req == 4 then label w i != 0 else label w i == req

def allowed (c w : Nat) : Bool :=
  isMatch c w && !(exclusions.getD c []).contains w

def witnessOK (w h : Nat) : Bool :=
  let c := h / 42
  let r := (h % 42) / 6
  let p := h % 6
  decide (c < 6) && decide (r < 7) && decide (p < 6) && allowed c (transform w r p)

def checkBlock (offset count packed : Nat) : Bool :=
  (List.range count).all fun i => witnessOK (offset+i) ((packed / 256^i)%256)

theorem witnessOK_sound (w h : Nat) (chk : witnessOK w h = true) :
    ∃ c r p, c < 6 ∧ r < 7 ∧ p < 6 ∧ allowed c (transform w r p) = true := by
  unfold witnessOK at chk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at chk
  exact ⟨h/42,(h%42)/6,h%6,chk.1.1.1,chk.1.1.2,chk.1.2,chk.2⟩

theorem checkBlock_sound (offset count packed i : Nat)
    (h : checkBlock offset count packed = true) (hi : i < count) :
    ∃ c r p, c < 6 ∧ r < 7 ∧ p < 6 ∧ allowed c (transform (offset+i) r p) = true :=
  witnessOK_sound _ _ (List.all_eq_true.mp h i (List.mem_range.mpr hi))
'''
width=81
for b in range(0,STATE,width):
    pck=sum(hints[b+i]*256**i for i in range(width))
    out+=f'''
set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem block{b} : checkBlock {b} {width} {pck} = true := by decide +kernel
'''
out+='''
/-- Every raw seven-neighbour assignment, modulo rotation and relabelling
the three noncentral colours, satisfies an allowed branch pattern. -/
theorem orbit_case_coverage (w : Nat) (hw : w < 2187) :
    ∃ c r p, c < 6 ∧ r < 7 ∧ p < 6 ∧ allowed c (transform w r p) = true := by
'''
for b in range(0,STATE,width):
    out+=f'''  by_cases h{b} : w < {b+width}
  · have m := checkBlock_sound {b} {width} _ (w-{b}) block{b} (by omega)
    rwa [show {b}+(w-{b})=w by omega] at m
'''
out+='  omega\n\n'
out+='''
set_option maxRecDepth 32768 in
set_option maxHeartbeats 20000000 in
theorem accepted_patterns_count :
    ((List.range 2187).filter fun w => (List.range 6).any fun c => allowed c w).length = 53 := by decide +kernel

#print axioms orbit_case_coverage
#print axioms accepted_patterns_count
end G449FiniteCoverage
'''
Path('FiniteCaseCoverage.lean').write_text(out)
print('Generated 2,187 witnesses; allowed patterns =', len(accepted), 'exclusions =', list(map(len,forests)))
