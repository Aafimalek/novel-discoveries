from pathlib import Path
import json, sys
a = int(sys.argv[1])
data_file = sys.argv[2] if len(sys.argv)>2 else 'fourpoint-data.json'
D={e['parity']:e for e in json.load(open(data_file)) if e['a']==a}
assert set(D)=={0,1}
B=min(e['bound'] for e in D.values())
import math
R=max(math.isqrt(max(0,(e['lambda']+3)//4-148**2-a*a))+1 for e in D.values())
step=math.ceil(R/4)
d=Path('NineSeparatedSubsetSums')
def put(n,s): (d/(n+'.lean')).write_text(s)
header=lambda n: f'import NineSeparatedSubsetSums.{n}\nopen scoped BigOperators\nnamespace NineSeparatedSubsetSums\n'
tail='\nend NineSeparatedSubsetSums\n'
options='set_option maxRecDepth 32768 in\nset_option maxHeartbeats 50000000 in\n'
s=header('FourPointSymmetry')
for p,e in sorted(D.items()):
    v=dict(e['penalty']); arr=[v.get(i,0) for i in range(max(v)+1)]
    body=',\n    '.join(', '.join(map(str,arr[i:i+16])) for i in range(0,len(arr),16))
    s+=f'def fourPoint{a}Table{p} : Array ℕ := #[\n    {body}\n]\n'
put(f'FourPoint{a}Tables',s+tail)
print(f'FourPoint{a}Tables')
modules=[]
for p,e in sorted(D.items()):
    lam=e['lambda']; budget=e['budget']
    for i,o in enumerate(range(0,4*step,step)):
        w=R-o if i==3 else step
        m=f'FourPoint{a}Anchor{p}Part{i}'; modules.append(m)
        put(m,header(f'FourPoint{a}Tables')+f'''{options}
theorem fourPoint{a}Anchor{p}Part{i} :
    ∀ j : Fin {w}, ((j.val : ℤ)+{o}+{a})%2={p} →
      {lam} ≤ blockCharge {a} (fun z => z^2+fourPointLookupPenalty fourPoint{a}Table{p} z)
        ((j.val : ℤ)+{o}) := by decide +kernel
#print axioms fourPoint{a}Anchor{p}Part{i}
'''+tail)
    m=f'FourPoint{a}Budget{p}'; modules.append(m)
    put(m,header(f'FourPoint{a}Tables').replace('open scoped', 'import NineSeparatedSubsetSums.FourPointBudget\nopen scoped')+f'''{options}
theorem fourPoint{a}Budget{p} :
    (∑ z ∈ fourPointLookupBox fourPoint{a}Table{p},
      fourPointLookupPenalty fourPoint{a}Table{p} z) = {budget} := by rw [fourPointLookupBudget_eq]; decide +kernel
#print axioms fourPoint{a}Budget{p}
'''+tail)
s=''.join('import NineSeparatedSubsetSums.'+m+'\n' for m in modules)+'''
open scoped BigOperators
namespace NineSeparatedSubsetSums
'''
for p,e in sorted(D.items()):
    lam=e['lambda']
    s+=f'''
theorem fourPoint{a}PositiveAnchor{p} :
    ∀ j : Fin {R}, ((j.val : ℤ)+{a})%2={p} →
      {lam} ≤ blockCharge {a} (fun z => z^2+fourPointLookupPenalty fourPoint{a}Table{p} z)
        (j.val : ℤ) := by
  intro j hp
  by_cases h₀ : j.val < {step}
  · let k : Fin {step} := ⟨j.val, h₀⟩
    simpa [k] using fourPoint{a}Anchor{p}Part0 k (by simpa [k] using hp)
  by_cases h₁ : j.val < {2*step}
  · let k : Fin {step} := ⟨j.val-{step}, by omega⟩
    have E : (k.val : ℤ)+{step} = j.val := by dsimp [k]; omega
    have eq := fourPoint{a}Anchor{p}Part1 k
    rw [E] at eq
    exact eq hp
  by_cases h₂ : j.val < {3*step}
  · let k : Fin {step} := ⟨j.val-{2*step}, by omega⟩
    have E : (k.val : ℤ)+{2*step} = j.val := by dsimp [k]; omega
    have eq := fourPoint{a}Anchor{p}Part2 k
    rw [E] at eq
    exact eq hp
  · have hj := j.isLt
    let k : Fin {R-3*step} := ⟨j.val-{3*step}, by omega⟩
    have E : (k.val : ℤ)+{3*step} = j.val := by dsimp [k]; omega
    have eq := fourPoint{a}Anchor{p}Part3 k
    rw [E] at eq
    exact eq hp

def fourPoint{a}Certificate{p} : FourPointCertificate {a} {p} {B} :=
  fourPointCertificateOfTable {a} {p} {B} {lam} fourPoint{a}Table{p} (by decide)
    (fun j hj => blockCharge_check_from_positive_window {a} {lam} {p}
      (fourPointLookupPenalty fourPoint{a}Table{p}) (fun _ => Int.natCast_nonneg _)
      (fourPointLookupPenalty_neg fourPoint{a}Table{p}) {R} (by decide)
      fourPoint{a}PositiveAnchor{p} ((j.val : ℤ)-800) hj)
    (by rw [fourPoint{a}Budget{p}]; decide)
'''
s+=f'''
/-- Both exact parity certificates imply this fixed strong cutoff. -/
theorem max148_second{a}_fourPoint_moment_bound (tail : List ℕ) (len : tail.length=7)
    (distinct : (natSubsetSums (148::{a}::tail)).Nodup) :
    {B} ≤ ((148::{a}::tail).map (· ^ 2)).sum := by
  apply fourPointNatMomentLower {a} {B} tail len distinct
  intro p hp
  by_cases h : p=0
  · subst p
    exact fourPoint{a}Certificate0
  · have he : p=1 := hp.resolve_left h
    subst p
    exact fourPoint{a}Certificate1

#print axioms max148_second{a}_fourPoint_moment_bound
'''
put(f'FourPoint{a}Checked',s+tail)
print(*modules,f'FourPoint{a}Checked')
