"""Produce parity-split packed numeric certificates and single geometric glue."""
import sys, json, math
from pathlib import Path
A,C=map(int,sys.argv[1:3])
T=f"{A}_{C}"
data=json.loads(Path(sys.argv[3] if len(sys.argv)>3 else 'fourpoint-data.json').read_text())
D={e['parity']:e for e in data if e['a']==A and e['b']==C};assert set(D)=={0,1}
B=min(d['bound'] for d in D.values())
R=max(math.isqrt(max(0,(d['lambda']+7)//8-148**2-A*A-C*C))+1 for d in D.values())
N='EightPoint'+T
folder=Path('NineSeparatedSubsetSums')
def open_(imports):
    return ''.join(f'import NineSeparatedSubsetSums.{src}\n' for src in imports)+'\nnamespace NineSeparatedSubsetSums\n'
def save(name,text):
    (folder/(name+'.lean')).write_text(text+'\nend NineSeparatedSubsetSums\n')
    return name
opts='set_option maxRecDepth 32768 in\nset_option maxHeartbeats 70000000 in\n'
names=[]
core=open_(['EightPointNumeric'])
data={}
for p,d in sorted(D.items()):
    mu=dict(d['penalty']); W=max(mu.values()).bit_length(); size=max(mu)+1
    value=sum(c<<(W*i) for i,c in mu.items()); var=f'packedOct{T}_{p}'
    core+=f'def {var} : Nat := {hex(value)}\n'
    start=(p-A-C)%2; K=(R+1-start)//2
    data[p]=(W,size,var,start,K,d['lambda'],d['budget'])
names+=[save(N+'PackedTables',core)]
checked=''
certificate=''
for p,(W,size,var,start,K,lam,budget) in data.items():
    n=N+f'PackedBudget{p}'
    names+=[save(n,open_([N+'PackedTables'])+f'''
{opts}theorem packedOct{T}_{p}_budget :
    FourPointNumeric.packedBudget {W} {var} {size} = {budget} := by decide +kernel

#print axioms packedOct{T}_{p}_budget
''')]
    # Every numeric chunk visits only the correct parity, no wasted lookup checks.
    splits=[]
    width=120
    for off in range(0,K,width):
        j=len(splits); w=min(width,K-off); n=N+f'PackedAnchor{p}Part{j}'
        splits.append((off,w,n))
        names+=[save(n,open_([N+'PackedTables'])+f'''
{opts}theorem {n[0].lower()+n[1:]} :
    ∀ j : Fin {w}, {lam} ≤ FourPointNumeric.octPackedCharge {A} {C} {W} {var}
      (2*((j.val : Int)+{off})+{start}) := by decide +kernel
''')]
    line=f'''
private theorem packedOct{T}Anchor{p} :
  ∀ j : Fin {R}, ((j.val : Int)+{A}+{C})%2={p} →
    {lam} ≤ FourPointNumeric.octPackedCharge {A} {C} {W} {var} (j.val : Int) := by
  intro j hj
  let k := (j.val-{start})/2
  have hk : k < {K} := by dsimp [k]; have h := j.isLt; omega
  have hrep : 2*(k : Int)+{start} = j.val := by dsimp [k]; omega
'''
    for i,(off,w,n) in enumerate(splits):
        th=n[0].lower()+n[1:]
        last=i==len(splits)-1
        if not last:
            line+=f'  by_cases h{i} : k < {off+w}\n  ·'
        else: line+=' '
        line+=f''' let z : Fin {w} := ⟨k-{off}, by omega⟩
    have he : (z.val : Int)+{off} = k := by dsimp [z] <;> omega
    have ht := {th} z
    rwa [he,hrep] at ht
'''
        if last:
            lines=line.splitlines()
            nlines=len(lines)
            for k in range(nlines-3,nlines):
                lines[k]=lines[k][2:]
            line='\n'.join(lines)+'\n'
    checked+=line
    certificate+=f'''
def packedOctCertificate{T}_{p} : EightPointCertificate {A} {C} {p} {B} :=
  eightPointCertificateOfPacked {A} {C} {p} {B} {lam} {W} {var} {size} {R}
    (by decide +kernel) (by decide) packedOct{T}Anchor{p}
    (by rw [packedOct{T}_{p}_budget]; decide)
'''
s=open_(['EightPointPackedGeometry',*names[1:]])+checked+certificate+f'''
theorem max148_second{A}_third{C}_eightPoint_moment_bound (tail : List ℕ) (len : tail.length=6)
    (distinct : (natSubsetSums (148::{A}::{C}::tail)).Nodup) :
    {B} ≤ ((148::{A}::{C}::tail).map (· ^ 2)).sum := by
  apply eightPointNatMomentLower {A} {C} {B} tail len distinct
  intro p hp
  by_cases h : p=0
  · subst p
    exact packedOctCertificate{T}_0
  · have he : p=1 := hp.resolve_left h
    subst p
    exact packedOctCertificate{T}_1

#print axioms max148_second{A}_third{C}_eightPoint_moment_bound
'''
names+=[save(N+'Checked',s)]
print(*names)
