"""Emit original Lean checker (all upstream point data generated locally)."""
from generate import raw, edges, dlist
from pathlib import Path

ids={v:i for i,v in enumerate(dlist)}
def v(xs): return '!['+', '.join(map(str,xs))+']'
def br(vals, offset=0, name='i'):
    if len(vals)==1: return vals[0]
    half=len(vals)//2
    a=br(vals[:half],offset,name)
    b=br(vals[half:],offset+half,name)
    return f'(if {name} < {offset+half} then {a} else {b})'

header='namespace PlaneColouring.Cyclotomic42\n\nset_option maxRecDepth 65536\nset_option maxHeartbeats 0\n'
def raw_basics():
    return (
      'import DirectNorm\n\n'+header+
      'def points (i : ℕ) : Coeff :=\n  '+br([v(p[:12]) for p in raw])+'\n\n'+
      'def rawDirs (i : ℕ) : Coeff :=\n  '+br([v(d) for d in dlist])+'\n\n'+
      '''def signedDir (k : ℕ) (flip : Bool) : Coeff := 
  fun j => if flip then -(rawDirs k j) else rawDirs k j

structure EdgeRow where
  a : ℕ
  b : ℕ
  d : ℕ
  flip : Bool

def EdgeRow.Valid (r : EdgeRow) : Prop :=
  r.a < 449 ∧ r.b < 449 ∧ r.d < 49 ∧
  ∀ j, diff (points r.a) (points r.b) j = signedDir r.d r.flip j

end PlaneColouring.Cyclotomic42
''')
def cleanup_rows():
    out=[]
    for a,b in edges:
        d0=tuple(x-y for x,y in zip(raw[a],raw[b]))[:12]
        d=min(d0,tuple(-x for x in d0))
        out.append(f'⟨{a},{b},{ids[d]},{str(d0!=d).lower()}⟩')
    return out

def cases(a,b,test=False):
    es=cleanup_rows()[a:b]
    d=f'edgesBlock{a}'
    out='import G449BalancedData\n\n'+header+f'''def {d} (i : Fin {b-a}) : EdgeRow :=
  let j := i.val
  {br(es,0,'j')}

/-- Certify the input data link for this fixed batch. -/
theorem block_{a}_valid : ∀ i, ({d} i).Valid := by
  unfold EdgeRow.Valid
  decide +kernel

#print axioms block_{a}_valid

end PlaneColouring.Cyclotomic42
'''
    return out
if __name__=='__main__':
    import sys
    Path('G449BalancedData.lean').write_text(raw_basics())
    a,b=map(int,sys.argv[1:3])
    Path(sys.argv[3]).write_text(cases(a,b))
