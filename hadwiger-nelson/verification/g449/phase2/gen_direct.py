"""Generate cyclotomic norm identities from independently reduced directions."""
from generate import dlist
from replay import PHI
from pathlib import Path

def quot(f):
    p=f[:]; q=[0]*(len(p)-12)
    for i in range(len(p)-1,11,-1):
        q[i-12]=p[i]
        for j,x in enumerate(PHI):
            p[i-12+j]-=q[i-12]*x
    assert not any(p)
    return q

def mathpoly(coeffs):
    out=[]
    for i,x in enumerate(coeffs):
        if not x: continue
        out.append(f'({x} : ℂ)' + (f'*zeta^{i}' if i else ''))
    return ' + '.join(out) if out else '0'

def test(start,end,path,selected=None):
    header='''import DirectNorm

namespace PlaneColouring.Cyclotomic42

set_option maxRecDepth 8192
set_option maxHeartbeats 20000000

private theorem phiExpanded : '''+mathpoly(PHI)+''' = 0 := by
  have h := phi_relation
  norm_num [eval, phiLow, Fin.sum_univ_succ, Fin.val_succ] at h
  linear_combination h
'''
    blocks=[]
    for k in (selected if selected is not None else range(start,end)):
        v=dlist[k]
        vv='!['+', '.join(map(str,v))+']'
        p=[0]*54
        for i,a in enumerate(v):
            for j,b in enumerate(v):
                p[i+(42-j)]+=a*b
        p[0]-=49**2
        q=quot(p)
        cert=(f"  norm_num [normUnreduced, dir{k}, Fin.sum_univ_succ, Fin.val_succ, zeta_pow]" if sum(x!=0 for x in v)==1
            else f"  norm_num [normUnreduced, dir{k}, Fin.sum_univ_succ, Fin.val_succ]\n  linear_combination ({mathpoly(q)}) * phiExpanded")
        blocks.append(f'''
def dir{k} : Coeff := {vv}

theorem cert{k} : normUnreduced dir{k} = (49^2 : ℂ) := by
{cert}

#print axioms cert{k}
''')
    Path(path).write_text(header+'\n'.join(blocks)+'\nend PlaneColouring.Cyclotomic42\n')
if __name__=='__main__':
    import sys
    start,end=map(int,sys.argv[1:3])
    test(start,end,sys.argv[3])
