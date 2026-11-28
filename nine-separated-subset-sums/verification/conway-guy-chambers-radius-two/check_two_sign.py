"""Pure exact coverage of the nontrivial simultaneous-two-flip certificate families."""
from itertools import combinations
from check_neighbors import A,Y,NAMES,word,dot,plus,times,dual_ok

R=tuple(map(word,NAMES))
basis=set(R)
U=[plus(r,R[7] if j<=4 else R[8]) for j,r in enumerate(R[:7])]
U6p=plus(R[5],R[7])
V=[plus(u,R[8]) for u in U[:5]]
assert all(set(r)<={-1,0,1} and dot(r,A)==2 and r not in basis for r in U+[U6p])
assert all(set(r)<={-1,0,1} and dot(r,A)==3 and r not in basis for r in V)
assert U[6]==word('.....-+..')

def certified(terms,flips):
    # Build model signs from CG-positive representatives of each term, not from the proposed sign.
    model={times(-1,p) if p in flips else p
           for _,r in terms for p in (r if dot(r,A)>0 else times(-1,r),)}
    return dual_ok(terms,model)

def ordinary(js, replacements):
    budgets=Y[:]
    budgets=list(budgets)
    for j in js: budgets[j]=0
    terms=[]
    for j,k,z,u in replacements:
        assert j in js and k not in js and u==plus(R[j],R[k]) and z>=Y[j]
        budgets[k]-=z
        terms.extend(((z-Y[j],times(-1,R[j])),(z,u)))
    terms=tuple(terms)+tuple(zip(budgets,R))
    # Rows with zero weights need not be enforced, and in particular a flipped basis is unused here.
    return tuple((c,r) for c,r in terms if c!=0)

vals=[]
for j,k in combinations(range(7),2):
    if k<=4:
        repl=((j,7,Y[j],U[j]),(k,7,48-Y[j],U[k]))
    elif j<=4:
        repl=((j,7,48,U[j]),(k,8,57,U[k]))
    else:
        assert (j,k)==(5,6)
        repl=((j,7,48,U6p),(k,8,57,U[k]))
    vals.append(certified(ordinary((j,k),repl),{R[j],R[k]}))
assert len(vals)==21 and min(vals)==185
print('Exact paired-basis cases:',len(vals),'minimum proved cap bound:',min(vals))
special=[]
for j in range(5):
    terms=tuple((c,r) for i,(c,r) in enumerate(zip(Y,R)) if i not in (j,7,8))
    terms+=((48-Y[j],R[7]),(57-Y[j],times(-1,U[j])),(57,V[j]))
    bound=certified(terms,{R[j],U[j]})
    assert bound==161+57-3*Y[j]
    special.append(bound)
special.append(certified(ordinary((5,),((5,7,48,U6p),)),{R[5],U[5]}))
assert special==[215,215,212,206,194,179]
print('Exact second-companion flip cases:',len(special),'bounds:',special)
print('Other sorted sign-distance-two cases reduce to the single-flip/original duals.')
