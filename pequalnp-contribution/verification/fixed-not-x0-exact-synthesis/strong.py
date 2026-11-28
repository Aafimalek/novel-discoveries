#!/usr/bin/env python3
"""Semantically normalized exact SAT instance for the fixed input-NOT graph circuit."""
import argparse
from pathlib import Path
from base import Encoder, INPUTS, frontiers, raw, check_dag, read_model

class Strong(Encoder):
    def __init__(self,n):
        super().__init__(n)
        self.base_count=self.num_vars
        self.used=[self.var() for _ in range(n)]
        self.diff=[]
        self.row(self.used[0])
        for g,k in enumerate(self.gates):
            live=self.used[g]
            if g:
                self.row(-live,self.used[g-1])
            # Outside the active prefix, duplicate the prior output under OR.
            if g:
                self.row(live,-k.and_type)
                self.row(live,k.left[INPUTS+g-1])
                self.row(live,k.right[INPUTS+g-1])
            # An active gate does not select the same parent twice.
            for l,r in zip(k.left,k.right):
                self.row(-live,-l,-r)
            if g+1<n:
                # Every gate, active or padding, is in the output cone.
                # Because all pins legally refer earlier wires, fanout of
                # each nonoutput gate forces a path to the unique sink.
                self.row(*(lit for later in self.gates[g+1:]
                           for lit in (later.left[INPUTS+g],later.right[INPUTS+g])))
                # The right/larger parent indices are nondecreasing.
                for a,lit in enumerate(k.right):
                    for r in self.gates[g+1].right[:a]:
                        self.row(-lit,-r)
        # Target is essential in each x_i. For x0 either raw polarity may
        # participate, but at least one of x0 and b must participate.
        for indices in [(i,) for i in range(1,8)]+[(0,8)]:
            self.row(*(k for g in self.gates for j in indices for k in (g.left[j],g.right[j])))
        E=self.examples
        # Direct propagation of monotonicity on every comparable pair.
        for x,_,ys,_ in E:
            for z,_,zs,_ in E:
                if x!=z and x&1==z&1 and x&z==x:
                    for a,b in zip(ys,zs): self.row(-a,b)
        for g,y in enumerate(self.gates):
            # Active results are not constant on the tested signatures.
            self.row(-self.used[g],*(ys[g] for _,_,ys,_ in E))
            self.row(-self.used[g],*(-ys[g] for _,_,ys,_ in E))
            for i in range(INPUTS):
                # Nontrivial active signature against each raw wire.
                self.row(-self.used[g],*(ys[g] if not raw(x)[i] else -ys[g]
                                        for x,_,ys,_ in E))
            for k in range(g):
                ds=[]
                for x,_,ys,_ in E:
                    d=self.var()
                    a,b=ys[g],ys[k]
                    # A marker may be true only if its sample differs.
                    self.row(-d,a,b)
                    self.row(-d,-a,-b)
                    ds.append(d)
                    self.diff.append((d,a,b))
                self.row(-self.used[g],*ds)
    def stitch_normal(self,dag,active):
        v=Encoder(self.n).stitch(dag)
        assert len(v)==self.base_count
        v.update({u:i<active for i,u in enumerate(self.used)})
        v.update({d:v[a]!=v[b] for d,a,b in self.diff})
        return v

def normal(dag,budget):
    """Exact deletion and renumbering on the same thirty fixed-phase samples."""
    tests=frontiers()
    sig=[tuple(raw(x)[i] for x,_ in tests) for i in range(INPUTS)]
    assert len(set(sig))==INPUTS
    seen={s:i for i,s in enumerate(sig)}
    equiv=list(range(INPUTS))
    uniq=[]
    # Negative sentinels stand for constants only during normalization.
    const={-1:(False,)*len(tests),-2:(True,)*len(tests)}
    def value(w):return sig[w] if w>=0 else const[w]
    for t,l,r in dag:
        a,b=equiv[l],equiv[r]
        s=tuple((u and v) if t=="and" else (u or v) for u,v in zip(value(a),value(b)))
        if s==const[-1]:z=-1
        elif s==const[-2]:z=-2
        else:
            z=seen.get(s)
            if z is None:
                assert a>=0 and b>=0
                z=len(sig); seen[s]=z; sig.append(s)
                uniq.append((t,a,b))
        equiv.append(z)
    root=equiv[-1]
    assert root>=INPUTS # edge target is no raw wire, on these samples
    needed={root}; stack=[root]
    while stack:
        i=stack.pop()
        for j in uniq[i-INPUTS][1:]:
            if j>=INPUTS and j not in needed:
                needed.add(j);stack.append(j)
    order=[]
    ren={j:j for j in range(INPUTS)}
    while needed:
        choices=[]
        for i in needed:
            op,a,b=uniq[i-INPUTS]
            if a in ren and b in ren:
                l,r=sorted([ren[a],ren[b]])
                choices.append((r,l,op,i))
        r,l,op,i=min(choices)
        needed.remove(i)
        ren[i]=INPUTS+len(order)
        order.append((op,l,r))
    assert ren[root]==INPUTS+len(order)-1
    active=len(order)
    assert 1<=active<=budget
    while len(order)<budget:
        r=INPUTS+len(order)-1
        order.append(("or",r,r))
    check_dag(order)
    return order,active

def witness():
    dag=[]
    def add(t,l,r):
        dag.append((t,*sorted([l,r])))
        return INPUTS+len(dag)-1
    def U(vs):
        a=vs[0]
        for v in vs[1:]:a=add("or",a,v)
        return a
    dummy=add("or",8,8)      # repeated-parent identity
    zero=add("and",0,dummy)  # constant only under the fixed phase relation
    bics=[((2,4),(6,7)),((5,),(1,7)),((0,3),(5,7)),((1,2),(4,6)),((0,),(3,))]
    out=U([add("and",U(l),U(r)) for l,r in bics])
    # Output reads b genuinely although formula simplifies on the two phases:
    # adding (f∨x0)∧(f∨b) recovers f, so the sampled duplicate can collapse.
    add("or",add("and",add("or",out,0),add("or",out,dummy)),zero)
    check_dag(dag)
    return dag

def selftest():
    dag,used=normal(witness(),17)
    assert used<=16
    k=Strong(17)
    assert k.check_model(k.stitch_normal(dag,used))==dag
    print(f"Positive control normalized to {used} active gates and {17-used} padding gates; all models/256 evaluations agree.")

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("formula",type=Path)
    p.add_argument("--gates",type=int,default=14)
    p.add_argument("--selftest",action="store_true")
    p.add_argument("--model",type=Path)
    a=p.parse_args()
    if a.selftest:selftest()
    k=Strong(a.gates)
    k.dimacs(a.formula)
    print(k.n,"AND/OR gates after b=NOT(x0):",k.num_vars,"variables,",len(k.rows),"clauses")
    count=sum(len(c) for c in k.rows)
    print(count,"literals, strictly legal parent IDs, 30 original phase-frontier input tests")
    if a.model:
        mod=read_model(a.model)
        dag=k.check_model(mod)
        for i,(op,l,r) in enumerate(dag):
            print(i+INPUTS,op,l,r,"active" if mod[k.used[i]] else "padding")
if __name__=="__main__":main()
