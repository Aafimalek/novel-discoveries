#!/usr/bin/env python3
"""Exact DIMACS encoding of a monotone DAG after the fixed input NOT(x0)."""
import argparse
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path

EDGES=((0,3),(1,4),(2,4),(0,5),(1,5),(3,5),(1,6),(2,6),(4,6),(0,7),(2,7),(3,7),(4,7),(5,7))
ALL=(1<<8)-1
# Wire numbers 0..7 are x0..x7, wire 8 is b=not x0, 9+g is gate g.
INPUTS=9
FRONTIER_ORDER=((0,1),(1,0),(1,1),(0,0))
GROUP_COUNTS=(11,3,8,8)

def edge_value(x):
    return any((x>>i)&1 and (x>>j)&1 for i,j in EDGES)

def raw(x):
    q=[bool((x>>i)&1) for i in range(8)]
    return q+[not q[0]]

def frontiers():
    groups=[]
    for h,y in FRONTIER_ORDER:
        cand=[s for s in range(256) if (s&1)==h and edge_value(s)==bool(y)]
        mid=[]
        for s in cand:
            if y:
                keep=not any(t!=s and (t&s)==t for t in cand)
            else:
                keep=not any(t!=s and (t&s)==s for t in cand)
            if keep:mid.append(s)
        # Test domination explicitly, not just the aggregate counts.
        for s in cand:
            if y: assert any((t&s)==t for t in mid)
            else: assert any((t&s)==s for t in mid)
        groups.append(mid)
    assert tuple(map(len,groups))==GROUP_COUNTS
    tests=[(x,bool(y)) for (_,y),g in zip(FRONTIER_ORDER,groups) for x in g]
    assert len(tests)==len({x for x,_ in tests})==30
    return tests

@dataclass
class Gate:
    and_type:int
    left:tuple
    right:tuple

class Encoder:
    def __init__(self,n):
        assert n>=1
        self.n=n
        self.num_vars=0
        self.rows=[]
        self.gates=[]
        self.examples=[]
        for g in range(n):
            lim=INPUTS+g
            t=self.var()
            l=tuple(self.var() for _ in range(lim))
            r=tuple(self.var() for _ in range(lim))
            self.gates.append(Gate(t,l,r))
            self.exactly_one(l)
            self.exactly_one(r)
            # AND and OR are both commutative. Equality must remain allowed.
            for i in range(lim):
                for j in range(i):
                    self.row(-l[i],-r[j])
        for x,target in frontiers():
            inputs=raw(x)
            y=[self.var() for _ in range(n)]
            aux=[]
            for g,k in enumerate(self.gates):
                a,b=self.var(),self.var()
                aux.append((a,b))
                for pins,z in ((k.left,a),(k.right,b)):
                    for i,s in enumerate(pins):
                        if i<INPUTS:
                            self.row(-s,z if inputs[i] else -z)
                        else:
                            parent=y[i-INPUTS]
                            assert i-INPUTS<g
                            self.row(-s,-z,parent)
                            self.row(-s,z,-parent)
                z=y[g]; t=k.and_type
                # t=true gives AND; t=false gives OR.
                self.row(-t,-a,-b,z)
                self.row(-t,a,-z)
                self.row(-t,b,-z)
                self.row(t,a,b,-z)
                self.row(t,-a,z)
                self.row(t,-b,z)
            self.row(y[-1] if target else -y[-1])
            self.examples.append((x,target,y,aux))
    def var(self):
        self.num_vars+=1
        return self.num_vars
    def row(self,*ls):
        assert len(ls)>0 and all(1<=abs(x)<=self.num_vars for x in ls)
        assert len(ls)==len(set(map(abs,ls)))
        self.rows.append(ls)
    def exactly_one(self,ls):
        self.row(*ls)
        for a,b in combinations(ls,2): self.row(-a,-b)
    def dimacs(self,path):
        with path.open("w",encoding="ascii",newline="\n") as f:
            print("p","cnf",self.num_vars,len(self.rows),file=f)
            for row in self.rows: print(*row,0,file=f)
    def stitch(self,dag):
        assert len(dag)==self.n
        out={}
        def add(i,y):
            assert i not in out
            out[i]=bool(y)
        for k,(t,l,r) in zip(self.gates,dag):
            add(k.and_type,t=="and")
            for i,s in enumerate(k.left): add(s,i==l)
            for i,s in enumerate(k.right): add(s,i==r)
        for x,target,ys,zs in self.examples:
            wires=raw(x)
            for (op,l,r),y,(a,b) in zip(dag,ys,zs):
                v,w=wires[l],wires[r]
                add(a,v);add(b,w)
                result=(v and w) if op=="and" else (v or w)
                add(y,result)
                wires.append(result)
            assert wires[-1]==target
        assert len(out)==self.num_vars
        return out
    def check_model(self,v):
        # Exact validation against re-generated rows, then full truth table.
        assert set(v)==set(range(1,self.num_vars+1))
        assert all(any(v[abs(l)]==(l>0) for l in row) for row in self.rows)
        dag=[]
        for k in self.gates:
            L=[i for i,u in enumerate(k.left) if v[u]]
            R=[i for i,u in enumerate(k.right) if v[u]]
            assert len(L)==len(R)==1 and L[0]<=R[0]<INPUTS+len(dag)
            dag.append(("and" if v[k.and_type] else "or",L[0],R[0]))
        check_dag(dag)
        return dag

def check_dag(dag):
    assert dag
    for g,(op,l,r) in enumerate(dag):
        assert op in ("and","or") and 0<=l<=r<INPUTS+g
    for x in range(256):
        w=raw(x)
        for op,l,r in dag:
            w.append((w[l] and w[r]) if op=="and" else (w[l] or w[r]))
        assert w[-1]==edge_value(x)

def read_model(path):
    result={}
    for line in path.read_text().splitlines():
        ts=line.split()
        if not ts or ts[0]!="v": continue
        for s in ts[1:]:
            val=int(s)
            if val==0: continue
            assert abs(val) not in result
            result[abs(val)]=val>0
    return result

def selftest():
    # Separately structured 16-gate witness; self-test the SAT-checker
    # with a known circuit, not with an attempted 14-gate witness.
    dag=[]
    def new(op,a,b):
        dag.append((op,*sorted((a,b))))
        return INPUTS+len(dag)-1
    bics=[((2,4),(6,7)),((5,),(1,7)),((0,3),(5,7)),((1,2),(4,6)),((0,),(3,))]
    def OR(L):
        a=L[0]
        for b in L[1:]:a=new("or",a,b)
        return a
    ys=[new("and",OR(l),OR(r)) for l,r in bics]
    y=OR(ys)
    assert len(dag)==16
    new("or",y,y) # identity padding, including parent duplication
    check_dag(dag)
    k=Encoder(len(dag))
    assert k.check_model(k.stitch(dag))==dag
    print("17-gate padded positive control and complete model decode OK")
    dag.pop()
    z1=new("or",y,0)
    z2=new("or",y,8)
    new("and",z1,z2)
    assert len(dag)==19
    # The computed output here uses b and x0: (f∨x0)∧(f∨b)=f.
    k=Encoder(len(dag))
    assert k.check_model(k.stitch(dag))==dag
    print("19-gate fixed-NOT positive control and complete model decode OK")

def main():
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument("formula",type=Path)
    a.add_argument("--gates",type=int,default=14)
    a.add_argument("--model",type=Path)
    a.add_argument("--selftest",action="store_true")
    h=a.parse_args()
    if h.selftest: selftest()
    k=Encoder(h.gates)
    k.dimacs(h.formula)
    print(h.gates,"remaining gates;",k.num_vars,"variables;",len(k.rows),"clauses")
    for h0,y0 in FRONTIER_ORDER:
        print("phase",h0,"target",y0,":",*[f"{x:02x}" for x,y in frontiers() if (x&1)==h0 and y==bool(y0)])
    if h.model:
        for i,(op,l,r) in enumerate(k.check_model(read_model(h.model))):
            print(i+INPUTS,op,l,r)
        print("Exact circuit-model clauses and all 256 input evaluations verified")
if __name__=="__main__":main()
