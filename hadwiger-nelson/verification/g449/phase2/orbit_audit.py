#!/usr/bin/env python3
"""Independent exact orbit decomposition of the pinned G449 coordinate data."""
from pathlib import Path
from collections import Counter
from replay import rem42, verify

def turn(c):
    return rem42([0]*6+list(c))

def canonical(v):
    return min(v,tuple(-x for x in v))

def cycles(items,action):
    unseen=set(items)
    histogram=Counter()
    while unseen:
        a=min(unseen)
        b=a
        k=0
        while True:
            unseen.remove(b)
            k+=1
            b=action(b)
            if a==b: break
        histogram[k]+=1
    return dict(sorted(histogram.items()))

def main():
    coords,edges=verify(Path('G449.k21'))
    ids={p:i for i,p in enumerate(coords)}
    rho=[ids[turn(p)] for p in coords]
    es=set(edges)
    assert len(set(rho))==449
    def edge_act(e):
        a,b=e
        return tuple(sorted((rho[a],rho[b])))
    D={canonical(tuple(x-y for x,y in zip(coords[a],coords[b]))) for a,b in es}
    assert cycles(ids.values(),rho.__getitem__)=={1:1,7:64}
    assert cycles(es,edge_act)=={7:314}
    assert cycles(D,lambda v:canonical(turn(v)))=={7:7}
    print('rotation: 1 fixed vertex + 64 seven-cycles; 314 edge seven-cycles; 7 direction seven-cycles')

if __name__=='__main__':
    main()
