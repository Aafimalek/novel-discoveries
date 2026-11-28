"""Exact orbit capacities for the two wide signed-sum rank holes."""
from collections import Counter
from itertools import product

N=8
FULL=(1<<N)-1

def canonical(s):
    return min(s, s ^ FULL)

def swap(s,p):
    return s ^ ((3<<p) if (s>>p)&1 != (s>>(p+1))&1 else 0)

def orbits(small_swaps, small_flips=()):
    unseen=set(range(1<<(N-1)))
    sizes=[]
    while unseen:
        s=unseen.pop()
        todo=[s]
        count=0
        while todo:
            s=todo.pop()
            count+=1
            nxt={canonical(swap(s,p)) for p in small_swaps}
            nxt.update(canonical(s^(1<<p)) for p in small_flips)
            new=unseen & nxt
            unseen-=new
            todo.extend(new)
        sizes.append(count)
    assert sum(sizes)==128
    return sorted(sizes)

def possible_counts(sizes):
    # Assign each orbit to one of three nested regions of size
    # a, b-a=148-2a, 128-b=a-20; track only the first two.
    pairs={(0,0)}
    for k in sizes:
        pairs=pairs | {(a+k,d) for a,d in pairs if a+k<=74} | {
            (a,d+k) for a,d in pairs if d+k<=20}
    return tuple(a for a in range(64,75) if (a,148-2*a) in pairs)

def replay():
    all_swaps=tuple(range(7))
    assert orbits(all_swaps)==[1,8,28,35,56]
    assert possible_counts(orbits(all_swaps))==()
    print('All adjacent swaps available: no nested region counts')
    excluded={1:(64,65,66,67,68,69,71,72,73,74),2:(69,),3:(67,72),
              4:(73,),5:(67,72),6:(69,),7:(64,65,66,67,68,69,71,72,73,74)}
    for cut in range(1,8):
        sizes=orbits(tuple(j for j in all_swaps if j!=cut-1))
        ans=possible_counts(sizes)
        assert tuple(i for i in range(64,75) if i not in ans)==excluded[cut]
        print('Only gap',cut,'can be large; orbit sizes',sizes,'admit a:',ans)
    # Invariance under s independent sign flips with at least one
    # fixed coordinate gives orbits of size 2^s.
    for s in range(4):
        sizes=orbits((),tuple(range(s)))
        assert set(sizes)=={2**s}
        ans=possible_counts(sizes)
        assert ans==tuple(a for a in range(64,75)
                          if a%(2**s)==0 and 148%(2**s)==0)
        print('Small coordinates',s,'admit a:',ans)

if __name__=='__main__':
    replay()
