from itertools import product
from math import comb
from cap127_third import calc

if __name__=='__main__':
    left=calc(130)
    assert left==[(64,49,24,24,0,7500)]
    a,A,B,C,_,_=left[0]
    # Adjacent gap = 1 + preceding deficit - following deficit.
    bounds=[1+(A+1)-B,1+(B+1)-C]+[1+C+1]*5
    q0=33
    assert max(bounds)<66-q0
    orbits=[comb(8,i) for i in range(4)]+[comb(8,4)//2]
    assert orbits==[1,8,28,56,35]
    b=148-a
    attainable={(sum(w for w,d in zip(orbits,tags) if d==0),
                 sum(w for w,d in zip(orbits,tags) if d<2))
                for tags in product(range(3),repeat=len(orbits))}
    assert (a,b) not in attainable
    print('All adjacent gaps bounded by',bounds,'<',66-q0)
    print('Sign permutation orbit capacities:',orbits)
    print('Nested membership counts',(a,b),'impossible; no profiles remain.')
