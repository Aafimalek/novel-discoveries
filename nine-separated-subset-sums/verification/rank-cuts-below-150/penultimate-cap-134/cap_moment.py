from fractions import Fraction as F
from itertools import product
from math import comb

K=(158,159,161,162,168,169,171,172)

def run(t):
    R={r for k in K for r in range(max(109,k+t-147),k+1)}
    assert R==set(range(max(109,158+t-147),173))
    return tuple(sorted(r-108 for r in R))

def envelope(t):
    Q=run(t); rows=[]
    for a in range(max(Q),75):
        lower=[2*j-1 for j in range(1,129)]
        for q in Q:
            for j,z in ((a-q+1,149-2*q),(a+1,150+2*q),(149-a,449-2*q)):
                lower[j-1]=max(lower[j-1],z)
        for i in range(1,len(lower)):
            lower[i]=max(lower[i],lower[i-1]+2)
        rows.append((F(sum(x*x for x in lower),128),a))
    return rows

def cap(t):
    y=tuple(range(t-6,t+2))
    B,a=min(envelope(t))
    D=sum(v*v for v in y)-B
    return y,B,D,a

def crude_deduction(t):
    y,B,D,a=cap(t)
    if D<0:
        return (B,a,'square',None)
    C=D/y[0]
    # Need the forced alpha at q=64 to be balanced.
    assert 2*t-20-C>=23 and C<2*y[0]
    def L(r):
        if r<=39:return 2*y[0]*r-r*r
        return 2*y[0]*r-(r*r+39*39)/2
    def cutoff():
        for r in range(1,C.numerator//C.denominator+1):
            if L(F(r))>D: return r
        return C
    R=cutoff()
    unbalanced=sorted(abs(sum(e*x for e,x in zip(s,y)))
        for s in product((-1,1),repeat=8) if s[0]==1 and sum(s))
    assert len(unbalanced)==93 and unbalanced[0]==2*t-20
    for q in run(t):
        avail=comb(8,4)//2+sum(v<151-2*q+R for v in unbalanced)
        if avail<65-q:
            return (B,a,'quantile',(R,q,65-q,avail))
    return (B,a,'not excluded',R)

if __name__=='__main__':
    expected=(93525.15625,92883.03125,92243.65625,91607.03125,90973.15625,90342.03125,89713.65625,89088.03125,88465.15625,87845.03125,87227.65625)
    for t,e in zip(range(109,120),expected):
        B,a,c,info=crude_deduction(t)
        assert B==F(e) and a==64
        assert (c=='not excluded')==(t==119)
        print(t,B,a,c,info)
