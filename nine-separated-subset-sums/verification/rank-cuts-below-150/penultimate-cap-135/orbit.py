"""Exact cardinal admissibility for sign permutation/flip orbit cuts."""
from functools import lru_cache

def generators():
    G=[]
    for i in range(9):
        images=[]
        for j in range(128):
            s=[1]+[1 if (j>>(7-k))&1 else -1 for k in range(1,8)]
            if i<7:
                s[i],s[i+1]=s[i+1],s[i]
            else:
                s[i-7]*=-1
            x=sum(int(s[k]==s[0])<<(7-k) for k in range(1,8))
            images.append(x)
        G.append(images)
    return G
G=generators()
@lru_cache(None)
def orbits(g):
    left=set(range(128)); parts=[]
    gen=[G[i] for i in range(9) if (g>>i)&1]
    while left:
        i=min(left);todo=[i];left.remove(i);p=[i]
        for u in todo:
            for z in gen:
                v=z[u]
                if v in left:
                    left.remove(v);todo.append(v);p.append(v)
        parts.append(tuple(p))
    return tuple(parts)

@lru_cache(None)
def orbit_size_cut(a,g):
    if not g:return True
    m=148-2*a
    reachable=[1]+[0]*a
    keep=(1<<(m+1))-1
    for O in orbits(g):
        w=len(O)
        reachable=[(p | ((p<<w)&keep) |
                    (reachable[j-w] if j>=w else 0)) for j,p in enumerate(reachable)]
    return bool(reachable[a]&(1<<m))

def cert_generators(A,B,C,Cu,lo,hi,Y,W):
    # Known intervals on the first 3 deficits chosen by unit boxes.
    # 60-scaled adjacent differences use a lower bound for the following deficit.
    loR=[A*60,B*60,C*60]
    hiR=[(A+1)*60,(B+1)*60,Cu*60]
    for j in range(1,6):
        loR.append((lo-(j-1)*Cu*60)//(6-j))
        hiR.append(min(Cu*60,-(-hi//j)))
    cap=(W-1)*60
    g=0
    for j in range(7):
        if hiR[j]-max(0,loR[j+1])<cap:
            g|=1<<j
    for j in (0,1):
        if Y[j]*60-loR[j]<W*60:
            g|=1<<(7+j)
    return g

if __name__=='__main__':
    assert sorted(map(len,orbits(127)))==[1,8,28,35,56]
    assert all(not orbit_size_cut(a,127) for a in range(64,75))
    for j in range(7):
        mask=127^(1<<j)
        print(j+1,'+',7-j,[a for a in range(64,75) if orbit_size_cut(a,mask)])
