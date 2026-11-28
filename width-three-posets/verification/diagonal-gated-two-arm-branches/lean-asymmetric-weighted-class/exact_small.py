"""Tiny exact diagnostic; no solver or Lean."""
from itertools import product
checked = 0
for p,q,r,s,u,v,H in product(range(5),repeat=7):
    if p*r+q*s<=(p+q)*(u+v):
        assert p*min(r,H)+q*min(s,H)<=(p+q)*(min(u,H)+min(v,H))
        checked += 1
print(f"{checked} finite capped inequalities with admissible raw rank sums, including zero weights.")
checked = 0
for h,i,j,d,e in product(range(1,7),range(7),range(7),range(10),range(10)):
    if d*e<=(h-1)*(d+e):
        B, M = h+i+j+1, max(min(i,j),abs(i-j))
        A = 2*h+i+j+M
        assert e*B+d*(h+2*j+e+1)<=(d+e)*A
        assert e*(h+2*i+d+1)+d*B<=(d+e)*A
        checked += 1
print(f"{checked} exact admissible product tuples, both possible late-head sides.")
n=16
V=tuple((rail,i) for rail in "xy" for i in range(n))
x=V[:n]
y=V[n:]
E=set(zip(x,x[1:]))|set(zip(y,y[1:]))|set(zip(x,y[4:]))|set(zip(y,x[12:]))
for z in V:
    E|={(u,v) for u in V for v in V if (u,z) in E and (z,v) in E}
assert all((z,z) not in E for z in V)
for i in range(n):
    for j in range(n):
        assert ((x[i],y[j]) in E)==(j-i>=4)
        assert ((y[j],x[i]) in E)==(i-j>=12)
opposite=lambda z:[w for w in V if z[0]!=w[0]]
degree=lambda z:sum((z,w) not in E and (w,z) not in E for w in opposite(z))
assert max(map(degree,V))==15
print("h=4, d=4, e=12: exact cross closure on 16+16 labels, degree 15; product 48 at equality.")
