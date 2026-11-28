"""Exact finite smoke check of the symbolic histogram formulas in notes.md."""
from fractions import Fraction as Q
from itertools import combinations

for d in range(2, 65):
    b, a, y, *xs = range(d + 3)
    first = [b, y, *xs]
    late = [b, *xs, y]
    weighted = Q(2*(d+1), 3*(3*d+2))
    parts = [(first, 3, Q(d-2, 3*d+2)),
             (first, 4, Q(4*(d+2), 3*(3*d+2))),
             (late, d+2, Q(2*(d+2), 3*(3*d+2)))]
    assert sum(w for _, _, w in parts) == 1

    def prepare(order, cuts, w):
        return (dict(zip(order,range(len(order)))), cuts, w)
    components = [prepare(*part) for part in parts]
    first_at_zero = prepare(first, 1, Q(1))

    def fwd(i, j, eps=0):
        total = 0
        for pos, h, w in components:
            if i == a:
                count = min(pos[j]+1, h)
            elif j == a:
                count = max(h-pos[i]-1, 0)
            else:
                count = h*(pos[i] < pos[j])
            total += w*count/h
        pos, _, _ = first_at_zero
        forward_at_zero = (j != a) and (i == a or pos[i] < pos[j])
        return (1-eps)*total + eps*forward_at_zero

    def joint(i, j):
        return sum(w*max(h-max(pos[i],pos[j])-1,0)/h
                   for pos, h, w in components)
    assert fwd(a,b) == weighted
    assert fwd(a,xs[0]) == fwd(a,y) == Q(2,3)
    assert fwd(y,xs[0]) >= Q(2,3)
    assert joint(xs[0],y) == 2*weighted - Q(1,3)
    eps = Q(1,1000)
    assert all(fwd(i,j,eps) > Q(2,3)
               for i,j in combinations([b,a,y,*xs],2))
    if d >= 4:
        assert (1-weighted)*joint(xs[0],y) < Q(1,9)

print("Exact histogram smoke checks passed for d=2,...,64; all perturbations strictly unbalanced.")
print("For d>=4 the boundary histogram fails XYZ conditioned on b<a.")
