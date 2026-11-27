from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
from scipy.linalg import qr

w=[77,117,137,148,154,157,159,160,161]
m=sorted(range(512),key=lambda j:sum(weight for bit,weight in enumerate(w) if (j>>bit)&1))
rows=np.array([[(b>>j&1)-(a>>j&1) for j in range(9)] for a,b in zip(m,m[1:])],dtype=int)
c=np.array([0]*8+[1])
res=linprog(c,A_ub=-rows,b_ub=-np.ones(len(rows)),bounds=[(None,None)]*9,method='highs')
assert res.success
primal=[Fraction(float(x)).limit_denominator(2**20) for x in res.x]
assert all(sum(int(a)*b for a,b in zip(row,primal))>=1 for row in rows)
dual=[(i,Fraction(float(-x)).limit_denominator(2**20)) for i,x in enumerate(res.ineqlin.marginals) if abs(x)>1e-8]
assert all(v>=0 for _,v in dual)
assert [sum(v*int(rows[i,j]) for i,v in dual) for j in range(9)]==list(c)
assert sum(v for _,v in dual)==primal[-1]
print('Chamber optimum exact:',primal[-1],'; exact vector',*(str(v) for v in primal))
print('Dual:',[(m[i],m[i+1],str(v)) for i,v in dual])
