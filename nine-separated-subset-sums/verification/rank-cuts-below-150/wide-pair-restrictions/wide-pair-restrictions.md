# Written wide-pair restrictions in the nine-weight floor-148 slice

The conclusion is a further restriction, **not** an exclusion of the
wide slice:
\[
 \boxed{d=x_9-x_8=1,\quad e=x_8-x_7\ge3}
\]
may be assumed in its normalized representative. More precisely, in
the narrow remaining band \(3\le e<4\), every one of the four prescribed
pairs has opposite seventh signs, with the left and right sign patterns
specified below. The existence of any remaining configuration is not
asserted. No solver, Lean, or branch enumeration was used.

## Normalization and established rank data

Write \(Y=x_7,\ X=x_8,\ M=x_9\). In the already established final slice
\(148\le X<149,\ 149\le M<150\), the terminal gap \(d=M-X<2\) is short.
The wide branch has \(X-Y\ge2\), while the short block is the terminal
pair. In the usual order-preserving pair normalization replace the last
two weights by their midpoint minus and plus \(1/2\). The sum \(X+M\)
stays fixed, \(X\) weakly increases and \(M\) weakly decreases, so the
wide condition persists. First-seven positive differences \(b\)
initially satisfy \(b\ge1+d\) by opposing the two middle top shifts,
and avoid \((X-1,M+1)\) by their comparisons with the two individual
top shifts. Hence when the pair moves inward, those differences retain
their unit margin and their side relative to each shift. The middle
swap distance decreases to 1 and remains below all positive \(b\);
the outer shift \(X+M\) is unchanged. This proves preservation of
every labeled subset order as well as separation. The earlier nine
bound ensures the new maximum is still at least 149, so the new
\(X\) is still in the displayed final slice. Relabel the representative
as \(Y,X,M\) and henceforth \(M=X+1\).

Write \(s_r\) for the increasing real scores and \(g_k=s_{k+1}-s_k\).
The previous central proof gives \(1\le g_k<2\) on ranks
158 through 354. For the ordered full absolute nine-sign magnitudes
\(D_j=s_{256+j}-s_{257-j}\), it follows that
\[
 2\le D_{j+1}-D_j<4
\]
whenever the upper gap \(g_{256+j}\) is in that central range; all
indices below, including the auxiliary ones at 46 through 66,
are in this range. Also \(D_j\ge2j-1\) globally. Each positive
full magnitude has a unique positive sign word: it is twice the
upper of its two complementary subset ranks minus the total score.
Thus no two distinct positive oriented words give the same number.

For the prescribed four pairs \(q=50,53,60,63\), set \(k=q+108\).
Write \(v_q,w_{q+1}\) for their positive full first-seven signed
forms, with seventh signs denoted respectively by \(v_7,w_7\).
Their known rank identities in this normalization are
\[
 D_q=v_q+1,\quad
 D_{q-1}=v_q-1,\quad
 D_{q+1}=X+M-w_{q+1},\quad
 D_{q+1}-D_q=2g_k .
\]
The predecessor is indeed the same first-seven word: the two possible
opposite-sign placements on the last pair differ by \(2d=2\),
both values are positive (here \(v_q\) is near \(2q-1\)), and no
different full magnitude can lie between them because all have
spacing at least 2. In particular \(D_q-D_{q-1}=2\).
The last two top signs for the three displayed positions are
respectively \((-+),(+-),(++)\) in the order \(q,q-1,q+1\),
and their seventh signs are respectively \(v_7,v_7,-w_7\).

For each pair the half sum of the two first-seven forms is
\[
 p_q=(v_q+w_{q+1})/2=X-g_k\in(X-2,X-1].
\]
Its coefficients belong to \(\{-1,0,1\}\). If seventh signs oppose,
it is a first-six signed-support form. If both are plus,
\(p_q-Y=e-g_k\) is a first-six signed-support form instead.

## First-six forbidden intervals

Any positive first-six subset difference \(b\) is at least 2,
since the first seven are 2-separated after normalization.
It must stay at least one from every positive signed difference of
the three top coordinates: compare opposite translations on disjoint
coordinate groups. In particular the centers \(Y-1,Y,Y+1\)
(the first and last are \(Y+X-M,Y+M-X\)) give the open
forbidden corridor \((Y-2,Y+2)\). The low centers \(e,e+1\)
(realized by \(X-Y,M-Y\)) give the open forbidden corridor
\((e-1,e+2)\). In the finite ranges \(e<4\) considered below,
\(Y>144\), so all claimed \(Y\)-band centers are positive.

A useful consequence for either mixed seventh signs or two plus
signs, when \(2\le e<4\), is
\[
 g_k\le e-2 .
\]
Indeed \(p_q>Y\) because \(e-g_k>0\). If seventh signs oppose,
\(p_q\) is first-six and hence must be at least \(Y+2\),
outside that open window. If both are plus, the positive first-six
difference \(p_q-Y\) must itself be at least 2. These give the same
inequality. In particular for \(2\le e<3\), neither pattern is
possible (since \(g_k\ge1\)), so all four pairs would be both minus.

## Exact third-lift indexing; exclusion of \(2\le e<3\)

The top patterns have these signed contributions, at fixed first-six
word, in increasing order:
\[
\begin{array}{c|ccc}
\text{one plus}&+--:\ -X-e-1&-+-:\ -Y-1&--+:\ -Y+1\\
\text{two plus}&++-:\ Y-1&+-+:\ Y+1&-++:\ X+e+1 .
\end{array}
\]
The step between \(+--\) and \(-+-\), or between \(+-+\) and
\(-++\), is \(2e\); the other step is 2.

If \(v_q(7)=-\), the full word of \(D_q\) has top \(\texttt{--+}\),
and \(D_{q-1}\) has top \(\texttt{-+-}\) with the same first six.
Its additional \(\texttt{+--}\) lift is precisely
\[
 D_{q-1}-2e = D_q-2-2e,
\]
**not** \(D_q-2e\). For \(q=53,63\) and \(e<4\) this is
strictly positive, since \(D_q\ge2q-1\ge105\) while \(2+2e<10\).
Its signed orientation is therefore the displayed top pattern.

If \(2\le e<3\), a displacement \(2e\in[4,6)\) down from
\(D_{q-1}\) cannot be one rank step (central steps are \(<4\))
and cannot be at least three steps (every step is \(\ge2\)).
It is exactly two steps, reaching \(D_{q-3}\).
For \(q=53,63\) these are \(D_{50},D_{60}\), required to have
last two signs \(-+\). The lift \(\texttt{+--}\) has last
two signs \(--\), impossible by sign uniqueness.
Thus \(v_{53}(7),v_{63}(7)\) cannot be minus, contradicting
the preceding all-minus requirement. This proves \(e\ge3\).

## Conditional sign and gap pattern when \(3\le e<4\)

A displacement \(2e\in[6,8)\) between these central values
has rank displacement 2 or 3: one step has length \(<4\)
and four steps have length \(\ge8\).
In particular the corrected negative lift from \(D_{q-1}\)
for \(q=53,63\) would fall at either \(q-3\) or \(q-4\).
These are \(50,49\) or \(60,59\), whose last two signs are
respectively \(-+\) and \(+-\); neither is \(--\).
Hence the right-hand \(v\) at 53 or 63 is plus.

Conversely if the left \(v\) at \(q=50\) or 60 were plus,
its top pattern \(\texttt{+-+}\) at \(D_q\) would extend to
\(\texttt{-++}\) at \(D_q+2e\), necessarily \(D_{q+2}\) or
\(D_{q+3}\). The first is the predecessor companion of the
right-hand \(v\) and has last two signs \(+-\); the second
has last two signs \(-+\). Neither is \(++\).
Thus the left \(v\) is minus.

Let \(j=q+3\) denote the right-hand center. If \(w_{j+1}(7)\)
were plus as is \(v_j(7)\), the above half-sum argument would
give \(g_{j+108}\le e-2\). The word at \(D_{j+1}\) would have
top \(\texttt{-++}\). Its middle lift \(\texttt{+-+}\) at fixed
first six is \(D_{j+1}-2e\) and lies in
\[
 (D_j-6,D_j-4],
\]
since \(2\le D_{j+1}-D_j=2g_{j+108}\le2e-4\) and \(e<4\).
The lift is positive. It lies below \(D_{j-1}=D_j-2\) and
can be at most two steps below \(D_j\) by the spacing 2;
it must be \(D_{j-2}=D_{q+1}\).
But that slot is required to have last two signs \(++\), unlike
the lift \(\texttt{+-+}\). Thus \(w_{54}(7),w_{64}(7)\) are minus.

Finally, if the left \(w_{q+1}(7)\) were minus too, both
\(D_{q+1}\) and \(D_{q+4}\) would have all-plus top patterns.
Set \(T=Y+X+M\). Then their positive numerical values can
be written \(T-B_1,T-B_2\), where \(B_1=Y+w_{q+1}>0\) and
\(B_2=Y+w_{q+4}>0\) are positive oriented full first-six
forms. The half-difference \((B_1-B_2)/2\) is a positive
first-six signed-support form (distinct actual magnitudes).
It is also
\[
 (D_{q+4}-D_{q+1})/2\in[3,5).
\]
Indeed \(D_{q+3}-D_{q+2}=2\) is the exact companion step
for the right-hand \(v\), and the other two steps are in
\([2,4)\). This falls strictly within \((e-1,e+2)\) for
\(3\le e<4\), a contradiction. Therefore the left \(w\)
is plus.

In summary, for \(q=50,60\) the seventh signs are
\[
\begin{array}{c|cc}
\text{pair}&v_7&w_7\\ \hline
(q,q+1)&-&+\\
(q+3,q+4)&+&-
\end{array}
\]
so **all four pairs are mixed** and all four physical gaps
obey \(1\le g_k\le e-2\). In particular each \(p_q\) is a
positive first-six signed-support form in the narrow common
interval \([Y+2,X-1]\) of width \(e-3<1\).
If two distinct coefficient words realize such half sums,
they must have opposite signs on some common coordinate:
otherwise their difference is a nonzero \(\{-1,0,1\}^6\)
signed form of magnitude below 1, inconsistent with separation.

## Scope and a tempting but invalid shortcut

The corrected first lift for a minus \(v_q\) comes from its
preceding companion \(D_{q-1}\), not from \(D_q\). For example,
for \(3\le e<4\), the forced left mixed pair is compatible
with these local indices at \(q=50,60\):
- \(D_{q+1}-2e\) is at \(q-2\) with top \(\texttt{+-+}\);
  the previous lift minus 2 is at \(q-3\) with top \(\texttt{++-}\).
- \(D_q-2-2e\), the first one-plus lift of the left \(v\),
  is at \(q-4\) with top \(\texttt{+--}\).
  Its distance below the \(\texttt{++-}\) at \(q-3\)
  is \(2g_k\), not \(2(g_k-1)\).
These indices follow from the same exact companion step and
the bounds \(1\le g_k\le e-2\): the middle lift at \(q-2\) lies
in \((D_q-6,D_q-4]\), and the one-plus first lift is below
\(q-3\) yet no more than four steps down from \(q\).
So the local interleaving gives no forbidden sub-2 gap.
No assertion \(e\ge4\) follows from the arguments here.
