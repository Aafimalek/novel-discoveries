# The normalized wide branch requires \(x_8-x_7\ge4\)

This appendix strengthens the previous wide terminal-pair restriction.
Let \(Y=x_7,\ X=x_8,\ M=x_9\), with the established final slice
\(148\le X<149,\ 149\le M<150\). Normalize the terminal short pair
by moving its two coordinates inward around its fixed midpoint.
As detailed in previous-e3-and-mixed-signs.md, this preserves all
labeled subset comparisons and the wide condition. Hence we may
assume \(M=X+1\). Write \(e=X-Y\). The previous proof rules out
the wide band \(2\le e<3\) by its forbidden half-sum interval and
a signed-lift comparison. Here we also rule out \(3\le e<4\).

## Exact displacement in the dense signed-rank interval

Let the positive full nine-sign magnitudes be sorted as \(D_j\),
one magnitude per pair of complementary words. Ranks and strict
separation uniquely determine their positive oriented words.
The established central envelope is
\[
  D_j=2j+\theta_j,\qquad -1\le\theta_j\le\delta<1
  \quad(1\le j\le64),
\]
with \(\delta=M-149\). Here \(D_{j+1}-D_j\ge2\) globally by
two complementary rank steps, so \(\theta_j\) is nondecreasing.
Consequently for ranks \(i<i'\le64\),
\[
 2(i'-i)\le D_{i'}-D_i<2(i'-i)+2 .
\]
In particular any observed **positive** full signed lift \(D_i+2e\)
for \(e\in[m,m+1)\), \(1\le i\le i+m\le64\), is exactly
\(D_{i+m}\). The rank displacement is at most \(m\) by global
minimum 2 spacing, so its target is inside the valid envelope.
A smaller displacement would give a difference strictly below
\(2m\). For a positive lift \(D_i-2e\) with \(i\le64\) and
\(i-m\ge1\), the same proof gives exactly \(D_{i-m}\).

For \(q=50,53,60,63\) the forced formulas have top signs
\[
\begin{array}{c|ccc}
\text{rank}&q-1&q&q+1\\
\text{top signs}&(v_7,+,-)&(v_7,-,+)&(-w_7,+,+).
\end{array}
\]
Here the first two values \(v_q-1,v_q+1\) differ exactly by 2
and have the same first-six signed prefix and seventh sign.
With \(v_7=+\), switch the top pattern \(\texttt{+-+}\) at \(q\)
to \(\texttt{-++}\) at fixed first-six signs; its positive lift
is \(D_q+2e\). With \(v_7=-\), switch \(\texttt{-+-}\) at
\(q-1\) to \(\texttt{+--}\), giving \(D_{q-1}-2e=D_q-2-2e\).
The starting rank \(q-1\), rather than \(q\), is essential.

## The band \(3\le e<4\) is impossible

Put \(m=3\). If \(v_{53}(7)=-\), the lift
\(D_{52}-2e>0\) has rank 49 by the displacement rule and top
signs \(\texttt{+--}\). But rank 49 is the companion of
rank 50 with last two signs \(+-\), a contradiction.
Therefore \(v_{53}(7)=+\) and its far lift
\(D_{53}+2e\) is at rank 56 with top \(\texttt{-++}\).

If \(v_{60}(7)=-\), its first lift \(D_{59}-2e>0\) is also
at rank 56, but with top \(\texttt{+--}\), inconsistent with
the positive word already there.
If \(v_{60}(7)=+\), its far lift \(D_{60}+2e\) is at rank 63
with top \(\texttt{-++}\), whose last two signs are \(++\),
inconsistent with the prescribed rank 63 having last signs
\(-+\) regardless of \(v_{63}(7)\).
All these positive lifts lie in ranks 1 through 64 by the
given bracketing argument. Positivity of the downward
lifts also follows numerically from \(D_{52}\ge103\),
\(D_{59}\ge117\) and \(2e<8\).
This exhausts the signs and proves \(e\ge4\) in the
normalized wide branch.

### Independent cross-check using the prior mixed-sign identities

In this band those identities give \(v_{53}(7)=+\),
\(v_{60}(7)=-,\ w_{61}(7)=+\), and each physical gap
\(1\le g_k\le e-2\).
The far positive two-plus lift \(D_{53}+2e\) is at
rank 55 or 56 even without the full envelope: its distance
is in \([6,8)\), steps are at least 2 and consecutive central
steps are strictly below 4. It cannot be 55, since its
distance above \(D_{54}\) is \(2(e-g_{161})\ge4\).
So it must be \(D_{56}\), with top \(\texttt{-++}\).

For \(w_{61}(7)=+\), its positive middle lift
\(D_{61}-2e=D_{60}+2g_{168}-2e\)
lies strictly above \(D_{60}-6\) and at most \(D_{60}-4\),
using \(g_{168}\ge1,\ e<4,\ g_{168}\le e-2\).
Consequently it is exactly \(D_{58}\):
it is below \(D_{59}=D_{60}-2\), but any rank at or below
57 is at least 6 below \(D_{60}\). Its first companion,
another exact 2 lower, is \(D_{57}=D_{61}-2e-2\).
The positive first lift of the negative \(v_{60}\) is
\(F=D_{60}-2e-2\), with top \(\texttt{+--}\).
It lies below \(D_{57}\) by \(2g_{168}\ge2\) and
strictly less than 10 below \(D_{60}\).
Thus it is above \(D_{55}\) and exactly \(D_{56}\).
All three raw numbers are positive by \(D_{60}\ge119\).
The two top words conflict at \(D_{56}\), as above.

## Optional static sign-pattern count, not a chamber search

For \(m\ge4\) one can impose the preceding deterministic lifted
top words, checking compatibility only on their ranks. The positive
lift of a plus \(v_q\) uses the rank \(q+m\) when it is in the
envelope. A minus \(v_q\) gives \(\texttt{+--}\) at \(q-1-m\)
when \(m\le q-3\), which ensures its positivity. A plus \(w\)
gives \(\texttt{+-+}\) at \(q+1-m\) and \(\texttt{++-}\)
at \(q-m\) when \(m\le q-1\): the middle lift is then
positive by the lower rank envelope, and its positive
predecessor is one step lower (its rank is at least 2).
No extraneous rule is imposed when the guaranteed in-window
or positivity conditions are absent.

Optionally, two negative \(w\) words yield two positive
all-plus full words at ranks \(r,r'\). Writing \(T=Y+X+M\),
their values have form \(T-B,T-B'\) with positive
first-six full forms \(B=Y+w,\ B'=Y+w'\). The first-six
signed-support half-difference is \(|D_r-D_{r'}|/2\).
If the rank difference is \(m\) or \(m+1\), the displacement
identity places it strictly within the forbidden interval
\((e-1,e+2)\) from the two top centers \(e,e+1\).
This extra rule is a necessary sign filter.

The supplied small integer program checks just these top labels
among \(2^8\) sign choices. Nonzero pattern counts are neither
feasible chamber counts nor evidence of actual configurations.
No interval beyond \(e<4\) is excluded by this table.
