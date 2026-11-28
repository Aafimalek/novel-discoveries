# Slot grammar in the normalized terminal-triple branch

Assume a hypothetical nine-weight configuration in the established
floor-148 slice, in its close-triple representative
\[
Y=x_7=X-1,\qquad X=x_8\in[148,149),\qquad M=x_9=X+1 .
\]
The unique short-block normalization preserves every labeled
subset comparison, so all earlier central rank restrictions
remain valid for this representative. In particular
\([158,355]\) has every consecutive real gap strictly below 2,
and the eight prescribed length-148 coordinate-9 edges have
the known top-bit patterns. We use the established convention
\(D_j=s_{256+j}-s_{257-j}\) for the \(j\)-th ordered positive
absolute full-sign magnitude (one per complementary pair).
Writing \(\delta=M-149=X-148\), the known central envelope
is
\[
2j-1\le D_j\le2j+\delta,\quad 1\le j\le64.
\]
Adjacent \(D_j\)'s are at least 2 apart: both complementary
ranks move apart by at least one real unit. For the indices
used below, they are also strictly less than 4 apart, since
\(D_{j+1}-D_j=2(s_{257+j}-s_{256+j})\) by complement
and these consecutive ranks are within the central range.

Positive first-six subset differences are at least 3 apart
from zero, and avoid \((X-3,X+3)\), by the normalized top
differences 1,2 and the middle band \(X-2,\ldots,X+2\).
In particular, first-six full absolute signed magnitudes
are distinct one per complementary pair, and are spaced
at least 6. The spacing follows by applying the same
complementary-rank identity to the ordered 64 subset sums
of these six coordinates, with unit spacing replaced by 3.
Any nonzero signed coefficient word in \(\{-1,0,1\}^6\)
is a difference of two first-six subsets, so it too must
avoid that open forbidden interval in positive orientation.

## 1. Complete trio partition

In a representative of each full nine-sign complement pair
choose at least two top signs plus. This selects exactly one
raw sign word per complementary pair. For each of the 64
first-six sign words, let \(b\) be its signed first-six sum.
The raw top-three contributions for two pluses are
\(X-2,X,X+2\), giving full raw sums \(b+X-2,b+X,b+X+2\).
Here \(|b+X|\ge3\): if \(b<0\) this follows from the middle
forbidden interval, and if \(b>0\) from \(X>0,b\ge3\).
Thus the three raw signs are the same and taking absolute
values produces a trio with gap exactly 2 at both steps.
No fourth magnitude can intervene, by minimum 2 spacing.

In positive full orientation the ascending top patterns
within a two-plus trio are \(++-\), \(+-+\), \(-++\).
Within a one-plus trio they are \(+--\), \(-+-\), \(--+\);
these arise by complementing a negative raw trio.
The all-plus raw form gives one other magnitude \(|b+3X|\),
whose positive top orientation is \(+++\) or \(---\).
Thus the entire list is a disjoint tiling by 64 complete
trios and 64 other singleton magnitudes. A singleton here
means its block type, not a claim about nearby numerical gaps.
All identities concern actual labeled signed words: if two
distinct complement pairs had equal absolute sum, their
positive orientations would give identical complementary
rank gaps, contrary to strict rank separation. No ambiguity
is introduced by taking positive orientations.

## 2. All four prescribed pairs are two-plus mirrors

For \(q=50,53,60,63\), the known formulas are
\[
D_q=v_q+1,\qquad D_{q+1}=2X+1-w_{q+1},
\]
where \(v_q,w_{q+1}\) are positive oriented first-seven full
forms. The top signs for \(D_q\) are
\((v_q(7),-,+)\), and for \(D_{q+1}\) are
\((-w_{q+1}(7),+,+)\). If \(v_q(7)=+\), \(D_q\) is middle
in a two-plus trio and \(D_{q+1}\) must be its last member.
Hence \(w_{q+1}(7)=+\) and the first-six word of \(w\)
is the negative of the first-six word of \(v\). Conversely
if \(w_{q+1}(7)=+\), its trio predecessor at \(q\) has
top pattern \(+-+\), giving \(v_q(7)=+\). Thus the seventh
signs match. If both are minus, \(D_q\) ends a one-plus trio
and \(D_{q+1}\) is an all-plus positive singleton.

For \(q=53,63\), the both-minus option is impossible:
the first term of its one-plus trio at \(q-2=51,61\)
would have top signs \(+--\), but these preceding forced
singleton-or-last-trio positions have top coordinates 8
and 9 both plus by their displayed formula. Therefore
\(v,w\) are both plus at \(53,63\).

Call a singleton of index in the range used here *low* when
\(D=3X-a\) for a positive first-six magnitude \(a<3X\),
and *high* when \(D=a-3X\) with \(a>3X\). These exhaust
the possibilities here: a raw magnitude \(3X+a\) is far
above \(D_{64}<129\).
For a two-plus trio center \(D_c\) in this range the
corresponding positive first-six magnitude is \(b=X-D_c\).
A low singleton cannot immediately precede or follow such
a trio. If it did, its slot value \(D_r\) would satisfy
\(|D_c-D_r|<6\) (one fixed trio step 2 and the neighboring
step strictly below 4). Then
\[
\frac{a-b}{2}=X+\frac{D_c-D_r}{2}
\]
is a positive first-six signed-support form inside
\((X-3,X+3)\), impossible. It is an allowed support
form because \(a,b\) are oriented full first-six words and
halving their difference gives coefficients in \(\{-1,0,1\}\).
Its support is nonempty by the distinct numerical bands.

Now if \(q=50\) or 60 had both seventh signs minus,
its position \(q+1\) would be a positive all-plus
singleton \(D_{q+1}=3X-(w+Y)\), with \(w+Y>0\).
It is low and immediately precedes the first member
at \(q+2\) of the already forced two-plus trio whose
center is \(q+3=53\) or 63. This contradicts the preceding
observation. Hence **all four prescribed pairs are both plus**,
with opposite first-six words. Their physical gaps
\(g_{158},g_{161},g_{168},g_{171}\) are all exactly 1,
as each equals \((D_{q+1}-D_q)/2\).

In particular the four centers have corresponding first-six
positive full magnitudes \(b_q=X-D_q\). Since \(D_{q-1}=D_q-2\)
and \(D_{q-1}\ge2q-3\), one has \(D_q\ge2q-1\) (the same
general lower envelope). Therefore
\[
b_{50}\in[48,50),\quad b_{53}\in[42,44),\quad
b_{60}\in[28,30),\quad b_{63}\in[22,24).
\]

## 3. One high singleton and one two-plus trio between the forced blocks

Slots 55–58 are strictly between the complete trios 52–54
and 59–61, so they consist either of four singletons or
one complete trio and a singleton. Any singleton at
55 or 58 immediately abuts a two-plus trio and therefore
must be high. Consecutive singletons of the same side are
impossible: their positive first-six magnitudes \(a,a'\)
would differ by the slot step, which is smaller than 4,
whereas distinct full first-six magnitudes differ by at
least 6. Thus four consecutive singleton slots would
alternate high/low, and their endpoints could not both
be high. Exactly one singleton and one trio occur, and
the singleton must be at an endpoint, either 55 or 58.
In particular it is high. With \(S_6=\sum_{i=1}^6x_i\),
its first-six magnitude is \(a=3X+D_r\), implying the
necessary affine root row
\[
\boxed{S_6\ge3X+109}
\]
since \(r\ge55\) and \(D_{55}\ge109\).

The remaining trio must be two-plus. An adjacent
one-plus trio with center \(D_c\) would correspond to the
positive first-six magnitude \(b=X+D_c\), and the high
singleton would give
\((a-b)/2=X+(D_r-D_c)/2\) in the same impossible
middle forbidden window. Therefore there is a fifth
distinct *small* full first-six magnitude \(X-D_c\):
it is in \([36,38)\) if the trio center is 56, or
\([34,36)\) if the center is 57.

One further exact signed-support relation useful later:
\[
t_1=(b_{50}-b_{53})/2,\qquad t_2=(b_{60}-b_{63})/2
\]
both lie in \([3,4)\) (two exact trio steps and one
inter-trio step in \([2,4)\)). If their signed support words
are distinct, they must have opposite signs on some
shared coordinate: otherwise their difference is a
nonzero \(\{-1,0,1\}^6\) form with absolute value below 1,
contradicting first-six separation at least 3. No extra
claim is made from the separate high-band avoidance:
since the first-six forbidden pair-sum window is only
\((2X-2,2X+2)\), its matching half-forms can give merely
a slot difference at least 4, already following from two
rank steps in the applications above.

## 4. Consequences for central orientations

The central positive top signs must belong to
\(+++\), \(++-\), \(+--\), \(---\): a trio containing
\(D_1\) begins there, so contributes only its first pattern.
Let \(P,N\) be the sums of the positive and negative sides
of the central first-six signs, respectively, and let
\(g=D_1\in[1,2)\). Expanding the displayed total lower
bound by the signed central equation yields:

| Central top signs | Necessary condition |
|---|---|
| \(++-\) | \(P\ge X+(111+g)/2\ge X+56\) |
| \(+--\) | \(N\ge X+(107-g)/2>X+52.5\) |
| \(+++\) | \(P\ge(109+g)/2\ge55\) |
| \(---\) | \(N\ge(109-g)/2>53.5\) |

Thus for the fixed earlier pilot orientation with word
\(\texttt{-----+++-}\), the only positive sign in the
first six is \(x_6\), contradicting the \(++-\) row.
Equivalently its central identity gives
\(S_6=2x_6+X-g-2<3X\). This independently clears that
central orientation's **close branch**, and in particular
all earlier live pairs of it that force the close branch.
It does not clear the wide branch, or any whole orientation.

The additional LP screen tests only \(S_6\ge3X+109\)
over the previous close root relaxations. The explicitly
listed structural identities are written mathematics,
not an LP enumeration or Lean formalization.
