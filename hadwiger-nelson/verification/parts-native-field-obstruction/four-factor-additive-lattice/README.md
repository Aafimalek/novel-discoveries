# The αβ factor still cannot create a mixed-summand unit edge

Let s=√−3, r=√33, h=√−7, with imaginary radicals chosen positive.
Set ω=(1+s)/2, Λ=Z[ω], α=(r+s)/6, β=(3+h)/4. Write N(z)=z·conj(z).
Both α, β have norm one. This note extends the earlier
[three-factor theorem](https://github.com/Aafimalek/novel-discoveries/blob/8be0f5af188954944d37043740b20aeaf1a0c2bf/hadwiger-nelson/verification/parts-native-field-obstruction/mixed-additive-lattice/INFINITE-CARTESIAN.md).

**Theorem.** The unit-distance graph on
M₄=Λ+αΛ+βΛ+αβΛ is exactly the Cartesian product of four triangular
lattice graphs. In particular adding αβΛ creates no mixed-summand
unit edge. Its chromatic number is three, and a chosen nonunit
pair can always share a color in a proper four-coloring.

## Norm decomposition

The square classes of -3,33,-7 are independent: primes 11 and 7
detect the latter two classes, and -3 is not a rational square.
The four quantities 1,r,h,rh are consequently independent over
Q(s). If t,u,v,w∈Λ, expand the displacement d by

    24 d = a + r b + h c + rh e,
    d = t + αu + βv + αβw,
    a = 24t + 4su + 18v + 3sw,
    b = 4u + 3w,
    c = 6v + sw,
    e = w.

All four coefficients lie in Λ. Their separate uniqueness, and
then the triangular equations for w,u,v,t, prove the summand
representation is unique.

Complex conjugation fixes r and negates h. The constant component
of N(24d) is

    N(a)+33N(b)+7N(c)+231N(e).

The other three independent components are multiples of r, hs,
and rhs. For the norm to be rational their vanishing is exactly

    Re(a·conj(b)) + 7 Re(c·conj(e)) = 0,
    Im(c·conj(a)) + 33 Im(e·conj(b)) = 0,
    Im(e·conj(a)) + Im(c·conj(b)) = 0.

Here each coefficient taken before the real radical, or after
division by s following an imaginary radical, is rational.
For unit distance the displayed constant must be 576.

## The new branch e≠0

If e=w=0, use the earlier three-factor theorem. Now suppose w≠0.
Since 231N(w)≤576, the positive integer N(w) is one or two.
But for any m+nω, N=m²+mn+n² ≡ (m−n)² mod 3, so two is impossible.
Multiply the entire displacement and all four summands by
conj(w)∈Λ, preserving the norm and normalizing w=e=1.

Now b≡3 mod 4Λ and N(b)≤(576−231)/33=345/33<11. If
b=m+nω and n is nonzero, then n is a multiple of four and
|Im(b)|²=3n²/4≥12, impossible. Thus b is an integer, and the
norm bound and its residue modulo four give b=3 or b=−1.

### Case b=3

Then u=0 and 7N(c)≤576−231−33·9=48. If v=m+nω then

    c = 6m+3n+(3n+1)s.

For n≠0 its squared imaginary component is at least 12, larger
than 48/7. Hence n=0, and m≠0 would give squared real component
at least 36. Thus v=0, c=s, and the constant-norm equation gives
N(a)=576−231−297−21=27. Since a=24t+3s, any nonzero t∈Λ satisfies
|a|≥24−3√3>3√3. Therefore t=0. This is exactly the pure αβ unit
step in the normalized configuration.

### Case b=−1

Here u=−1. From the three cross identities with e=1 one obtains

    Re(a)=7 Re(c),
    Im(c·conj(a))=0,
    Im(a)=−Im(c).

Write c=x+iy. As above y=(3n+1)√3 for some integer n, so y≠0.
Then a=7x−iy and the middle cross identity gives 8xy=0.
It follows that x=0 and N(a)=N(c). Since `Re(c)=0`,
the element v is purely imaginary in Λ, hence v=ks with k∈Z:
a lattice coordinate m+nω with zero real part has n even.
Thus c=(6k+1)s. The constant-norm equation now reads

    8N(c) = 576−231−33 = 312

Thus N(c)=39, so (6k+1)²=13.
This is impossible for an integer k. Thus b=−1 gives no unit
displacement.

## Graph and coloring

We have classified every unit step: it changes exactly one of
t,u,v,w by a unit of Λ. Conversely any such step is unit because
α, β and αβ have norm one. Together with uniqueness of the
representation this is the claimed graph isomorphism. On each
unrotated factor use color m+2n mod 3 for m+nω and sum the four
factor colors; each edge changes one summand color nontrivially.
A triangle in the first factor proves sharpness at three colors.
To make any chosen nonadjacent pair equal, give just those two
vertices a fresh fourth color.

So neither this four-factor additive module nor any of its subsets
can realize the desired six-chromatic unit-only witness or a
five-color gadget that forces a marked nonunit pair apart. No
claim is made about multiplicative saturation or other rotations.
For example α² and β² satisfy
α²=1+(s/3)α and β²=−1+(3/2)β; these lie outside this integral
module and are not covered. No production search, SAT, Lean,
or Git was used.
