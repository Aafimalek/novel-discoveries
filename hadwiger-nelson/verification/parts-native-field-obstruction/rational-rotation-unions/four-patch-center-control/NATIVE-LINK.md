# Classification of native-linked cross rhombi in the three copies

**Scope.** Consider four distinct, nonzero vertices of a
unit four-cycle in K ∪ ρK ∪ ρ²K, where
K=Q(√33,√−3) and ρ=(31+3√−7)/32. A native edge has
both endpoints in the same copy. If the cycle has at
least one native edge and uses more than one copy,
then, up to the normalizations described below,
it is the positive-real anchor rhombus with native outer
edge endpoints S,S+1, and other sites ρT,ρ², where
T=31/16 and S=449/256. In particular no such cycle with
three cross edges has its native edge in the middle copy.
All-native cycles are not restricted by this statement;
all-cross cycles and cycles through the common origin
are not classified here. This is a written argument,
not a Lean theorem.

## Proof

Any unit four-cycle on four distinct points is a rhombus:
opposite vertices are the two distinct intersections of
the unit circles centered at the other two vertices, so
the opposite pairs have the same midpoint. In this
ambient set, distinct copies meet only at zero. Unit
cross distances imply the native representatives are
collinear, by the exterior radical coefficient in the
exact squared norm (see the
[rational-rotation note](https://github.com/Aafimalek/novel-discoveries/blob/0bf59bc95f82db5764382256922a9847191a2c1f/hadwiger-nelson/verification/parts-native-field-obstruction/rational-rotation-unions/README.md)).

There cannot be exactly one cross edge on a cycle, as a
cycle's label must return to its initial copy. If there
are exactly two cross edges, two copies occur. For a
2+2 split the native edges are opposite, so their equal
nonzero displacements would belong to the intersection
of two copies, impossible. For a 3+1 split, the foreign
vertex is the sum of the two opposite native vertices
minus the third native vertex by parallelogram identity.
It therefore belongs to their copy, again impossible
for a foreign nonzero vertex.

The only remaining case has exactly three cross edges,
one native edge, and all three copies. Rotate the copy
of the native edge to K, and multiply by the inverse of
its native unit displacement. Do not translate. The
two native endpoints are now A,A+1. Along the three
cross edges all four native representatives are
collinear through zero, because all are nonzero. As
A and A+1 differ by 1, they are all real and hence in
the real subfield Q(√33). Label the cycle in order
A,A+1,RY,S'Z, with R,S' the moved rotations of the
two other copies. The rhombus equation is

    RY−S'Z=1.

Reversing the path by starting at the other native
endpoint and renormalizing its direction exchanges the
order of R,S' and sends the normalized edge endpoints
to −A−1,−A. If the original native side is copy 2,
complex conjugation after rotation to K exchanges
negative powers with positive. Thus in either outer
case one may use R=ρ, S'=ρ². Since ρ²=Tρ−1 and ρ∉K,
comparison gives Y=T and Z=1. The remaining adjacent
side to A has norm |A−ρ²|=1, giving
A(A−2Re(ρ²))=0. The solution A=0 was excluded, and
2Re(ρ²)=449/256=S. This is the stated anchor.

In the middle-native case the relative phases are ρ and
ρ⁻¹. After exchanging path order if needed, use R=ρ
and S'=ρ⁻¹=T−ρ. Then Y=1/T and Z=−1/T. The remaining
unit equation is |A+ρ⁻¹/T|²=1, or
A²+A+1/T²=1. Its discriminant is 3781/961.
The integer 3781 sits strictly between 61² and 62²
and is prime to 3, so it is neither a rational square
nor 33 times a rational square. A rational number
has a square root in Q(√33) only in those two cases
(compare coefficients after squaring a+b√33).
Therefore the middle case has no solution. ∎
