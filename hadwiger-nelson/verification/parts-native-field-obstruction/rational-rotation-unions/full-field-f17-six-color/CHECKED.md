# Six-color finite residue certificate over F17
One exact standalone attempt passed in 4.60 s wall (4.26 user,
0.30 sys), Lean 4.36.0, import Init only, -j1 -M1100,
-DwarningAsError=true, ordinary kernel decide (no native).
The compiler object used the same supplied 17 rows as colors.txt.
The generator packs row b into a radix-8 natural with column a at
digit a, and independently verifies every unpacked digit matches
the supplied table. The Lean color is typed Fin 6. Subtraction in
the norm hypothesis is modular, and all coordinate types are Fin 17.

Checked result HadwigerNelson.F17Residue.proper_norm_one_difference:
for all a,b,a',b' : Fin 17, writing da=(a'+17−a) mod 17 and
db=(b'+17−b) mod 17, if da²+3 db² = 1 mod 17, then
color a b ≠ color a' b'. The exact named theorem has only the existing
standard Lean axioms propext and Quot.sound (no Classical.choice,
native_decide, or added axioms). hasDirection checks all norm-one
differences lie in the literal 18-entry direction list. Row properties
are separately checked by ordinary decide. Independent external
enumeration found and checked all 2,601 unordered edges on 289 vertices.

This is a finite residue graph theorem. The claim that it transfers to
the complex field Q(sqrt(-3),sqrt(33),sqrt(-7)) via 17-adic valuation
is a separate written argument, not this Lean theorem. No lower bound,
sharpness assertion, or new determination for the unrestricted plane.
