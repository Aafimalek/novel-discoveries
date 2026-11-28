"""Compute the additive leaf-avoidance size terms for the nine profiles."""
PROFILES = ((0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15), (0, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15), (0, 2, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 15), (2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15), (2, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 15), (2, 3, 4, 6, 7, 10, 11, 12, 13, 14, 15), (2, 4, 6, 7, 10, 11, 12, 13, 14, 15), (2, 6, 7, 10, 11, 12, 13, 14, 15), (2, 6, 7, 10, 11, 14, 15))

terms=[]
for masks in PROFILES:
    gamma=[sum(bool(t & (1<<i)) for t in masks) for i in range(4)]
    terms.append(min(2*gamma[0]+5, *(2*c+7 for c in gamma[1:])))
assert terms==[19,17,15,17,15,15,13,13,11]
print('Additive terms in canonical profile order:',terms)
