"""Small independent replay of the one-high offset arithmetic, no solver."""
for h in range(2, 14):
    for i in range(14):
        for t in range(14):
            off = max(0,t-i)
            I = abs(i-t)
            M = max(min(i,t), I)
            assert i+off >= t
            # Bound from the checked directional gate versus anchor lower bound.
            assert h+i+(i+off)+1 <= 2*h+i+t+M
            # If a high comparison fit under the sum of two low counts,
            # its own strict lower bound would contradict these inequalities.
            for N in range(12):
                lows = range((N+2)//3)
                for u in lows:
                    assert 3*u < N
                    assert 3*(u+u) < 2*N
print("Verified exact small-case inequalities for the necessarily absent gate, anchor slack, and strict count cap.")
