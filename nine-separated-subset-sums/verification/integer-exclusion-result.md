# Completed local integer computation

Compiled with `g++ -std=c++17 -O3 -Wall -Wextra` and ran the exact exhaustive checker over maxima 1 through 148. Exit status: 0, no witness. Final counts:

```
Cleared through 148 nodes by remaining depth: 0 372311181 1440092003 163901849 9644018 520288 26866 1244 148 0
```

These are independent computational checks, not a substitute for a Lean certificate. See [the algorithm and its pruning rules](integer-exclusion-notes.md).
