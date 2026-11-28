# Block-degree deficits at exactly five isolates

For a ground-minimal weak height-six family with five isolates and at
least two forcing centers, the [proof](theorem-note.md) forces the
maximum block-degree deficit to be at most two. If it equals two,
at most six centers have deficit two and the omitted-block design
loses fewer than k+10 blocks compared with an all-pair design on k centers.

[Paper PDF](paper/exactly-five-isolates.pdf) · [TeX](paper/exactly-five-isolates.tex)

The proof uses a finite integer replay in the high-deficit cases.
The replay rejects all 75 eligible rows and requires only Python:

```sh
python3 deficit_replay.py
sha256sum --strict -c SHA256SUMS
```

The prior [four-isolate reduction](../exactly-four-isolates/) remains
separate. This paper neither closes the five-isolate case nor changes
the lower bound of four isolates. Its new results are not Lean theorems.
