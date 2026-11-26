"""Fill the %TABLES%, %BOUND%, %CMIN% and %CMAX% placeholders of the research note.

Usage: python fill_tables.py summary.json template.tex out.tex BOUND_TEX
"""
import json
import math
import sys

summary_path, template_path, out_path, bound_tex = sys.argv[1:5]
summary = json.load(open(summary_path))
rows, cs = [], []
for k, v in sorted(summary["dyadic"].items(), key=lambda kv: int(kv[0])):
    k = int(k)
    if k < 16 or v["n_min_ratio"] is None:
        continue
    lo, hi = 2**k, 2 ** (k + 1)
    if hi > summary["hi"]:
        continue  # skip a dyadic range the run did not finish
    n, r = v["n_min_ratio"], v["min_ratio"]
    c = (1 - r) * n**0.25 / math.log(n) ** 1.5
    if k >= 24:
        cs.append(c)
    rows.append(f"{k} & {v['min_G']} & {n} & {r:.4f} & {c:.3f} \\\\")

table = "\n".join([
    "\\begin{table}[ht]",
    "\\centering\\small",
    "\\begin{tabular}{rrrrr}",
    "\\toprule",
    "$k$ & $\\min G$ & $n$ attaining $\\min G/\\sqrt n$ & $r=\\min G/\\sqrt n$ & $\\hat C$ \\\\",
    "\\midrule",
    *rows,
    "\\bottomrule",
    "\\end{tabular}",
    "\\caption{Minima over $2^k\\le n<2^{k+1}$. The column $\\min G$ is the minimum of $G$ "
    "itself, which may be attained at a different $n$.}",
    "\\label{tab:ratio}",
    "\\end{table}",
])
tex = open(template_path, encoding="utf-8").read()
tex = (tex.replace("%TABLES%", table).replace("%BOUND%", bound_tex)
       .replace("%CMIN%", f"{min(cs):.2f}").replace("%CMAX%", f"{max(cs):.2f}"))
open(out_path, "w", encoding="utf-8", newline="\n").write(tex)
print(f"{len(rows)} rows; C-hat range {min(cs):.3f}..{max(cs):.3f}")
