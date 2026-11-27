#!/usr/bin/env python3
"""Confirm the separate exact prefix and suffix audits cover the same originals with no gap."""
import re,sys
from pathlib import Path
pre_re=r"^(.*): exact non-lex prefix (\d+), archived lex suffix (\d+); original SHA-256 (\w+); prefix SHA-256 (\w+)$"
suf_re=r"^(.*): exact lex suffix (\d+); original SHA-256 (\w+); suffix SHA-256 (\w+)$"
pres={}
for line in Path(sys.argv[1]).read_text().splitlines():
    case,pre,n,dig,_=re.fullmatch(pre_re,line).groups()
    assert case not in pres
    pres[case]=(int(pre),int(n),dig)
assert len(pres)==17
for line in Path(sys.argv[2]).read_text().splitlines():
    case,n,dig,_=re.fullmatch(suf_re,line).groups()
    pre,n2,dig2=pres.pop(case)
    assert int(n)==n2 and dig==dig2
    print(f"{case}: {pre}+{n2}={pre+n2} exact modeled rows; original SHA-256 {dig}")
assert not pres
