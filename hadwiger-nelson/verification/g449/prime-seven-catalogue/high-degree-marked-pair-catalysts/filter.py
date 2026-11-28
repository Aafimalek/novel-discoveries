#!/usr/bin/env python3
"""One exact prioritized filter of two-grid-addition distance-2 terminal gadgets."""
from argparse import ArgumentParser
from pathlib import Path
from hashlib import sha256
from collections import Counter
import json
from audit_layers import sub
from rotation_bank import load_data,key,absent
from census import flags

TERMINALS='ed3da1a1210f3148924cf7dfde172a69673c6ecf1a5674c877bff3dc8867f4df'
PALETTES='6ada0cb4253e7bad57cedc7a732485bdbca2d6e8ccc79b1b9d48a9257d180888'
GRID='f944eea2d111cbe242c3b223155ade4f150e9a9da912795a1b57e956bebdcec9'
PROFILE='7b04a25fa89bb03d290a7288c10087f2afca2b4f58821b151e6a330dadf2fbf4'

def read(path,pin):
    z=path.read_bytes()
    assert sha256(z).hexdigest()==pin,path
    return z

def first(m):
    return (m&-m).bit_length()-1

def main():
    p=ArgumentParser(description=__doc__)
    for name in ('base','catalogue','grid','profile','terminals','palettes','fresh_outdir'):
        p.add_argument(name,type=Path)
    a=p.parse_args()
    G,initial,E,D=load_data(a.base,a.catalogue)
    raw=json.loads(read(a.palettes,PALETTES))
    P=[tuple(map(int,p['colors'])) for p in raw['palettes']]
    assert len(P)==61 and P[0]==initial
    assert all(len(c)==449 and set(c)==set(range(5)) and all(c[i]!=c[j] for i,j in E) for c in P)
    T=json.loads(read(a.terminals,TERMINALS))
    assert T['counts']['exact_distance_two']==len(T['true_pairs'])==861
    Z=[tuple(map(int,x.split())) for x in read(a.grid,GRID).splitlines()]
    assert len(Z)==len(set(Z))==7056 and all(len(q)==12 for q in Z)
    R=read(a.profile,PROFILE).splitlines()
    assert R[0]==b'7056 61 33908' and len(R)==1+7056+33908
    rows=[tuple(map(int,s.split())) for s in R[1:7057]]
    assert all(len(row)==62 and 2<=row[0]<=9 for row in rows)
    ids=[j for j,row in enumerate(rows) if row[0]>=4]
    assert len(ids)==1043 and sum(rows[j][0]>=5 for j in ids)==574
    bounds=lambda Q:max(abs(x) for q in Q for x in q)
    # To compare a computed z+d to original x by key, even the difference
    # has magnitude strictly <256 in every signed base-256 coordinate.
    assert bounds(G)+bounds(Z)+bounds(D)<256 and 2*bounds(Z)<256
    orig_key={key(q):i for i,q in enumerate(G)}
    offsets=tuple(map(key,D))
    assert len(orig_key)==449 and len(set(offsets))==546
    # Verify original-neighbor lists directly via signed geometry, not stored
    # witness incidence or the palette profile that the lookups are compared to.
    ns={j:tuple(sorted(orig_key[r] for d in offsets if (r:=key(Z[j])+d) in orig_key)) for j in ids}
    box={}
    for j in ids:
        n=ns[j]
        assert len(set(n))==len(n)==rows[j][0]
        lists=tuple(absent(n,c) for c in P)
        assert lists==rows[j][1:]
        B=0
        Bc=[0]*5
        for k,L in enumerate(lists):
            if L:B|=1<<k
            for c in range(5):
                if L&~(1<<c):Bc[c]|=1<<k
        box[j]=(lists,B,Bc)
    T=[r for r in T['true_pairs'] if len(r['original_neighbors_of_new'])>=5]
    assert Counter(len(r['original_neighbors_of_new']) for r in T)=={5:21,6:14}
    assert all(r['reflected_through'] is None for r in T)
    assert len({(r['original'],r['new_grid_id']) for r in T})==35
    a.fresh_outdir.mkdir(exist_ok=False)
    stats=Counter()
    with (a.fresh_outdir/'positive.jsonl').open('w') as yes, (a.fresh_outdir/'residual.jsonl').open('w') as no:
        for t in T:
            x,z=t['original'],t['new_grid_id']
            assert G[x]==tuple(t['original_numerator']) and Z[z]==tuple(t['new_numerator'])
            assert tuple(t['original_neighbors_of_new'])==ns[z]
            assert flags(sub(Z[z],G[x]))==(False,True)
            Az=[0]*5
            for k,c in enumerate(P):
                if box[z][0][k]&(1<<c[x]):Az[c[x]]|=1<<k
            common=sum(Az)
            assert common and (common>>t['same_color_palette'])&1
            for w in ids:
                stats['raw']+=1
                if w==z:
                    stats['collision']+=1
                    continue
                d=sub(Z[w],Z[z])
                adj=d in D
                # Independently recompute integer Laurent norm for each pair;
                # this is the kernel of all claimed new edge checks.
                assert flags(d)[0]==adj
                L,B,Bc=box[w]
                if adj:
                    M=0
                    for c in range(5):M|=Az[c]&Bc[c]
                    stats['adjacent']+=1
                else:
                    M=common&B
                    stats['nonadjacent']+=1
                greedy=not adj and len(ns[w])==4
                if greedy:
                    assert B==(1<<61)-1 and M==common
                    stats['degree4_nonadjacent_greedy']+=1
                if not M:
                    stats['residual']+=1
                    record={'x':x,'z':z,'w':w,'x_numerator':G[x],
                            'z_numerator':Z[z],'w_numerator':Z[w],
                            'z_original_neighbors':ns[z],'w_original_neighbors':ns[w],
                            'adjacent':adj,'A_by_color':Az,'B':B,'Bc':Bc}
                    no.write(json.dumps(record,separators=(',',':'))+'\n')
                    continue
                k=first(M); cx=P[k][x]
                lw=L[k]&(~(1<<cx) if adj else 31)
                cw=first(lw)
                assert 0<=k<61 and 0<=cx<5 and 0<=cw<5
                assert all(P[k][v]!=cx for v in ns[z])
                assert all(P[k][v]!=cw for v in ns[w])
                assert (not adj) or cx!=cw
                # Original graph proper is independently checked above;
                # these are every remaining edge of its exact two-site extension.
                yes.write(json.dumps([x,z,w,k,cx,cw],separators=(',',':'))+'\n')
                stats['positive']+=1
    assert stats['raw']==35*1043==stats['collision']+stats['positive']+stats['residual']
    assert stats['raw']==stats['collision']+stats['adjacent']+stats['nonadjacent']
    r={'stats':dict(sorted(stats.items())), 'terminal_count':35, 'high_degree_catalysts':1043,
       'positive_sha256':sha256((a.fresh_outdir/'positive.jsonl').read_bytes()).hexdigest(),
       'residual_sha256':sha256((a.fresh_outdir/'residual.jsonl').read_bytes()).hexdigest()}
    (a.fresh_outdir/'summary.json').write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps(r,indent=2))

if __name__=='__main__':main()
