"""Plan exact Lean shelf checking with auditable adaptive subtree splits.

This generates proof *inputs*, not proof results. Use run-adaptive-queue.py
and require success of the final shelf theorem before marking coverage.
"""
import argparse, fcntl, json, os, subprocess, sys
from pathlib import Path

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('a',type=int)
p.add_argument('--third',type=int,action='append',
               help='Only generate these representative third weights; no shelf theorem.')
p.add_argument('--cost',type=int,default=1700,
               help='Target maximum heuristic C++ states per numeric leaf.')
p.add_argument('--oct-cost',type=int,default=6000,
               help='Try an eight-point cutoff above this old work estimate.')
p.add_argument('--no-oct',action='store_true')
p.add_argument('--out',default=None)
p.add_argument('--repo',default='.')
opt=p.parse_args()
a=opt.a
assert 114<=a<=147 and min(opt.cost,opt.oct_cost)>0
src=Path(opt.repo).resolve()
d=src/'NineSeparatedSubsetSums'
d.mkdir(parents=True,exist_ok=True)
planlock=(src/f'.adaptive-shelf-{a}.lock').open('w')
fcntl.flock(planlock,fcntl.LOCK_EX|fcntl.LOCK_NB)
out=Path(opt.out or f'adaptive-{a}.json')
data=json.loads((src/'fourpoint-data.json').read_text())
four=min(x['bound'] for x in data if x['a']==a)
rootenv=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1')
def invoke(*argv):
    return subprocess.check_output([str(x) for x in argv],cwd=src,env=rootenv,text=True)
def memo(fn):
    from functools import lru_cache
    return lru_cache(maxsize=None)(fn)

@memo
def estimate(B,hist):
    count, found=map(int,invoke('./bench-plan',B,*hist).split())
    if found:
        raise RuntimeError(f'heuristic search reported witness: {B},{hist}')
    return count

def moments(h,k,hi):
    u=sum(h)+sum(max(hi-j,0) for j in range(k))
    q=sum(w*w for w in h)+sum(max(hi-j,0)**2 for j in range(k))
    return u,q
def cutoff(B,h,hi):
    k=9-len(h)
    def good(x):
        s,q=moments(h,k,x)
        return s>=511 and q>=B
    def rec(fuel,l,u):
        if not fuel or u<=l:return l
        mid=(l+u)//2
        return min(mid,rec(fuel-1,l,mid)) if good(mid) else rec(fuel-1,mid+1,u)
    return rec(hi.bit_length(),k,hi)
def child_choices(B,h):
    k=9-len(h)
    hi=h[-1]-1
    if k<3:return []
    s,q=moments(h,k,hi)
    if s<511 or q<B:return []
    D=1
    for w in h: D|=(D<<w)|(D<<(2*w))
    lo=cutoff(B,h,hi)
    return [j for j in range(lo,hi+1) if ((D>>(sum(h)+j))&1)==0]

def write(n, imports, text):
    (d/(n+'.lean')).write_text(''.join(f'import NineSeparatedSubsetSums.{i}\n' for i in imports)
                  +'\nnamespace NineSeparatedSubsetSums\n\n'+text+'\nend NineSeparatedSubsetSums\n')
def add(n):
    if n not in names:names.append(n)
def add_names(seq):
    for n in seq:add(n)

names=[]
add_names(invoke(sys.executable,'make-packed-shards.py',a).split())
lower=cutoff(four,(148,a),a-1)
selected=opt.third or list(range(lower,a))
assert all(lower<=b<a for b in selected) and selected==sorted(set(selected))
meta=[]
tops=[]
S='set_option maxRecDepth 47000 in\nset_option maxHeartbeats 300000000 in\n'
for b in selected:
    tag=f'Adaptive{a}Third{b}'
    root=(148,a,b)
    weak=estimate(four,root)
    B=four
    oct_name=None
    if not opt.no_oct and weak>=opt.oct_cost:
        numpath=f'oct-data-{a}-{b}.json'
        if not (src/numpath).exists():
            (src/numpath).write_text(invoke(sys.executable,'find-eightpoint.py',a,b))
        bd=json.loads((src/numpath).read_text())
        B=max(four,min(z['bound'] for z in bd))
        if B>four:
            oct_name=f'EightPoint{a}_{b}Checked'
            add_names(invoke(sys.executable,'make-eight-packed-shards.py',a,b,numpath).split())
    id_of={root:0}
    defs=[f'def {tag}Node0 : CachedSearchNode :=\n  ⟨4, {b-1}, computeCenteredMask [148,{a},{b}], {148+a+b}, {148**2+a*a+b*b}⟩\n']
    stats=dict(nodes=0,leaves=0,max_leaf=0,largest_fanout=0)
    pending=[]
    def emit(h):
        i=id_of[h]
        n=tag+f'Proof{i}'
        est=estimate(B,h)
        children=child_choices(B,h) if est>opt.cost and len(h)<7 else []
        children=[(x,h+(x,)) for x in children]
        stats['nodes']+=1
        stats['largest_fanout']=max(stats['largest_fanout'],len(children))
        body=f'theorem {n[0].lower()+n[1:]} : runCachedNode 511 {B} {tag}Node{i} = false := by\n'
        imp=[]
        if not children:
            stats['leaves']+=1
            stats['max_leaf']=max(stats['max_leaf'],est)
            body=S+body+'  decide +kernel\n'
        else:
            for x,h2 in children:
                j=len(id_of)
                id_of[h2]=j
                defs.append(f'def {tag}Node{j} : CachedSearchNode := cachedChild {tag}Node{i} {x}\n')
                imp.append(emit(h2))
            body+=f'''  apply runCachedNode_false_of_children
  · decide +kernel
  intro x hx
  have selected : cachedChildChoices 511 {B} {tag}Node{i} = {list(x for x,_ in children)} := by decide +kernel
  rw [selected] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
'''
            body+= ('  rcases hx with '+' | '.join('rfl' for _ in children)+'\n'
                    if len(children)>1 else '  subst x\n')
            pref='  · ' if len(children)>1 else '  '
            for dep in imp:
                body+=pref+f'exact {dep[0].lower()+dep[1:]}\n'
        pending.append((n,imp,body+f'\n#print axioms {n[0].lower()+n[1:]}\n',est))
        return n
    theorem=emit(root)
    write(tag+'State',['CachedSearchTree'],''.join(defs))
    add(tag+'State')
    # Batch independent leaves while preserving the numerical cap per
    # compiled file. Join proofs are then grouped in postorder.
    home={}
    bins=[]
    for row in sorted((x for x in pending if not x[1]),key=lambda x:-x[3]):
        est=row[3]
        for bucket in bins:
            if bucket[0]+est<=opt.cost and len(bucket[1])<32:
                bucket[0]+=est;bucket[1].append(row);break
        else:
            bins.append([est,[row]])
    for i,(est,rows) in enumerate(bins):
        m=tag+f'Leaves{i}'
        write(m,[tag+'State'],'\n'.join(x[2] for x in rows))
        add(m)
        for row in rows:home[row[0]]=m
    joins=[x for x in pending if x[1]]
    for start in range(0,len(joins),8):
        rows=joins[start:start+8];m=tag+f'Joins{start//8}'
        for row in rows:home[row[0]]=m
        deps=list(dict.fromkeys(home[y] for x in rows for y in x[1] if home[y]!=m))
        write(m,[tag+'State']+deps,'\n'.join(x[2] for x in rows))
        add(m)
    stats['leaf_modules']=len(bins)
    stats['join_modules']=(len(joins)+7)//8
    moment=f'max148_second{a}_third{b}_eightPoint_moment_bound' if oct_name else (
        f'(fun t ht nd => max148_second{a}_fourPoint_moment_bound ({b}::t) (by simp [ht]) nd)')
    imp=[home[theorem],'CachedFixedThird',oct_name or f'FourPoint{a}Checked']
    write(tag,imp,f'''
theorem {tag[0].lower()+tag[1:]} : NoDescendingTailAfterThird {a} {b} :=
  noDescendingThirdTail_of_cached {a} {b} {B} {moment} {theorem[0].lower()+theorem[1:]}

#print axioms {tag[0].lower()+tag[1:]}
''')
    add(tag);tops.append((b,tag))
    meta.append(dict(b=b,fourpoint_nodes=weak,cutoff=B,eight_point=bool(oct_name),
                     estimated_nodes=estimate(B,root),**stats))
final=None
if not opt.third:
    final=f'AdaptiveShelf{a}'
    s=f'''
theorem adaptiveShelf{a}_no_descending_tail : NoDescendingTail {a} := by
  apply noDescendingTail_of_third_tails {a} {four} max148_second{a}_fourPoint_moment_bound
  intro b hlo hhi
  have cut : cachedThirdLower {a} {four} = {lower} := by decide +kernel
  rw [cut] at hlo
'''
    for b,tag in tops[:-1]:
        s+=f'  by_cases h{b} : b = {b}\n  · subst b; exact {tag[0].lower()+tag[1:]}\n'
    if tops:
        b,tag=tops[-1]
        s+=f'  have hlast : b = {b} := by omega\n  subst b\n  exact {tag[0].lower()+tag[1:]}\n'
    else:s+='  omega\n'
    s+=f'\n#print axioms adaptiveShelf{a}_no_descending_tail\n'
    write(final,[f'FourPoint{a}Checked','CachedFixedThird']+[n for b,n in tops],s)
    add(final)
known=set(names)
jobs={}
for n in names:
    imports=[]
    for line in (d/(n+'.lean')).read_text().splitlines():
        if line.startswith('import NineSeparatedSubsetSums.'):
            x=line.removeprefix('import NineSeparatedSubsetSums.').strip()
            if x in known:imports.append(x)
    jobs[n]=imports
out.write_text(json.dumps(dict(second=a,fourpoint=four,lower=lower,final=final,
                        targets=[n for _,n in tops],branches=meta,modules=jobs),indent=2)+'\n')
print(out, len(jobs),'modules')
