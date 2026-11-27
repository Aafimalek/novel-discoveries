"""Shards may use different cutoff certificates; reuse the checked 120,119 slice."""
from pathlib import Path
import json, sys
a=int(sys.argv[1])
assert a in (119,120)
data=json.loads(Path('fourpoint-data.json').read_text())
B=min(d['bound'] for d in data if d['a']==a)
lo=next(b for b in range(7,a) if 148+a+sum(b-j for j in range(7))>=511
     and 148**2+a*a+sum((b-j)**2 for j in range(7))>=B)
ranges=dict([[119,[(105,112),(112,114),(114,115),(115,116),(116,117),(117,118),(118,119)]],
             [120,[(105,112),(112,114),(114,115),(115,116),(116,117),(117,118),(118,119)]]])[a]
assert ranges[0][0]==lo and ranges[-1][1]==119
assert all(x[1]==y[0] for x,y in zip(ranges,ranges[1:]))
p=Path('NineSeparatedSubsetSums')
names=[]
for i,(start,stop) in enumerate(ranges):
 n=f'FixedThird{a}Part{i}';w=stop-start;names.append(n)
 p.joinpath(n+'.lean').write_text(f'''import NineSeparatedSubsetSums.CachedFixedThird
open NineSeparatedSubsetSums
set_option maxRecDepth 47000 in
set_option maxHeartbeats 300000000 in
theorem fixedThird{a}Part{i} : ∀ t : Fin {w},
    cachedFixedThirdShard {a} ({start}+t.val) {B} = false := by decide +kernel
#print axioms fixedThird{a}Part{i}
''')
name=f'FourPoint{a}CachedShard'
head=f'import NineSeparatedSubsetSums.FourPoint{a}Checked\n'
if a==120:head+='import NineSeparatedSubsetSums.EightPoint120_119Shard\n'
s=head+''.join(f'import NineSeparatedSubsetSums.{n}\n' for n in names)+f'''
namespace NineSeparatedSubsetSums

theorem fourPoint{a}_no_descending_tail : NoDescendingTail {a} := by
  apply noDescendingTail_of_third_tails {a} {B} max148_second{a}_fourPoint_moment_bound
  intro b hlo hhi
  have h0 : cachedThirdLower {a} {B} = {lo} := by decide +kernel
  rw [h0] at hlo
'''
if a==120:
 s+=f'''  by_cases h120 : b=119
  · subst b
    exact eightPoint120_119_no_descending_tail
'''
s+=f'''  have upper : b < 119 := by omega
  apply noDescendingThirdTail_of_cached {a} b {B}
  · intro t ht hd
    exact max148_second{a}_fourPoint_moment_bound (b::t) (by simp [ht]) hd
'''
for i,(start,stop) in enumerate(ranges):
 w=stop-start
 last=i+1==len(ranges)
 if not last:
    s+=f'  by_cases q{i} : b < {stop}\n  · '
 else:s+='  '
 indent='  ' if last else '    '
 s+=f'''let j : Fin {w} := ⟨b-{start}, by omega⟩
{indent}have hj : {start}+j.val=b := by dsimp [j]; omega
{indent}have ok := fixedThird{a}Part{i} j
{indent}simpa only [hj] using ok
'''
s+=f'''
#print axioms fourPoint{a}_no_descending_tail
end NineSeparatedSubsetSums
'''
p.joinpath(name+'.lean').write_text(s)
print(*names,name)
