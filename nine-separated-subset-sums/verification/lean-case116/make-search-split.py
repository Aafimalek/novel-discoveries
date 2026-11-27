"""Generate a formal third-weight split when the whole checker times out."""
from pathlib import Path
import json,sys
a=int(sys.argv[1]); width=int(sys.argv[2]) if len(sys.argv)>2 else 4
B=min(d['bound'] for d in json.loads(Path('fourpoint-data.json').read_text()) if d['a']==a)
d=Path("NineSeparatedSubsetSums")
T=next((b for b in range(7,a) if 148+a+sum(b-j for j in range(7))>=511
  and 148**2+a*a+sum((b-j)**2 for j in range(7))>=B),a)
N=a-T
parts=[]
for lo in range(0,N,width):
    w=min(width,N-lo); q=len(parts)
    name=f"CachedThird{a}Part{q}"
    parts.append((lo,w,name))
    (d/(name+'.lean')).write_text(f"""import NineSeparatedSubsetSums.CachedFourPointShards
open NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem cachedThird{a}Part{q} : ∀ t : Fin {w}, cachedThirdShard {a} {B} (t.val+{lo}) = false := by decide +kernel
#print axioms cachedThird{a}Part{q}
""")
name=f"FourPoint{a}CachedShard"
s=f"""import NineSeparatedSubsetSums.FourPoint{a}Checked
"""+''.join('import NineSeparatedSubsetSums.'+p+'\n' for _,_,p in parts)+f"""
namespace NineSeparatedSubsetSums
theorem cachedFourPoint{a}_false : cachedSecondShard {a} {B} = false := by
  apply cachedSecondFalse_of_thirds
  intro t ht
  have hc : cachedThirdCount {a} {B} = {N} := by decide +kernel
  rw [hc] at ht
"""
for j,(lo,w,p) in enumerate(parts):
    last=j+1==len(parts)
    tab='  ' if last else '    '
    if not last: s+=f"  by_cases h{j} : t < {lo+w}\n  · "
    else:s+='  '
    s+=f"""let o : Fin {w} := ⟨t-{lo}, by omega⟩
{tab}have e : o.val+{lo}=t := by dsimp [o]; omega
{tab}rw [←e]
{tab}exact cachedThird{a}Part{j} o
"""
if not parts:s+="  omega\n"
s+=f"""
theorem fourPoint{a}_no_descending_tail : NoDescendingTail {a} :=
  noDescendingTail_of_cached {a} {B} max148_second{a}_fourPoint_moment_bound cachedFourPoint{a}_false
#print axioms fourPoint{a}_no_descending_tail
end NineSeparatedSubsetSums
"""
(d/(name+'.lean')).write_text(s)
print(*[p for _,_,p in parts],name)
