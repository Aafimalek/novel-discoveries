import sys, json
from pathlib import Path
a=int(sys.argv[1]); B=min(d['bound'] for d in json.loads(Path('fourpoint-data.json').read_text()) if d['a']==a)
p=Path('NineSeparatedSubsetSums')
p.joinpath(f'FourPoint{a}CachedShard.lean').write_text(f"""import NineSeparatedSubsetSums.FourPoint{a}Checked
import NineSeparatedSubsetSums.CachedFourPointShards

namespace NineSeparatedSubsetSums
set_option maxRecDepth 32768 in
set_option maxHeartbeats 70000000 in
theorem cachedFourPoint{a}_false : cachedSecondShard {a} {B} = false := by decide +kernel

theorem fourPoint{a}_no_descending_tail : NoDescendingTail {a} :=
  noDescendingTail_of_cached {a} {B} max148_second{a}_fourPoint_moment_bound cachedFourPoint{a}_false

#print axioms cachedFourPoint{a}_false
#print axioms fourPoint{a}_no_descending_tail
end NineSeparatedSubsetSums
""")
print(f'FourPoint{a}CachedShard')
