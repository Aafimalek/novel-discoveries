// Exact finite checks for the written proof, not a search over real weights.
const verify = (ok, msg) => { if (!ok) throw new Error(msg) }
const n = 9
const all = Array.from({length: 1 << n}, (_, i) => i)
const bitcount = x => x === 0 ? 0 : 1 + bitcount(x & (x - 1))
const lex = (x, y) => {
  if (x === y) return 0
  const firstDifference = (x ^ y) & -(x ^ y)
  return x & firstDifference ? -1 : 1
}
all.sort((x, y) => bitcount(x)-bitcount(y) || lex(x,y))
const prefix = new Set(all.slice(0, 158))
verify([...prefix].filter(x => bitcount(x) <= 3).length === 130, 'Initial lower layers')
verify([...prefix].filter(x => bitcount(x) === 4).length === 28, 'Partial layer')
const boundary = new Set()
for (const x of prefix) for (let i = 0; i < n; i++) {
  const y = x ^ (1 << i)
  if (!prefix.has(y)) boundary.add(y)
}
verify(boundary.size === 148, 'Harper initial-segment boundary')
verify([...boundary].filter(x => bitcount(x) === 4).length === 98, 'Four-element boundary')
verify([...boundary].filter(x => bitcount(x) === 5).length === 50, 'Five-element shadow')
verify(158 + 355 === 513 && 207 + 306 === 513 && 207 <= 306, 'Overlapping complementary rank intervals')
verify(355 - 158 - 148 > 2*n, 'Centering margin exceeds rounding error')
const example = [77n, 117n, 137n, 148n, 154n, 157n, 159n, 160n, 161n]
let sums = [0n]
for (const x of example) sums = sums.concat(sums.map(s => s + x))
verify(sums.length === 512 && new Set(sums).size === 512, 'Upper-bound witness')
console.log('Verified Harper boundary count (148), central margin, and all 512 sums of the upper-bound example.')
