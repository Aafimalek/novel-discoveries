// Exhaustive small check of the conditional monotonicity lemma.
// Every finite poset can be relabelled so that its strict order is forward.
const n = 5
const pairs = []
for (let i = 0; i < n; i++) for (let j = i+1; j < n; j++) pairs.push([i,j])
let posets = 0
let instances = 0
for (let mask = 0; mask < 2**pairs.length; mask++) {
  const lt = Array.from({length:n}, () => Array(n).fill(false))
  pairs.forEach(([i,j], k) => { lt[i][j] = Boolean(mask & (1 << k)) })
  if (pairs.some(([i,k]) => lt[i].some((ij,j) => ij && lt[j][k] && !lt[i][k]))) continue
  posets++
  const exts = []
  function extend(path) {
    if (path.length === n) { exts.push(path); return }
    for (let x = 0; x < n; x++) {
      if (!path.includes(x) && lt.every((row,y) => !row[x] || path.includes(y))) extend([...path,x])
    }
  }
  extend([])
  for (let a = 0; a < n; a++) for (let b = 0; b < n; b++) {
    if (a === b || lt[a][b] || lt[b][a] || lt.some(row => row[a] && !row[b])) continue
    instances++
    const S = new Set([b, ...lt[b].flatMap((yes,z) => yes && !lt[a][z] ? [z] : [])])
    const counts = new Map()
    for (const L of exts) {
      const key = L.filter(x => S.has(x)).join(',')
      const i = L.slice(0, L.indexOf(a)).filter(x => S.has(x)).length
      if (!counts.has(key)) counts.set(key, Array(S.size+1).fill(0))
      counts.get(key)[i]++
    }
    for (const bins of counts.values()) {
      if (bins.some((count,i) => i > 0 && count > bins[i-1])) throw new Error('Nonmonotone bins')
    }
  }
}
if (posets !== 357 || instances === 0) throw new Error('Unexpected enumeration size')
console.log('Conditional monotonicity checked for ' + instances + ' eligible ordered pairs across ' + posets + ' naturally labelled posets on five elements.')
