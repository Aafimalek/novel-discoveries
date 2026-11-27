// Exact checks supporting the written proof; not a search over real weights.
const check = (condition, label) => {
  if (!condition) throw new Error(label)
}
function choose(n, k) {
  let value = 1n
  for (let i = 1n; i <= k; i++) value = value * (n - i + 1n) / i
  return value
}
let bandwidth = 0n
for (let j = 0n; j < 9n; j++) bandwidth += choose(j, j / 2n)
check(bandwidth === 148n, 'Bandwidth formula at n=9')
check(bandwidth + 1n > (1n << 8n) / 2n + 1n, 'Projected block exceeds half')
const prefix = [149n, 123n, 16n, 8n, 4n, 2n, 1n]
let total = 0n
let squares = 0n
for (let k = 1n; k <= 7n; k++) {
  const x = prefix[Number(k - 1n)]
  const a = 149n * k
  const b = 303n - ((1n << (7n - k)) - 1n)
  total += x
  squares += x * x
  check(total === (a < b ? a : b), 'Seven-term prefix bound')
}
const count = 1n << 9n
const moment = (count * count - 1n) / 3n
check(squares === 37671n, 'Seven-term square bound')
check(moment === 87381n, 'Necessary second moment')
check(squares + 2n * 149n ** 2n === 82073n && 82073n < moment, 'Moment contradiction')
check((1n << 8n) - 1n > 148n + 8n, 'Eight-term collision impossible')
const example = [77n, 117n, 137n, 148n, 154n, 157n, 159n, 160n, 161n]
let sums = [0n]
for (const x of example) sums = sums.concat(sums.map(s => s + x))
check(BigInt(sums.length) === count && BigInt(new Set(sums).size) === count, 'Upper-bound witness')
console.log('Verified constants and all 512 sums of the upper-bound example.')
