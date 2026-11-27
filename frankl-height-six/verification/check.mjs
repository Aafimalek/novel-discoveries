// Exact arithmetic checks for the small-ground-set cases in the written proof.
const expect = (b, label) => { if (!b) throw new Error(label) }
const falling4 = (u, v) => u * (u - v) * (u - 2n*v) * (u - 3n*v)
const p = (n, u, v) => falling4(u, v) - 6n*(n - 3n)*(2n*u - n*v)*v**3n
const derivativeAt4 = n => 50n - 12n*(n - 3n)
expect(p(5n, 9n, 2n) === 177n, 'P5(9/2)')
expect(p(6n, 31n, 7n) === 3000n, 'P6(31/7)')
expect(p(7n, 4n, 1n) === 0n, 'P7(4)')
expect(derivativeAt4(5n) === 26n && derivativeAt4(6n) === 14n && derivativeAt4(7n) === 2n, 'Small-n derivatives')
expect(p(8n, 4n, 1n) === 24n && derivativeAt4(8n) === -10n, 'P8(4) and its derivative')
expect(100n - 4n*35n*24n < 0n, 'Negative quadratic discriminant')
console.log('Height-six note: exact small-case arithmetic checks passed.')
