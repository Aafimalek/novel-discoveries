/*
 * Exact computation of G(n) = F(n) - n for Erdos problems #385 and #430, where
 * F(n) = max { m + p(m) : m < n, m composite } and p(m) is the least prime factor.
 *
 * n is an exception to #385(i) and #430 exactly when G(n) <= 0.
 *
 * Only m in [n - sqrt(n), n) can give m + p(m) - n >= 0, because p(m) <= sqrt(m)
 * for composite m. So each block [L, R) needs a least-prime-factor sieve on
 * [L - sqrt(R) - 2, R) and nothing else. Blocks are independent and run in parallel.
 *
 * Output (stdout, plain text):
 *   BAD n G            every n in [lo, hi) with G(n) <= 0 (value exact)
 *   LAST t n           largest n in [lo, hi) with 0 <= G(n) <= t, for t = 0..TMAX
 *   COUNT t c          number of n in [lo, hi) with G(n) == t, for t = 0..TMAX
 *   RANGE k minG nG minRatio nRatio
 *                      for n in [2^k, 2^(k+1)) within [lo, hi): minimum of G(n), and
 *                      minimum of G(n)/sqrt(n), each with an n attaining it
 *
 * Build: gcc -O3 -march=native -fopenmp -o f385 f385.c -lm
 * Usage: ./f385 lo hi [block]
 */
#include <inttypes.h>
#include <math.h>
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TMAX 4096
#define KMAX 64
#define BADMAX 100000

typedef struct {
    int64_t last_exact[TMAX + 1]; /* largest n with G(n) == t */
    int64_t count_exact[TMAX + 1]; /* number of n with G(n) == t */
    int64_t min_g[KMAX];
    int64_t min_g_n[KMAX];
    double min_ratio[KMAX];
    int64_t min_ratio_n[KMAX];
    int64_t bad_n[BADMAX];
    int64_t bad_g[BADMAX];
    int bad_count;
} Stats;

static uint64_t isqrt_u64(uint64_t x) {
    uint64_t r = (uint64_t)sqrtl((long double)x);
    while (r * r > x) r--;
    while ((r + 1) * (r + 1) <= x) r++;
    return r;
}

static void stats_init(Stats *s) {
    for (int t = 0; t <= TMAX; t++) {
        s->last_exact[t] = -1;
        s->count_exact[t] = 0;
    }
    for (int k = 0; k < KMAX; k++) {
        s->min_g[k] = INT64_MAX;
        s->min_g_n[k] = -1;
        s->min_ratio[k] = INFINITY;
        s->min_ratio_n[k] = -1;
    }
    s->bad_count = 0;
}

int main(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "usage: %s lo hi [block]\n", argv[0]);
        return 1;
    }
    int64_t lo = strtoll(argv[1], NULL, 10);
    int64_t hi = strtoll(argv[2], NULL, 10);
    int64_t block = argc > 3 ? strtoll(argv[3], NULL, 10) : (1LL << 24);
    if (lo < 4) lo = 4;

    /* Primes up to sqrt(hi). */
    uint64_t plim = isqrt_u64((uint64_t)hi) + 2;
    char *comp = calloc(plim + 1, 1);
    uint32_t *primes = malloc(sizeof(uint32_t) * (plim / 2 + 10));
    size_t np = 0;
    for (uint64_t i = 2; i <= plim; i++) {
        if (!comp[i]) {
            primes[np++] = (uint32_t)i;
            for (uint64_t j = i * i; j <= plim; j += i) comp[j] = 1;
        }
    }
    free(comp);

    int64_t nblocks = (hi - lo + block - 1) / block;
    int nthreads = omp_get_max_threads();
    Stats *all = malloc(sizeof(Stats) * nthreads);
    for (int i = 0; i < nthreads; i++) stats_init(&all[i]);

#pragma omp parallel
    {
        Stats *st = &all[omp_get_thread_num()];
        int64_t cap = block + (int64_t)isqrt_u64((uint64_t)hi) + 8;
        uint32_t *lpf = malloc(sizeof(uint32_t) * cap);

#pragma omp for schedule(dynamic, 1)
        for (int64_t b = 0; b < nblocks; b++) {
            int64_t L = lo + b * block;
            int64_t R = L + block < hi ? L + block : hi;
            int64_t W = (int64_t)isqrt_u64((uint64_t)R) + 2;
            int64_t S = L - W > 2 ? L - W : 2;
            int64_t len = R - S;
            memset(lpf, 0, sizeof(uint32_t) * len);
            uint64_t rlim = isqrt_u64((uint64_t)(R - 1));
            for (size_t i = 0; i < np && primes[i] <= rlim; i++) {
                int64_t p = primes[i];
                int64_t start = p * p;
                if (start < S) start = ((S + p - 1) / p) * p;
                for (int64_t m = start; m < R; m += p) {
                    uint32_t *slot = &lpf[m - S];
                    if (*slot == 0) *slot = (uint32_t)p;
                }
            }
            /* F(n) = max(F(n-1), (n-1) + p(n-1) if n-1 composite). */
            int64_t F = INT64_MIN / 4;
            for (int64_t n = S + 1; n < R; n++) {
                int64_t m = n - 1;
                uint32_t q = lpf[m - S];
                if (q != 0 && m + (int64_t)q > F) F = m + (int64_t)q;
                if (n < L) continue;
                int64_t g = F - n;
                if (g <= 0) {
                    /* Exact: a value of 0 can only come from m in the window. A
                       negative value may be inexact, but such n are rechecked. */
                    if (st->bad_count < BADMAX) {
                        st->bad_n[st->bad_count] = n;
                        st->bad_g[st->bad_count] = g;
                        st->bad_count++;
                    }
                }
                if (g >= 0 && g <= TMAX) {
                    if (n > st->last_exact[g]) st->last_exact[g] = n;
                    st->count_exact[g]++;
                }
                int k = 63 - __builtin_clzll((uint64_t)n);
                if (g < st->min_g[k]) {
                    st->min_g[k] = g;
                    st->min_g_n[k] = n;
                }
                double ratio = (double)g / sqrt((double)n);
                if (ratio < st->min_ratio[k]) {
                    st->min_ratio[k] = ratio;
                    st->min_ratio_n[k] = n;
                }
            }
        }
        free(lpf);
    }

    /* Merge. */
    Stats tot;
    stats_init(&tot);
    for (int i = 0; i < nthreads; i++) {
        Stats *s = &all[i];
        for (int t = 0; t <= TMAX; t++)
        {
            if (s->last_exact[t] > tot.last_exact[t]) tot.last_exact[t] = s->last_exact[t];
            tot.count_exact[t] += s->count_exact[t];
        }
        for (int k = 0; k < KMAX; k++) {
            if (s->min_g[k] < tot.min_g[k] ||
                (s->min_g[k] == tot.min_g[k] && s->min_g_n[k] > tot.min_g_n[k])) {
                tot.min_g[k] = s->min_g[k];
                tot.min_g_n[k] = s->min_g_n[k];
            }
            if (s->min_ratio[k] < tot.min_ratio[k]) {
                tot.min_ratio[k] = s->min_ratio[k];
                tot.min_ratio_n[k] = s->min_ratio_n[k];
            }
        }
        for (int j = 0; j < s->bad_count && tot.bad_count < BADMAX; j++) {
            tot.bad_n[tot.bad_count] = s->bad_n[j];
            tot.bad_g[tot.bad_count] = s->bad_g[j];
            tot.bad_count++;
        }
    }
    /* Sort bad list. */
    for (int i = 1; i < tot.bad_count; i++) {
        int64_t a = tot.bad_n[i], g = tot.bad_g[i];
        int j = i - 1;
        while (j >= 0 && tot.bad_n[j] > a) {
            tot.bad_n[j + 1] = tot.bad_n[j];
            tot.bad_g[j + 1] = tot.bad_g[j];
            j--;
        }
        tot.bad_n[j + 1] = a;
        tot.bad_g[j + 1] = g;
    }
    printf("RUN lo=%" PRId64 " hi=%" PRId64 " threads=%d primes=%zu\n", lo, hi, nthreads, np);
    printf("BADCOUNT %d\n", tot.bad_count);
    for (int i = 0; i < tot.bad_count; i++)
        printf("BAD %" PRId64 " %" PRId64 "\n", tot.bad_n[i], tot.bad_g[i]);
    int64_t best = -1;
    for (int t = 0; t <= TMAX; t++) {
        if (tot.last_exact[t] > best) best = tot.last_exact[t];
        printf("LAST %d %" PRId64 "\n", t, best);
    }
    for (int t = 0; t <= TMAX; t++)
        printf("COUNT %d %" PRId64 "\n", t, tot.count_exact[t]);
    for (int k = 0; k < KMAX; k++)
        if (tot.min_g_n[k] >= 0)
            printf("RANGE %d %" PRId64 " %" PRId64 " %.6f %" PRId64 "\n", k, tot.min_g[k],
                   tot.min_g_n[k], tot.min_ratio[k], tot.min_ratio_n[k]);
    return 0;
}
