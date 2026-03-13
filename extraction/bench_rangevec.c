/*
 * bench_rangevec.c — Benchmark for extracted Pulse RangeVec (vector-based range tracker)
 *
 * Compile:
 *   gcc -O2 -I ~/karamel/include -I ~/karamel/krmllib/dist/minimal \
 *       bench_rangevec.c _c_output/Pulse_Lib_RangeVec.c -o bench_rangevec
 *
 * Run:
 *   ./bench_rangevec [iterations]
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#include "_c_output/Pulse_Lib_RangeVec.h"

/* ─── Timing ─────────────────────────────────────────────────── */

static inline uint64_t now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

/* ─── PRNG (xorshift64) ─────────────────────────────────────── */

static uint64_t rng_state = 0x123456789ABCDEF0ULL;
static inline uint64_t xorshift64(void) {
    uint64_t x = rng_state;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    return (rng_state = x);
}

static void shuffle(uint32_t* arr, uint32_t n) {
    for (uint32_t i = n - 1; i > 0; i--) {
        uint32_t j = (uint32_t)(xorshift64() % (i + 1));
        uint32_t tmp = arr[i]; arr[i] = arr[j]; arr[j] = tmp;
    }
}

/* ─── Scenarios ──────────────────────────────────────────────── */

static void bench_sequential_add(uint32_t iters, uint32_t n_ranges, uint32_t chunk) {
    uint64_t t0 = now_ns();
    for (uint32_t it = 0; it < iters; it++) {
        Pulse_Lib_RangeVec_range_vec_t rv = Pulse_Lib_RangeVec_range_vec_create();
        for (uint32_t i = 0; i < n_ranges; i++) {
            Pulse_Lib_RangeVec_range_vec_add(rv, (size_t)i * chunk, (size_t)chunk);
        }
        size_t cf = Pulse_Lib_RangeVec_range_vec_contiguous_from(rv, 0);
        (void)cf;
        Pulse_Lib_RangeVec_range_vec_free(rv);
    }
    uint64_t t1 = now_ns();
    double ms = (double)(t1 - t0) / 1e6;
    uint64_t total_ops = (uint64_t)iters * n_ranges;
    double ops_s = (double)total_ops / ((double)(t1 - t0) / 1e9);
    printf("  Sequential add (%u ranges x %uB):  %8.2f ms  %10.0f add/s\n",
           n_ranges, chunk, ms, ops_s);
}

static void bench_ooo_add(uint32_t iters, uint32_t n_ranges, uint32_t chunk) {
    uint32_t* order = malloc(n_ranges * sizeof(uint32_t));
    for (uint32_t i = 0; i < n_ranges; i++) order[i] = i;

    uint64_t t0 = now_ns();
    for (uint32_t it = 0; it < iters; it++) {
        shuffle(order, n_ranges);
        Pulse_Lib_RangeVec_range_vec_t rv = Pulse_Lib_RangeVec_range_vec_create();
        for (uint32_t i = 0; i < n_ranges; i++) {
            Pulse_Lib_RangeVec_range_vec_add(rv, (size_t)order[i] * chunk, (size_t)chunk);
        }
        size_t cf = Pulse_Lib_RangeVec_range_vec_contiguous_from(rv, 0);
        (void)cf;
        Pulse_Lib_RangeVec_range_vec_free(rv);
    }
    uint64_t t1 = now_ns();
    double ms = (double)(t1 - t0) / 1e6;
    uint64_t total_ops = (uint64_t)iters * n_ranges;
    double ops_s = (double)total_ops / ((double)(t1 - t0) / 1e9);
    printf("  OOO add (%u ranges x %uB):         %8.2f ms  %10.0f add/s\n",
           n_ranges, chunk, ms, ops_s);
    free(order);
}

static void bench_gap_stress(uint32_t iters, uint32_t n_ranges, uint32_t chunk) {
    uint64_t t0 = now_ns();
    for (uint32_t it = 0; it < iters; it++) {
        Pulse_Lib_RangeVec_range_vec_t rv = Pulse_Lib_RangeVec_range_vec_create();
        /* Add every other range (max gaps) */
        for (uint32_t i = 0; i < n_ranges; i += 2) {
            Pulse_Lib_RangeVec_range_vec_add(rv, (size_t)i * chunk, (size_t)chunk);
        }
        /* Fill gaps */
        for (uint32_t i = 1; i < n_ranges; i += 2) {
            Pulse_Lib_RangeVec_range_vec_add(rv, (size_t)i * chunk, (size_t)chunk);
        }
        size_t cf = Pulse_Lib_RangeVec_range_vec_contiguous_from(rv, 0);
        (void)cf;
        Pulse_Lib_RangeVec_range_vec_free(rv);
    }
    uint64_t t1 = now_ns();
    double ms = (double)(t1 - t0) / 1e6;
    uint64_t total_ops = (uint64_t)iters * n_ranges;
    double ops_s = (double)total_ops / ((double)(t1 - t0) / 1e9);
    printf("  Gap-fill add (%u ranges x %uB):    %8.2f ms  %10.0f add/s\n",
           n_ranges, chunk, ms, ops_s);
}

static void bench_queries(uint32_t iters, uint32_t n_ranges, uint32_t chunk) {
    /* Build once, then query many times */
    Pulse_Lib_RangeVec_range_vec_t rv = Pulse_Lib_RangeVec_range_vec_create();
    for (uint32_t i = 0; i < n_ranges; i++) {
        Pulse_Lib_RangeVec_range_vec_add(rv, (size_t)i * chunk, (size_t)chunk);
    }

    uint64_t t0 = now_ns();
    for (uint32_t it = 0; it < iters; it++) {
        size_t cf = Pulse_Lib_RangeVec_range_vec_contiguous_from(rv, 0);
        size_t me = Pulse_Lib_RangeVec_range_vec_max_endpoint(rv);
        (void)cf; (void)me;
    }
    uint64_t t1 = now_ns();
    double ms = (double)(t1 - t0) / 1e6;
    double ops_s = (double)iters * 2 / ((double)(t1 - t0) / 1e9);
    printf("  Queries (cf+maxep, %u ranges):     %8.2f ms  %10.0f query/s\n",
           n_ranges, ms, ops_s);
    Pulse_Lib_RangeVec_range_vec_free(rv);
}

/* ─── Main ───────────────────────────────────────────────────── */

int main(int argc, char* argv[]) {
    uint32_t iters = 1000;
    if (argc > 1) {
        iters = (uint32_t)atoi(argv[1]);
        if (iters == 0) iters = 1000;
    }

    printf("═══════════════════════════════════════════════════════════\n");
    printf("  RangeVec (Vector-based) Benchmark\n");
    printf("  Iterations: %u\n", iters);
    printf("═══════════════════════════════════════════════════════════\n\n");

    bench_sequential_add(iters, 256, 16);
    bench_sequential_add(iters, 64, 256);
    bench_ooo_add(iters, 256, 16);
    bench_ooo_add(iters, 64, 256);
    bench_gap_stress(iters, 256, 16);
    bench_gap_stress(iters, 64, 256);
    bench_queries(iters * 100, 256, 16);
    bench_queries(iters * 100, 64, 256);

    printf("\n═══════════════════════════════════════════════════════════\n");
    return 0;
}
