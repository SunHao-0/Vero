#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>
#include <assert.h>

typedef uint64_t u64;

static inline int fls64(u64 x)
{
	if (x == 0)
		return 0;
	return 64 - __builtin_clzll(x);
}

u64 tnum_step_up(u64 tval, u64 tmask, u64 z)
{
	u64 d = z - tval;
	u64 carry_mask = (1ULL << fls64(d & ~tmask)) - 1;
	u64 inc = ((d | carry_mask | ~tmask) + 1) & tmask;

	return tval | inc;
}

static u64 rand64(void)
{
	return ((u64)rand() << 32) ^ ((u64)rand() << 16) ^ (u64)rand();
}

/* Original Lean4 algorithm (proved correct by bv_decide) */
static u64 lean4_step_up(u64 tval, u64 tmask, u64 z)
{
	u64 d = z - tval;
	u64 nonmask_d = d & ~tmask;
	u64 mask_d0 = tmask & ~d;
	u64 nm = nonmask_d;

	nm |= nm >> 1;  nm |= nm >> 2;  nm |= nm >> 4;
	nm |= nm >> 8;  nm |= nm >> 16; nm |= nm >> 32;

	u64 above = ~nm;
	u64 valid = mask_d0 & above;
	u64 lowest = valid & (0ULL - valid);
	u64 high_mask = ~(lowest | (lowest - 1));
	u64 result_high = d & tmask & high_mask;

	return tval | (result_high | lowest);
}

/* Brute-force: scan z+1 upward (only usable for small popcount) */
static u64 brute_step_up(u64 tval, u64 tmask, u64 z)
{
	for (u64 v = z + 1; v <= (tval | tmask); v++)
		if ((v & ~tmask) == tval)
			return v;
	return 0;
}

static int check(u64 tval, u64 tmask, u64 z)
{
	u64 r = tnum_step_up(tval, tmask, z);

	/* P1: satisfies tnum */
	if ((r & ~tmask) != tval) {
		fprintf(stderr, "FAIL sat: tval=%lx tmask=%lx z=%lx r=%lx\n",
			tval, tmask, z, r);
		return 1;
	}

	/* P2: in range */
	if (r < tval || r > (tval | tmask)) {
		fprintf(stderr, "FAIL range: tval=%lx tmask=%lx z=%lx r=%lx\n",
			tval, tmask, z, r);
		return 1;
	}

	/* P3: strictly above z */
	if (r <= z) {
		fprintf(stderr, "FAIL gt: tval=%lx tmask=%lx z=%lx r=%lx\n",
			tval, tmask, z, r);
		return 1;
	}

	/* P4: matches Lean4 original (proved correct by bv_decide) */
	u64 lean = lean4_step_up(tval, tmask, z);
	if (r != lean) {
		fprintf(stderr, "FAIL lean4: tval=%lx tmask=%lx z=%lx r=%lx lean=%lx\n",
			tval, tmask, z, r, lean);
		return 1;
	}

	/* P5: matches brute-force (small values only — expensive) */
	if ((tval | tmask) <= 0xFFFFFF) {
		u64 brute = brute_step_up(tval, tmask, z);
		if (r != brute) {
			fprintf(stderr, "FAIL brute: tval=%lx tmask=%lx z=%lx r=%lx brute=%lx\n",
				tval, tmask, z, r, brute);
			return 1;
		}
	}

	return 0;
}

/* Generate a random z in [tval, tval|tmask) */
static u64 rand_z(u64 tval, u64 tmask)
{
	u64 range = tmask; /* tval|tmask - tval = tmask (disjoint) */
	u64 d = rand64() % range; /* d in [0, tmask) */
	return tval + d;
}

int main(int argc, char **argv)
{
	int seconds = argc > 1 ? atoi(argv[1]) : 10;
	time_t deadline = time(NULL) + seconds;
	u64 iters = 0, fails = 0;

	srand(42);

	while (time(NULL) < deadline) {
		u64 tmask, tval, z;

		switch (iters % 3) {
		case 0: /* Small values: brute-force optimality check feasible */
			tmask = rand64() & 0xFFFF;
			tval = (rand64() & ~tmask) & 0xFF0000;
			break;
		case 1: /* Medium: sparse 64-bit mask */
			tmask = rand64() & rand64() & rand64();
			tval = rand64() & ~tmask;
			break;
		default: /* Full random 64-bit */
			tmask = rand64();
			tval = rand64() & ~tmask;
			break;
		}
		if (tmask == 0)
			continue;

		z = rand_z(tval, tmask);
		fails += check(tval, tmask, z);
		iters++;
		if (iters % 819200 == 0)
			printf("Iter %ld...\n", iters);
	}

	printf("%lu iters in %ds, %lu failures\n", iters, seconds, fails);
	return fails ? 1 : 0;
}
