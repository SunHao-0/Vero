// SPDX-License-Identifier: GPL-2.0
#include <linux/bitops.h>
#include <linux/tnum.h>

/*
 * tnum_step - smallest tnum member strictly above z
 *
 * Since every tnum member is tval | s for some submask s of tmask,
 * and tval | s = tval + s (disjoint), the problem reduces to:
 * find the smallest s, a submask of tmask, such that s > d,
 * where d = z - tval.
 *
 * We do this by "incrementing d within the mask": fill all non-mask
 * positions with 1 so that +1 ripples through the gaps, then mask
 * off the non-mask bits.  A carry_mask ensures the +1 also ripples
 * past any non-mask bits that are set in d.
 */
u64 tnum_step(struct tnum t, u64 z)
{
	u64 tmax, d, carry_mask, filled, inc;

	tmax = t.value | t.mask;

	if (z >= tmax)
		return tmax;

	if (z < t.value)
		return t.value;

	d = z - t.value;
	carry_mask = (1ULL << fls64(d & ~t.mask)) - 1;
	filled = d | carry_mask | ~t.mask;
	inc = (filled + 1) & t.mask;

	return t.value | inc;
}
