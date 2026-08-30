# Agent Notes: tnumStepUp

## Algorithm

The algorithm finds the smallest value `w > z` satisfying a tnum constraint `(tval, tmask)` in O(1) bit operations.

### Key Insight

Any valid `w` has the form `tval ||| m` where `m` is a submask of `tmask`. We need the smallest submask `m` of `tmask` such that `tval + m > z`, i.e., `m > d` where `d = z - tval`.

### Finding the Smallest Submask > d

The core challenge is finding the smallest submask of `tmask` that exceeds `d` numerically. The naive "increment mask-sub-number" trick `((d ||| ~~~tmask) + 1) &&& tmask` fails because it only considers mask-bit positions in isolation, ignoring the numerical contribution of non-mask bits in `d`.

The correct approach identifies a "branching point" — the lowest mask bit position `k` where we can set `m[k] = 1` (while `d[k] = 0`) and guarantee `m > d`:

1. **Constraint**: All non-mask bits of `d` above position `k` must be 0 (otherwise `d` would exceed `m` at those positions since `m` has 0 at non-mask positions).
2. **Implementation**: Compute `top_nm` = MSB position of `d &&& ~~~tmask` using parallel prefix OR (smearing). Then find the lowest mask bit above `top_nm` where `d` has a 0.
3. **Result construction**: Set `m = (d's mask bits above k) ||| (1 << k)`, clear all mask bits below `k`.

### Complexity

- 6 shifts + 6 ORs for parallel prefix smearing
- ~10 additional bitwise operations (AND, OR, NOT, subtract)
- Total: O(1) with ~22 fixed bit operations, no loops

### Proof

All 5 proof obligations (lower bound, upper bound, tnum satisfaction, strict improvement, optimality) are discharged by `bv_decide`, a SAT-based decision procedure for bitvector arithmetic.
