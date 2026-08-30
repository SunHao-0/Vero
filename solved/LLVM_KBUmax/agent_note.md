# Agent Notes: Unsigned Maximum (kbUmax)

## Implementation Strategy

The implementation uses a three-case structure based on KnownBits range analysis:

1. **maxB <= minA**: Result is always `a` (every concrete value in `a` is >= every concrete value in `b`).
2. **maxA < minB**: Result is always `b` (symmetric case).
3. **Overlap**: The result's known-zero bits are `a.zero &&& b.zero` (intersection). The known-one bits use a "smear" technique: cascading OR-shifts to compute a bitmask covering the range of possible differences, then intersecting with the minimum values' known bits.

The smear operation (`v ||| v>>>1`, `v ||| v>>>2`, ..., `v ||| v>>>32`) fills all bits below the MSB of its input, producing a mask of bits that could vary in the result.

## Proof Strategy

- **Well-formedness**: Cases 1 and 2 inherit from inputs. Case 3 uses `split <;> bv_decide`.
- **Soundness**: Uses `bv_decide` with `.toNat` comparisons converted to BitVec comparisons via `BitVec.le_def.mpr`/`BitVec.lt_def.mpr`.
- **Optimality**: Constructs specific witnesses to force `r'` to accept all values that `r` accepts:
  - Corner witnesses `(~~~a.zero, b.one)` and `(a.one, ~~~b.zero)` establish zero-bit constraints.
  - Witness `(a.one, b.one)` establishes basic one-bit constraints.
  - Specially constructed witnesses `y_all`/`x_all` (using the smear mask to selectively disable unknown bits) establish the tighter one-bit constraints in the overlap case.

## Key Technical Decisions

- Used `bv_decide` as the primary workhorse (bit-blasting + SAT) rather than `omega`/`simp`/`grind`.
- All `.toNat` comparisons from if-conditions must be converted to BitVec-level comparisons before `bv_decide` can use them.
- The `set` + `subst_eqs` pattern lets `bv_decide` see through the smear computation chain.
- All axioms are standard Lean axioms (propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound).
