# LLVM KnownBits and DemandedBits Tasks

This document defines the abstract domain and specifications for the 27
`LLVM_*` tasks: 19 forward KnownBits transfer functions and 8 backward
DemandedBits transfer functions.

Two analyses are covered.

- KnownBits (forward): given abstract inputs, compute the optimal
  abstract output.
- DemandedBits (backward): given which output bits are used downstream,
  compute the minimal set of input bits that can affect them.

An operation is included when the current LLVM implementation is not
optimal, the optimal transfer function is non-trivial, and the operation
exists at the LLVM IR level. Operations whose LLVM analysis is already
exact, or that are not IR instructions, are excluded (section 5).

## 1. Domain and conventions

KnownBits represents a set of 64-bit values by two masks:

```lean
structure KnownBits where
  zero : BitVec 64   -- bits known to be 0
  one  : BitVec 64   -- bits known to be 1

def validKB (k : KnownBits) : Prop := (k.zero &&& k.one) = 0

def inKBGamma (k : KnownBits) (x : BitVec 64) : Prop :=
  (x &&& k.zero) = 0 ∧ (x &&& k.one) = k.one
```

All tasks use `BitVec 64`.

Flags as parameters. LLVM IR instructions carry boolean flags (nsw, nuw,
exact, IntMinIsPoison) that make an input producing an out-of-range
result into poison. Rather than one task per flag combination, each
transfer function takes the flags as boolean parameters, matching the
LLVM API (for example `KnownBits::udiv(LHS, RHS, Exact)`). A flag adds a
precondition on the concrete inputs in the soundness clause. Setting all
flags false recovers the base operation. Self-multiply `x * x` is a
separate task from `mul(x, y)` because the arity of the soundness
quantifier differs.

Poison and division by zero. The transfer function is specified over
non-poison executions only: the soundness clause quantifies over
concrete inputs that satisfy the flag preconditions. For udiv, sdiv,
urem, srem the divisor is required to be non-zero.

## 2. Forward specification

For inputs `a` (and `b`) the result `r` must be a valid KnownBits, sound,
and the least sound abstraction under concretization containment:

```
validKB r ∧
(∀ x y, inKBGamma a x → inKBGamma b y → [flag precond] → inKBGamma r (op x y)) ∧
(∀ r', validKB r' →
   (∀ x y, inKBGamma a x → inKBGamma b y → [flag precond] → inKBGamma r' (op x y)) →
   (∀ z, inKBGamma r z → inKBGamma r' z))
```

The least sound abstraction exists in the KnownBits domain: the tightest
KnownBits covering a set fixes exactly the bit positions that are
constant across the set. The unary and division and remainder tasks
adjust the operand list and preconditions accordingly.

## 3. Forward tasks (19)

Source file `llvm/lib/Support/KnownBits.cpp`, except mul flag handling,
which is in `llvm/lib/Analysis/ValueTracking.cpp`.

| Task | Operation | LLVM source | Reason the LLVM result is not optimal |
|------|-----------|-------------|----------------------------------------|
| `KBUdiv` | `x / y`, exact flag | 1200-1225 | Base sets only the leading zeros of the quotient. The exact flag adds some trailing bits. The modular relation between the low bits of `x`, `y`, and the quotient is unused. |
| `KBSdiv` | `x sdiv y`, exact flag | 1144-1198 | Sign-case analysis sets only leading sign bits. Low bits are ignored in every case. |
| `KBUrem` | `x % y` | 1240-1255 | Leading-zero bound is `max(lz x, lz y)`. The fact that the result is below `y`, and low-bit structure beyond a trailing-zero divisor, are unused. |
| `KBSrem` | `x srem y` | 1257-1284 | As `KBUrem`, with sign-dependent leading bits. |
| `KBUmax` | `umax(x, y)` | 309-325 | Uses `makeGE` on each operand then intersects. Bit positions determined jointly by the two operands are lost. |
| `KBUmin` | `umin(x, y)` | 327-331 | Defined as `umax` on flipped operands; inherits its loss. |
| `KBSmax` | `smax(x, y)` | 333-335 | Defined as `umax` after flipping the sign bit; inherits its loss. |
| `KBSmin` | `smin(x, y)` | 337-348 | As `KBSmax`. |
| `KBAbs` | `abs(x)`, IntMinIsPoison flag | 695-751 | For unknown input sign, only trailing zeros and the sign bit are set; the two branches (identity and negation) are not combined. |
| `KBAbdu` | `\|x - y\|` unsigned | 350-367 | Intersects two nuw subtractions. The leading zeros implied by operand range proximity and the common trailing bits are lost. |
| `KBAbds` | `\|x - y\|` signed inputs | 369-398 | Sign-flips to unsigned then intersects like `KBAbdu`. |
| `KBMul` | `x * y`, nsw and nuw flags | 989-1090 (+ ValueTracking) | `KnownBits::mul` ignores the flags. ValueTracking sets only the sign bit under nsw. nuw bounds the active bits exactly, which is unused. |
| `KBMulSelf` | `x * x`, nsw flag | 989-1090 | Adds only two bits over the general product. Quadratic structure (for example `x*x mod 4 ∈ {0,1}`) is unused. |
| `KBUaddSat` | `min(x + y, 2^64-1)` | 793-948 | When overflow is uncertain, all known zeros of the sum are cleared. |
| `KBUsubSat` | `max(x - y, 0)` | 793-948 | When overflow is uncertain, all known ones of the difference are cleared. |
| `KBSaddSat` | clamp `x + y` to signed range | 793-948 | When the overflow direction is uncertain, only sign bits are kept. |
| `KBSsubSat` | clamp `x - y` to signed range | 793-948 | As `KBSaddSat`. |
| `KBMulhu` | high 64 bits of `x * y` unsigned | 1100-1106 | Delegates to a 128-bit `mul` and inherits its conservatism on the upper half. |
| `KBMulhs` | high 64 bits of `x * y` signed | 1092-1098 | As `KBMulhu`, with sign extension. |

## 4. Backward specification

DemandedBits is the dual analysis. Given `demanded`, the mask of output
bits used downstream, the transfer function returns the mask of input
bits that can affect a demanded output bit.

Bit `i` of input `a` is demanded when there exist `x1, x2 ∈ γ(a)`
differing only at bit `i`, and `y ∈ γ(b)`, such that `op(x1, y)` and
`op(x2, y)` differ at some position where `demanded` is set (both inputs
satisfying any flag preconditions). A demanded bit is necessarily an
unknown bit of the input.

The result `(dA, dB)` must satisfy three clauses:

```
-- (1) demanded bits are among the unknown bits
(dA &&& (a.zero ||| a.one)) = 0 ∧ (dB &&& (b.zero ||| b.one)) = 0

-- (2) soundness: flipping an undemanded input bit does not change any
--     demanded output bit, for inputs and flips satisfying the flags
∀ i, dA.getLsbD i = false → ∀ x y, ... → op(x,y) &&& demanded = op(flip x i, y) &&& demanded
(and symmetrically for dB)

-- (3) optimality: every demanded input bit has a witnessing flip that
--     changes a demanded output bit
∀ i, dA.getLsbD i = true → ∃ x1 x2 y, ... ∧ x1 ^^^ x2 = (1 <<< i) ∧
     op(x1,y) &&& demanded ≠ op(x2,y) &&& demanded
(and symmetrically for dB)
```

A tighter analysis returns fewer demanded bits.

## 5. Backward tasks (8)

Source file `llvm/lib/Transforms/InstCombine/InstCombineSimplifyDemanded.cpp`
(`SimplifyDemandedUseBits`).

| Task | Operation | LLVM source | Reason the LLVM result is not optimal |
|------|-----------|-------------|----------------------------------------|
| `DBAdd` | `x + y`, nsw and nuw flags | 565-650 | Reduces demand only for a contiguous run of high unused bits and low bits above a known-zero divisor tail. Interior positions where the carry is known are not reduced. Flags are not used. |
| `DBSub` | `x - y`, nsw and nuw flags | 651-693 | As `DBAdd`. The RHS demand is not reduced from LHS known bits (asymmetric). Flags are not used. |
| `DBMul` | `x * y`, nsw and nuw flags | 694-722 | Handles only the high-unused-bits case and two constant-multiplier special cases. The general fact that demanding low bits `[0,k)` demands only input bits `[0,k)` is not used, nor are the flags. |
| `DBUdiv` | `x / y`, exact flag | 942-963 | Ignores the output demand mask entirely (explicit TODO in LLVM). The exact flag is unused. A non-constant divisor is not handled. |
| `DBSrem` | `x srem y` | 964-980 | Handles only a power-of-two constant divisor. General divisors are not handled. |
| `DBSdiv` | `x sdiv y`, exact flag | default | No backward analysis in LLVM. |
| `DBUrem` | `x % y` | default | No backward analysis in LLVM, including the power-of-two case. |
| `DBAbs` | `abs(x)`, IntMinIsPoison flag | abs intrinsic | Handles only the case where a single low bit is demanded. |

## 6. Excluded operations

- Already exact in LLVM, no approximation to improve: forward and
  backward AND, OR, XOR, select, constant shifts, zext, sext, trunc,
  `computeForAddCarry`, `computeForSubBorrow`, the averaging operations,
  and structural operations (byteswap, bit reverse, insert and extract
  bits).
- Not IR-level instructions: abdu and abds backward exist only at the
  SelectionDAG level, so InstCombine never runs a backward analysis for
  them.
- Backward analysis not useful: for umax, umin, smax, smin, and the
  saturating operations, almost all input bits are demanded whenever any
  output bit is demanded, so a backward transfer function offers no
  reduction over modeling the underlying add or subtract.

## 7. Naming and templates

Forward tasks are named `KB<Op>`, backward tasks `DB<Op>`. Templates in
`template/`:

| Template | Shape | Tasks |
|----------|-------|-------|
| `KBBinOp.lean` | forward binary, no flags | KBUmax, KBUmin, KBSmax, KBSmin, KBAbdu, KBAbds, KBUaddSat, KBUsubSat, KBSaddSat, KBSsubSat, KBMulhu, KBMulhs |
| `KBBinOpDiv.lean` | forward binary, `y ≠ 0` | KBUrem, KBSrem |
| `KBBinOpDivExact.lean` | forward binary, exact flag, `y ≠ 0` | KBUdiv, KBSdiv |
| `KBBinOpMulFlags.lean` | forward binary, nsw and nuw flags | KBMul |
| `KBUnaryOpFlag.lean` | forward unary, one flag | KBAbs, KBMulSelf |
| `DBBinOpFlags.lean` | backward binary, nsw and nuw flags | DBAdd, DBSub, DBMul |
| `DBBinOpExact.lean` | backward binary, exact flag, `y ≠ 0` | DBUdiv, DBSdiv |
| `DBBinOp.lean` | backward binary, `y ≠ 0`, no flags | DBSrem, DBUrem |
| `DBUnaryOpFlags.lean` | backward unary, one flag | DBAbs |
