# Cnum + Tnum Task Family

This document defines the cnum + tnum abstract domain used by the
`eBPF_Cnum_*` tasks and states their specification. These are the 64-bit
operations of the eBPF verifier under the cnum rewrite. The 32-bit
operations use the interval + tnum domain; see `docs/interval.md`.

Kernel sources (bpf-next):

- `include/linux/cnum.h`, `kernel/bpf/cnum_defs.h`, `kernel/bpf/cnum.c`
- `include/linux/bpf_verifier.h`: register state `var_off` (tnum), `r64`
  (cnum64), `r32` (cnum32)
- `kernel/bpf/verifier.c`: `reg_bounds_sync`, `scalar*_min_max_*`,
  `is_scalar_branch_taken`, `regs_refine_cond_op`, `coerce_reg_to_size`

## 1. The cnum domain

A cnum is a contiguous arc on the circle of `2^w` values. With base and
size in `uw`, the cnum `{base, size}` denotes

```
γ(c) = { base + k (mod 2^w) | 0 ≤ k ≤ size },
```

the `size + 1` values starting at `base` going clockwise, wrapping past
`2^w - 1` back to `0`. The size excludes the base, so the full circle
uses `size = 2^w - 1`.

Two encodings are reserved:

- Empty: `{2^w - 1, 2^w - 1}` denotes the empty set. This costs one arc
  (the full circle starting at `2^w - 1`), which is not lost, since the
  full circle is representable from any other base. The kernel
  canonicalizes the full circle to base `0`.
- Full circle: `{0, 2^w - 1}`.

Membership reduces to a single wrapping comparison:

```
v ∈ γ(c)  iff  c ≠ empty ∧ (v - base) ≤ size    (subtraction mod 2^w)
```

The kernel `cnumT_contains` is a two-case unsigned range check. It is
equivalent to the wrapping form above. We verified the equivalence over
all `2^32` edge combinations plus 50 million random cases (a C harness
transcribing `cnum_defs.h`) and by kernel-checked `decide` proofs on the
Lean definition.

A single arc keeps whichever of the unsigned and signed views is not cut
by its wrap point. The kernel derives `umin/umax` unless the arc crosses
the `2^w - 1` to `0` boundary, and `smin/smax` unless it crosses the
`S_MAX` to `S_MIN` boundary. This is the reason for the domain change:
one arc replaces the four separate ranges of the interval domain.

## 2. Lean formalization

```lean
structure Cnum64 where
  base : BitVec 64
  size : BitVec 64

def cnum64IsEmpty (c : Cnum64) : Prop :=
  c.base = BitVec.allOnes 64 ∧ c.size = BitVec.allOnes 64

def inCnum64Gamma (c : Cnum64) (x : BitVec 64) : Prop :=
  ¬ cnum64IsEmpty c ∧ x - c.base ≤ c.size
```

`Cnum32` is analogous over `BitVec 32`. The register state carries a
tnum, a 64-bit cnum, and a 32-bit cnum over the low 32 bits:

```lean
structure RegState where
  var_off : Tnum
  r64     : Cnum64
  r32     : Cnum32

def inGamma (reg : RegState) (x : BitVec 64) : Prop :=
  satisfiesTnum64 x reg.var_off.value reg.var_off.mask ∧
  inCnum64Gamma reg.r64 x ∧
  inCnum32Gamma reg.r32 (x.truncate 32)
```

Validity is tnum consistency alone:

```lean
def validReg (reg : RegState) : Prop :=
  (reg.var_off.value &&& reg.var_off.mask) = 0
```

The 64-bit tasks carry all three components because the kernel state
does and the transfer functions read and produce all three.
`reg_bounds_sync` exists precisely because the components interact, and
`is_scalar_branch_taken` uses the 32-bit view for 64-bit equality tests.
No validity condition on `r64` or `r32` is needed: every cnum encoding
denotes a set, either an arc or the empty set. The interval domain
needed ordering and coupling conditions to exclude states that denote
nothing; the cnum domain does not.

## 3. Optimality

The interval domain states optimality as the best abstract transformer:
the result `r` is sound and `γ(r) ⊆ γ(r')` for every sound valid `r'`.
That form requires a least sound abstraction to exist. In the cnum
domain no least sound abstraction exists in general, so the form is
unsatisfiable.

The reason is that a set need not have a least arc cover. Consider the
set `S = {0, 2^63}`, the two values on opposite sides of the 64-bit
circle. This set is realizable: a register whose tnum leaves only bit 63
free has concretization exactly `S`. Two arcs of equal size cover `S`:

- Arc `A`: from `0` clockwise to `2^63`, covering `0, 1, ..., 2^63`.
- Arc `B`: from `2^63` clockwise through `2^64 - 1` back to `0`, covering
  `2^63, ..., 2^64 - 1, 0`.

Both are sound. Neither is contained in the other: `A` contains `1`,
which `B` excludes; `B` contains `2^63 + 1`, which `A` excludes. The
best-transformer form requires a result contained in every sound state,
hence contained in both `A` and `B`, hence in `A ∩ B = {0, 2^63}`.
Soundness requires the result to contain `S = {0, 2^63}`. So the result
would concretize to exactly `{0, 2^63}`, which is not an arc and is not
representable by a cnum. No such result exists. The product with the
tnum and the 32-bit cnum does not restore a least element; the same two
arcs are incomparable in the product.

The tasks therefore state optimality per component. Against every sound
valid `r'`:

```
r.r64.size ≤ r'.r64.size ∧                    -- minimum-size 64-bit arc
r.r32.size ≤ r'.r32.size ∧                    -- minimum-size 32-bit arc
(r.var_off.mask &&& ~~~r'.var_off.mask) = 0   -- minimal tnum mask
```

This condition is well posed. Among the finitely many arcs covering a
set, one has minimum size, so `r.r64` and `r.r32` are required to be
minimum-size arc covers of `S` and of its low 32-bit projection, and
`r.var_off` the least tnum cover. Ties (several minimum-size arcs, as in
the example) are all accepted, matching the kernel, which picks one
representative. Minimum size is stronger than local minimality: an arc
whose two endpoints both touch `S` cannot be shrunk in place, yet a
differently placed arc may be smaller, and the condition rejects the
former.

`Cnum_BoundsSync` uses the same per-component condition. Its interval
predecessor already did, for the same reason.

## 4. Task families

| Family | Count | Operation |
|--------|-------|-----------|
| `Cnum_Alu64{Add,Sub,And,Or,Xor,Lsh,Rsh,Arsh}` | 8 | 64-bit ALU transfer function |
| `Cnum_Jmp64{Eq,Lt,Le,Slt,Sle,Jset}` | 6 | branch outcome for a 64-bit comparison |
| `Cnum_RefineJmp64{Ne,Lt,Le,Slt,Sle,Jset,Xjset}` | 7 | refine two states on the taken branch |
| `Cnum_Cast{Zext,Sext}` | 2 | zero and sign extension (`coerce_reg_to_size`) |
| `Cnum_BoundsSync` | 1 | reduced form: synchronize tnum, cnum64, cnum32 |

ALU, cast, and sync tasks state the best abstract transformer with the
per-component optimality of section 3. Branch tasks state correctness as
an equivalence between the returned `always` / `never` / `unknown` and
the always/never predicates. Refinement tasks state soundness and
per-component optimality for each of the two refined states, under a
feasibility precondition, so the optimal result of an infeasible branch
is never required.

Shift tasks carry `hshift : ∀ s, inGamma src s → s.toNat < 64`. Cast
tasks carry `hsize : size = 1 ∨ size = 2 ∨ size = 4`. Branch and
refinement tasks provide the axiomatized tnum helpers `tnumStepUp` and
`tnumStepDown` with their specifications.

## 5. Candidate future tasks

The cnum API contains operations whose optimal forms would make
standalone tasks:

- `Cnum_Intersect`: least single-arc cover of `γ(a) ∩ γ(b)`. The kernel
  over-approximates the two-sub-arc case by returning the smaller
  operand.
- `Cnum_SyncFrom32`: the standalone `cnum64_cnum32_intersect` refinement,
  subsumed by `Cnum_BoundsSync`.
- Refinement without the feasibility precondition, where the optimal
  result of an infeasible branch is the empty encoding.
