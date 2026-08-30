# Interval + Tnum Task Family

This document defines the interval + tnum abstract domain used by the
`eBPF_Interval_*` tasks and states their specification. These are the
32-bit operations of the eBPF verifier. The 64-bit operations use the
cnum domain instead; see `docs/cnum.md`.

Kernel background: this is the register representation the verifier used
before the cnum rewrite. A register tracked four numeric ranges
(unsigned 64, signed 64, unsigned 32, signed 32) as explicit min/max
pairs, together with a tnum. The 32-bit tasks retain this representation
because computing the optimal 32-bit result requires the 64-bit range
fields of the input.

## 1. The domain

A register state is a tnum together with four numeric ranges:

```lean
structure Tnum where
  value : BitVec 64
  mask  : BitVec 64

structure RegState where
  umin_value    : BitVec 64   -- unsigned 64-bit range
  umax_value    : BitVec 64
  smin_value    : BitVec 64   -- signed 64-bit range
  smax_value    : BitVec 64
  u32_min_value : BitVec 32   -- unsigned 32-bit range (low 32 bits)
  u32_max_value : BitVec 32
  s32_min_value : BitVec 32   -- signed 32-bit range (low 32 bits)
  s32_max_value : BitVec 32
  var_off       : Tnum
```

A tnum `(value, mask)` fixes the bits cleared in `mask` to the
corresponding bits of `value` and leaves the bits set in `mask` free:

```
x satisfies (value, mask)  iff  x &&& ~~~mask = value
```

## 2. Concretization and validity

A concrete 64-bit value is in the register's concretization when it
satisfies all five constraints: the four ranges and the tnum. The 32-bit
ranges constrain the low 32 bits.

```lean
def inGamma (reg : RegState) (x : BitVec 64) : Prop :=
  reg.umin_value ≤ x ∧ x ≤ reg.umax_value ∧
  reg.smin_value.toInt ≤ x.toInt ∧ x.toInt ≤ reg.smax_value.toInt ∧
  reg.u32_min_value ≤ x.truncate 32 ∧ (x.truncate 32 : BitVec 32) ≤ reg.u32_max_value ∧
  reg.s32_min_value.toInt ≤ (x.truncate 32 : BitVec 32).toInt ∧
    (x.truncate 32 : BitVec 32).toInt ≤ reg.s32_max_value.toInt ∧
  satisfiesTnum64 x reg.var_off.value reg.var_off.mask
```

A register state is valid when each range is ordered and the tnum is
consistent with the unsigned 64-bit range:

```lean
def validReg (reg : RegState) : Prop :=
  reg.umin_value ≤ reg.umax_value ∧
  reg.smin_value.toInt ≤ reg.smax_value.toInt ∧
  reg.u32_min_value ≤ reg.u32_max_value ∧
  reg.s32_min_value.toInt ≤ reg.s32_max_value.toInt ∧
  (reg.var_off.value &&& reg.var_off.mask) = 0 ∧
  reg.var_off.value ≤ reg.umin_value ∧
  reg.umax_value ≤ (reg.var_off.value ||| reg.var_off.mask)
```

The validity conditions rule out states that do not denote a set: an
inverted range, an inconsistent tnum, or a tnum whose bounds contradict
the unsigned range. Task preconditions add non-emptiness where needed.

## 3. Optimality

The ALU and cast tasks require the best abstract transformer. For a
transfer function `f` and inputs `a` (and `b`), the result `r` must be
sound and must be the least sound abstraction under concretization
containment:

```
sound r  :=  ∀ inputs, inGamma inputs → inGamma r (f inputs)

∀ r', validReg r' → sound r' → (∀ x, inGamma r x → inGamma r' x)
```

That is, `γ(r) ⊆ γ(r')` for every sound valid `r'`. This condition is
satisfiable in the interval + tnum domain because each factor of the
product admits a least cover of any nonempty finite set `S`:

- The unsigned 64-bit interval `[min_u S, max_u S]` is the least interval
  containing `S`, and likewise for the signed 64-bit and the two 32-bit
  projections.
- The least tnum covering `S` sets `mask` to the union of `x ^^^ y` over
  all `x, y ∈ S` and `value` to the fixed bits.

Each least cover is unique, so their product is a valid register state
whose concretization is contained in that of every sound state. The
least element therefore exists, and the specification is well posed.
This is the property that fails in the cnum domain, where a set can have
two incomparable minimal arcs; see `docs/cnum.md` section 3.

The branch tasks state correctness as an equivalence rather than
containment (section 4). The refinement tasks state soundness and
`γ`-containment optimality for each of the two refined states.

## 4. Task families

All tasks operate on the low 32 bits. The optimal 32-bit result must use
the 64-bit range fields of the inputs, not only the 32-bit fields, since
the 64-bit ranges can exclude values the 32-bit ranges admit.

| Family | Count | Operation | Specification |
|--------|-------|-----------|---------------|
| `Interval_Alu32{Add,Sub,And,Or,Xor,Lsh,Rsh,Arsh}` | 8 | 32-bit ALU, result zero-extended to 64 | best abstract transformer |
| `Interval_Jmp32{Eq,Lt,Le,Slt,Sle,Jset}` | 6 | branch outcome for a 32-bit comparison | `always` / `never` / `unknown`, equivalence spec |
| `Interval_RefineJmp32{Eq,Ne,Lt,Le,Slt,Sle,Jset,Xjset}` | 8 | refine two states on the taken branch | soundness and `γ`-containment optimality per state |

Shift tasks carry `hshift : ∀ s, inGamma src s → (s.truncate 32).toNat < 32`.
Branch and ALU tasks carry non-emptiness preconditions on the inputs.
Refinement tasks carry a feasibility precondition, so the optimal result
of an infeasible branch is never required.

Branch and refinement tasks provide the axiomatized tnum helpers
`tnumStepUp` and `tnumStepDown` with their specifications in the AXIOMS
section.
