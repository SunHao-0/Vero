/-
  BPF cnum ALU verification task: Arithmetic Right Shift (64-bit, cnum domain)
  Operator: ALU64_ARSH
  Source: Linux eBPF verifier (bpf-next cnum domain), kernel/bpf/verifier.c (adjust_scalar_min_max_vals) and kernel/bpf/cnum.c

  Compute the optimal abstract state for the result of
  arithmetic right shift ((s64)dst >> src), shift amount < 64 on two abstract register states in the
  bpf-next cnum + tnum domain: a 64-bit tnum plus 64-bit and 32-bit
  circular ranges (cnums).
  The result must be sound and component-wise optimal: its cnums are
  minimum-size arc covers and its tnum mask is minimal among all sound
  results. (A ⊑-least sound RegState does not always exist in the cnum
  domain — minimum-size arc covers can tie — hence the component-wise
  formulation.)
-/
import Mathlib.Tactic
import Plausible

namespace BPF

-- === BEGIN: DEFINITIONS (provided) ===

/-- A tnum represents a set of 64-bit values:
    known bits are fixed by `value`, unknown bits are indicated by `mask`. -/
structure Tnum where
  value : BitVec 64
  mask  : BitVec 64

/-- A 64-bit cnum (circular number) represents a contiguous arc of the
    2^64 value circle: the values `base, base + 1, ..., base + size`
    (wrapping mod 2^64), i.e. `size + 1` consecutive values.
    The reserved encoding `base = size = 2^64 - 1` denotes the empty set;
    the full circle is representable with any other base and
    `size = 2^64 - 1`. -/
structure Cnum64 where
  base : BitVec 64
  size : BitVec 64

/-- A 32-bit cnum: an arc on the 2^32 value circle, with the analogous
    reserved empty encoding `base = size = 2^32 - 1`. -/
structure Cnum32 where
  base : BitVec 32
  size : BitVec 32

/-- Abstract register state of the bpf-next verifier: a 64-bit tnum plus
    64-bit and 32-bit circular ranges. The 32-bit cnum constrains the
    low 32 bits of the value. -/
structure RegState where
  var_off : Tnum
  r64     : Cnum64
  r32     : Cnum32

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

/-- A value `x` satisfies a 64-bit tnum constraint. -/
def satisfiesTnum64 (x tval tmask : BitVec 64) : Prop :=
  (x &&& ~~~tmask) = tval

/-- The reserved empty encoding of a 64-bit cnum. -/
def cnum64IsEmpty (c : Cnum64) : Prop :=
  c.base = BitVec.allOnes 64 ∧ c.size = BitVec.allOnes 64

/-- The reserved empty encoding of a 32-bit cnum. -/
def cnum32IsEmpty (c : Cnum32) : Prop :=
  c.base = BitVec.allOnes 32 ∧ c.size = BitVec.allOnes 32

/-- A value `x` is in the concretization of a 64-bit cnum:
    `x` lies on the arc, i.e. `x - base ≤ size` (wrapping subtraction). -/
def inCnum64Gamma (c : Cnum64) (x : BitVec 64) : Prop :=
  ¬ cnum64IsEmpty c ∧ x - c.base ≤ c.size

/-- A value `x` is in the concretization of a 32-bit cnum. -/
def inCnum32Gamma (c : Cnum32) (x : BitVec 32) : Prop :=
  ¬ cnum32IsEmpty c ∧ x - c.base ≤ c.size

/-- A concrete value `x` is in the gamma (concretization) of a register
    state iff it satisfies ALL three constraints: the tnum, the 64-bit
    cnum, and the 32-bit cnum (on the low 32 bits of `x`). -/
def inGamma (reg : RegState) (x : BitVec 64) : Prop :=
  satisfiesTnum64 x reg.var_off.value reg.var_off.mask ∧
  inCnum64Gamma reg.r64 x ∧
  inCnum32Gamma reg.r32 (x.truncate 32)

/-- A register state is well-formed if its tnum is consistent.
    (Every cnum encoding is meaningful — an arc or the reserved empty
    encoding — so no further conditions are needed.) -/
def validReg (reg : RegState) : Prop :=
  (reg.var_off.value &&& reg.var_off.mask) = 0

-- === END: PREDICATES ===

-- === BEGIN: SPEC (provided) ===

/-- The concrete ALU operation. -/
def concreteArsh64 (d s : BitVec 64) : BitVec 64 :=
  BitVec.ofInt 64 (d.toInt >>> s.toNat)

/-- Compute the optimal abstract state for Arithmetic Right Shift (64-bit, cnum domain). -/
def alu64Arsh (dst src : RegState) : RegState :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC_CORRECT (provided) ===

theorem alu64Arsh_correct (dst src : RegState)
    (hv1 : validReg dst) (hv2 : validReg src)
    (hne1 : ∃ d, inGamma dst d) (hne2 : ∃ s, inGamma src s)
    (hshift : ∀ s, inGamma src s → s.toNat < 64) :
    let r := alu64Arsh dst src
    -- Well-formedness: result is a valid register state
    validReg r ∧
    -- Soundness: every concrete result is in γ(r)
    (∀ d s, inGamma dst d → inGamma src s → inGamma r (concreteArsh64 d s)) ∧
    -- Optimality (component-wise): against every sound valid r', the
    -- result's cnums are minimum-size arc covers and its tnum mask is
    -- minimal
    (∀ r' : RegState, validReg r' →
      (∀ d s, inGamma dst d → inGamma src s → inGamma r' (concreteArsh64 d s)) →
      r.r64.size ≤ r'.r64.size ∧
      r.r32.size ≤ r'.r32.size ∧
      (r.var_off.mask &&& ~~~r'.var_off.mask) = 0) := by
-- === END: SPEC_CORRECT ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end BPF
