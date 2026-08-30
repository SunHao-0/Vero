/-
  BPF verification task: Register Bounds Synchronization
  Operator: REG_BOUNDS_SYNC
  Source: Linux eBPF verifier, kernel/bpf/verifier.c (reg_bounds_sync)

  Compute the reduced product canonical form of a register state:
  tighten each component domain to its optimal value without
  changing the set of concrete values represented.
  The result must be component-wise optimal (reduced form).
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

/-- Abstract register state tracking value ranges and tnum constraint. -/
structure RegState where
  umin_value    : BitVec 64
  umax_value    : BitVec 64
  smin_value    : BitVec 64
  smax_value    : BitVec 64
  u32_min_value : BitVec 32
  u32_max_value : BitVec 32
  s32_min_value : BitVec 32
  s32_max_value : BitVec 32
  var_off       : Tnum

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

/-- A value `x` satisfies a 64-bit tnum constraint. -/
def satisfiesTnum64 (x tval tmask : BitVec 64) : Prop :=
  (x &&& ~~~tmask) = tval

/-- A concrete value `x` is in the gamma (concretization) of a register state
    iff it satisfies ALL five constraints: u64 range, s64 range,
    u32 range, s32 range, and tnum. -/
def inGamma (reg : RegState) (x : BitVec 64) : Prop :=
  -- unsigned 64-bit range
  reg.umin_value ≤ x ∧ x ≤ reg.umax_value ∧
  -- signed 64-bit range
  reg.smin_value.toInt ≤ x.toInt ∧ x.toInt ≤ reg.smax_value.toInt ∧
  -- unsigned 32-bit range
  reg.u32_min_value ≤ x.truncate 32 ∧ (x.truncate 32 : BitVec 32) ≤ reg.u32_max_value ∧
  -- signed 32-bit range
  reg.s32_min_value.toInt ≤ (x.truncate 32 : BitVec 32).toInt ∧
    (x.truncate 32 : BitVec 32).toInt ≤ reg.s32_max_value.toInt ∧
  -- tnum constraint
  satisfiesTnum64 x reg.var_off.value reg.var_off.mask

/-- A register state is valid if all ranges are well-formed and
    consistent with the tnum. -/
def validReg (reg : RegState) : Prop :=
  reg.umin_value ≤ reg.umax_value ∧
  reg.smin_value.toInt ≤ reg.smax_value.toInt ∧
  reg.u32_min_value ≤ reg.u32_max_value ∧
  reg.s32_min_value.toInt ≤ reg.s32_max_value.toInt ∧
  (reg.var_off.value &&& reg.var_off.mask) = 0 ∧
  reg.var_off.value ≤ reg.umin_value ∧
  reg.umax_value ≤ (reg.var_off.value ||| reg.var_off.mask)

-- === END: PREDICATES ===

-- === BEGIN: SPEC (provided) ===

/-- Compute the reduced product canonical form of a register state. -/
def regBoundsSync (reg : RegState) : RegState :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC_CORRECT (provided) ===

theorem regBoundsSync_correct (reg : RegState)
    (hv : validReg reg)
    (hne : ∃ x, inGamma reg x) :
    let r := regBoundsSync reg
    -- Well-formedness: result is a valid register state
    validReg r ∧
    -- Soundness: don't lose any concrete value
    (∀ x, inGamma reg x → inGamma r x) ∧
    -- Component-wise optimality: r is the tightest RegState
    -- covering γ(reg) in every component domain simultaneously
    (∀ r' : RegState, validReg r' →
      (∀ x, inGamma reg x → inGamma r' x) →
      r.umin_value ≥ r'.umin_value ∧
      r.umax_value ≤ r'.umax_value ∧
      r.smin_value.toInt ≥ r'.smin_value.toInt ∧
      r.smax_value.toInt ≤ r'.smax_value.toInt ∧
      r.u32_min_value ≥ r'.u32_min_value ∧
      r.u32_max_value ≤ r'.u32_max_value ∧
      r.s32_min_value.toInt ≥ r'.s32_min_value.toInt ∧
      r.s32_max_value.toInt ≤ r'.s32_max_value.toInt ∧
      (r.var_off.mask &&& ~~~r'.var_off.mask) = 0) := by
-- === END: SPEC_CORRECT ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end BPF
