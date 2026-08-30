/-
  BPF ALU verification task: Bitwise AND (32-bit)
  Operator: ALU32_AND
  Source: Linux eBPF verifier, kernel/bpf/verifier.c (adjust_scalar_min_max_vals, scalar32_min_max_*)

  Compute the optimal abstract state for the result of
  32-bit bitwise AND, zero-extended to 64 on two abstract register states.
  The result must be the best abstract transformer (α ∘ f ∘ γ).
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

/-- The concrete ALU operation. -/
def concreteAnd32 (d s : BitVec 64) : BitVec 64 :=
  (((d.truncate 32 : BitVec 32) &&& (s.truncate 32 : BitVec 32)).zeroExtend 64 : BitVec 64)

/-- Compute the optimal abstract state for Bitwise AND (32-bit). -/
def alu32And (dst src : RegState) : RegState :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC_CORRECT (provided) ===

theorem alu32And_correct (dst src : RegState)
    (hv1 : validReg dst) (hv2 : validReg src)
    (hne1 : ∃ d, inGamma dst d) (hne2 : ∃ s, inGamma src s)
     :
    let r := alu32And dst src
    -- Well-formedness: result is a valid register state
    validReg r ∧
    -- Soundness: every concrete result is in γ(r)
    (∀ d s, inGamma dst d → inGamma src s → inGamma r (concreteAnd32 d s)) ∧
    -- Optimality: r is the ⊑-least sound abstraction (best abstract transformer)
    (∀ r' : RegState, validReg r' →
      (∀ d s, inGamma dst d → inGamma src s → inGamma r' (concreteAnd32 d s)) →
      (∀ x, inGamma r x → inGamma r' x)) := by
-- === END: SPEC_CORRECT ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end BPF
