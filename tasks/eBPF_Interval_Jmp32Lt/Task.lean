/-
  BPF JMP verification task: Less Than, unsigned (32-bit)
  Operator: JMP32_LT
  Source: Linux eBPF verifier, kernel/bpf/verifier.c (is_scalar_branch_taken)

  Determines if (x.truncate 32 : BitVec 32) < y.truncate 32 is always true, always false,
  or unknown for concrete values from two abstract register states.
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

/-- Branch analysis result. -/
inductive BranchResult where
  | always  : BranchResult
  | never   : BranchResult
  | unknown : BranchResult
  deriving DecidableEq, Repr

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

-- === BEGIN: AXIOMS (provided) ===

/-- Smallest value > z satisfying a tnum. -/
axiom tnumStepUp (tval tmask z : BitVec 64) : BitVec 64

axiom tnumStepUp_spec (tval tmask z : BitVec 64)
    (h_consistent : (tval &&& tmask) = 0)
    (h_lo : tval ≤ z)
    (h_hi : z < (tval ||| tmask)) :
    tval ≤ tnumStepUp tval tmask z ∧
    tnumStepUp tval tmask z ≤ (tval ||| tmask) ∧
    satisfiesTnum64 (tnumStepUp tval tmask z) tval tmask ∧
    z < tnumStepUp tval tmask z ∧
    (∀ (w : BitVec 64), satisfiesTnum64 w tval tmask → z < w →
      tnumStepUp tval tmask z ≤ w)

/-- Largest value < z satisfying a tnum. -/
axiom tnumStepDown (tval tmask z : BitVec 64) : BitVec 64

axiom tnumStepDown_spec (tval tmask z : BitVec 64)
    (h_consistent : (tval &&& tmask) = 0)
    (h_lo : tval < z)
    (h_hi : z ≤ (tval ||| tmask)) :
    tval ≤ tnumStepDown tval tmask z ∧
    tnumStepDown tval tmask z ≤ (tval ||| tmask) ∧
    satisfiesTnum64 (tnumStepDown tval tmask z) tval tmask ∧
    tnumStepDown tval tmask z < z ∧
    (∀ (w : BitVec 64), satisfiesTnum64 w tval tmask → w < z →
      w ≤ tnumStepDown tval tmask z)

/-- Decide branch outcome for Less Than, unsigned (32-bit). -/
def isJmp32LtTaken (reg1 reg2 : RegState) : BranchResult :=
-- === END: AXIOMS ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC (provided) ===

/-- All pairs (x, y) from gamma satisfy the relation. -/
def alwaysPropJmp32Lt (r1 r2 : RegState) : Prop :=
  ∀ (x y : BitVec 64), inGamma r1 x → inGamma r2 y → (x.truncate 32 : BitVec 32) < y.truncate 32

/-- No pair (x, y) from gamma satisfies the relation. -/
def neverPropJmp32Lt (r1 r2 : RegState) : Prop :=
  ∀ (x y : BitVec 64), inGamma r1 x → inGamma r2 y → ¬((x.truncate 32 : BitVec 32) < y.truncate 32)

theorem isJmp32LtTaken_correct (reg1 reg2 : RegState)
    (hv1 : validReg reg1) (hv2 : validReg reg2)
    (hne1 : ∃ x, inGamma reg1 x) (hne2 : ∃ y, inGamma reg2 y) :
    (isJmp32LtTaken reg1 reg2 = BranchResult.always ↔ alwaysPropJmp32Lt reg1 reg2) ∧
    (isJmp32LtTaken reg1 reg2 = BranchResult.never ↔ neverPropJmp32Lt reg1 reg2) ∧
    (isJmp32LtTaken reg1 reg2 = BranchResult.always ∨
     isJmp32LtTaken reg1 reg2 = BranchResult.never ∨
     isJmp32LtTaken reg1 reg2 = BranchResult.unknown) := by
-- === END: SPEC ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end BPF
