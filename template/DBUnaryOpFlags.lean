/-
  LLVM DemandedBits verification task: {{OPERATION_TITLE}}
  Operator: {{OPERATOR_NAME}}
  Source: LLVM DemandedBits analysis, llvm/lib/Analysis/DemandedBits.cpp (determineLiveOperandBits)

  Compute the optimal backward demanded bits for
  {{LEAN_OP_DESCRIPTION}} with an optional {{LEAN_FLAG_DESCRIPTION}} flag.
  Given which output bits are demanded and KnownBits of the input,
  determine the minimal set of input bits that are truly demanded.
  The result must be the optimal (minimal) demanded bit set.
-/
import Mathlib.Tactic
import Plausible

namespace LLVM

-- === BEGIN: DEFINITIONS (provided) ===

/-- KnownBits represents a set of 64-bit values:
    `zero` marks bits known to be 0, `one` marks bits known to be 1. -/
structure KnownBits where
  zero : BitVec 64
  one  : BitVec 64

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

/-- A KnownBits is well-formed: no bit is both known-zero and known-one. -/
def validKB (k : KnownBits) : Prop :=
  (k.zero &&& k.one) = 0

/-- A concrete value `x` is in the concretization of a KnownBits. -/
def inKBGamma (k : KnownBits) (x : BitVec 64) : Prop :=
  (x &&& k.zero) = 0 ∧ (x &&& k.one) = k.one

/-- Flip bit at position `i` in a 64-bit bitvector. -/
def flipBit (x : BitVec 64) (i : Nat) : BitVec 64 :=
  x ^^^ ((1 : BitVec 64) <<< i)

-- === END: PREDICATES ===

-- === BEGIN: SPEC (provided) ===

/-- The concrete operation. -/
def {{LEAN_CONCRETE_OP_NAME}} (x : BitVec 64) : BitVec 64 :=
  {{LEAN_CONCRETE_OP_BODY}}

/-- Flag precondition. -/
def {{LEAN_FLAG_PRE_NAME}} (x : BitVec 64) : Prop :=
  {{LEAN_FLAG_PRE_BODY}}

/-- Combined flag precondition. -/
def {{LEAN_FLAGS_NAME}} (x : BitVec 64) (flag : Bool) : Prop :=
  flag = true → {{LEAN_FLAG_PRE_NAME}} x

/-- Compute optimal backward demanded bits for {{OPERATION_TITLE}}. -/
def {{LEAN_FUNC_NAME}} (demanded : BitVec 64) (a : KnownBits) (flag : Bool)
    : BitVec 64 :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC_CORRECT (provided) ===

theorem {{LEAN_FUNC_NAME}}_correct (demanded : BitVec 64) (a : KnownBits) (flag : Bool)
    (ha : validKB a) :
    let dA := {{LEAN_FUNC_NAME}} demanded a flag
    -- (1) Demanded bits are among unknown bits only
    (dA &&& (a.zero ||| a.one)) = 0 ∧
    -- (2) Soundness: undemanded bits do not affect demanded output bits
    (∀ (i : Fin 64), dA.getLsbD i.val = false →
      ∀ x, inKBGamma a x → {{LEAN_FLAGS_NAME}} x flag →
        inKBGamma a (flipBit x i.val) → {{LEAN_FLAGS_NAME}} (flipBit x i.val) flag →
        ({{LEAN_CONCRETE_OP_NAME}} x) &&& demanded = ({{LEAN_CONCRETE_OP_NAME}} (flipBit x i.val)) &&& demanded) ∧
    -- (3) Optimality: every demanded bit is truly needed
    (∀ (i : Fin 64), dA.getLsbD i.val = true →
      ∃ x₁ x₂, inKBGamma a x₁ ∧ inKBGamma a x₂ ∧
        {{LEAN_FLAGS_NAME}} x₁ flag ∧ {{LEAN_FLAGS_NAME}} x₂ flag ∧
        x₁ ^^^ x₂ = ((1 : BitVec 64) <<< i.val) ∧
        ({{LEAN_CONCRETE_OP_NAME}} x₁) &&& demanded ≠ ({{LEAN_CONCRETE_OP_NAME}} x₂) &&& demanded) := by
-- === END: SPEC_CORRECT ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end LLVM
