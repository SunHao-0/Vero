/-
  LLVM DemandedBits verification task: {{OPERATION_TITLE}}
  Operator: {{OPERATOR_NAME}}
  Source: LLVM DemandedBits analysis, llvm/lib/Analysis/DemandedBits.cpp (determineLiveOperandBits)

  Compute the optimal backward demanded bits for
  {{LEAN_OP_DESCRIPTION}} with optional nsw/nuw flags.
  Given which output bits are demanded and KnownBits of both inputs,
  determine the minimal set of input bits that are truly demanded.
  The result must be the optimal (minimal) demanded bit sets.
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
def {{LEAN_CONCRETE_OP_NAME}} (x y : BitVec 64) : BitVec 64 :=
  {{LEAN_CONCRETE_OP_BODY}}

/-- NSW precondition: signed operation does not overflow. -/
def {{LEAN_NSW_PRE_NAME}} (x y : BitVec 64) : Prop :=
  {{LEAN_NSW_PRE_BODY}}

/-- NUW precondition: unsigned operation does not overflow. -/
def {{LEAN_NUW_PRE_NAME}} (x y : BitVec 64) : Prop :=
  {{LEAN_NUW_PRE_BODY}}

/-- Combined flag precondition. -/
def {{LEAN_FLAGS_NAME}} (x y : BitVec 64) (nsw nuw : Bool) : Prop :=
  (nsw = true → {{LEAN_NSW_PRE_NAME}} x y) ∧ (nuw = true → {{LEAN_NUW_PRE_NAME}} x y)

/-- Compute optimal backward demanded bits for {{OPERATION_TITLE}}. -/
def {{LEAN_FUNC_NAME}} (demanded : BitVec 64) (a b : KnownBits) (nsw nuw : Bool)
    : BitVec 64 × BitVec 64 :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC_CORRECT (provided) ===

theorem {{LEAN_FUNC_NAME}}_correct (demanded : BitVec 64) (a b : KnownBits) (nsw nuw : Bool)
    (ha : validKB a) (hb : validKB b) :
    let (dA, dB) := {{LEAN_FUNC_NAME}} demanded a b nsw nuw
    -- (1) Demanded bits are among unknown bits only
    ((dA &&& (a.zero ||| a.one)) = 0 ∧ (dB &&& (b.zero ||| b.one)) = 0) ∧
    -- (2) Soundness: undemanded bits do not affect demanded output bits
    ((∀ (i : Fin 64), dA.getLsbD i.val = false →
        ∀ x y, inKBGamma a x → inKBGamma b y → {{LEAN_FLAGS_NAME}} x y nsw nuw →
          inKBGamma a (flipBit x i.val) → {{LEAN_FLAGS_NAME}} (flipBit x i.val) y nsw nuw →
          ({{LEAN_CONCRETE_OP_NAME}} x y) &&& demanded = ({{LEAN_CONCRETE_OP_NAME}} (flipBit x i.val) y) &&& demanded) ∧
     (∀ (j : Fin 64), dB.getLsbD j.val = false →
        ∀ x y, inKBGamma a x → inKBGamma b y → {{LEAN_FLAGS_NAME}} x y nsw nuw →
          inKBGamma b (flipBit y j.val) → {{LEAN_FLAGS_NAME}} x (flipBit y j.val) nsw nuw →
          ({{LEAN_CONCRETE_OP_NAME}} x y) &&& demanded = ({{LEAN_CONCRETE_OP_NAME}} x (flipBit y j.val)) &&& demanded)) ∧
    -- (3) Optimality: every demanded bit is truly needed
    ((∀ (i : Fin 64), dA.getLsbD i.val = true →
        ∃ x₁ x₂ y, inKBGamma a x₁ ∧ inKBGamma a x₂ ∧ inKBGamma b y ∧
          {{LEAN_FLAGS_NAME}} x₁ y nsw nuw ∧ {{LEAN_FLAGS_NAME}} x₂ y nsw nuw ∧
          x₁ ^^^ x₂ = ((1 : BitVec 64) <<< i.val) ∧
          ({{LEAN_CONCRETE_OP_NAME}} x₁ y) &&& demanded ≠ ({{LEAN_CONCRETE_OP_NAME}} x₂ y) &&& demanded) ∧
     (∀ (j : Fin 64), dB.getLsbD j.val = true →
        ∃ x y₁ y₂, inKBGamma a x ∧ inKBGamma b y₁ ∧ inKBGamma b y₂ ∧
          {{LEAN_FLAGS_NAME}} x y₁ nsw nuw ∧ {{LEAN_FLAGS_NAME}} x y₂ nsw nuw ∧
          y₁ ^^^ y₂ = ((1 : BitVec 64) <<< j.val) ∧
          ({{LEAN_CONCRETE_OP_NAME}} x y₁) &&& demanded ≠ ({{LEAN_CONCRETE_OP_NAME}} x y₂) &&& demanded)) := by
-- === END: SPEC_CORRECT ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end LLVM
