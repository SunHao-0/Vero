/-
  LLVM KnownBits verification task: {{OPERATION_TITLE}}
  Operator: {{OPERATOR_NAME}}
  Source: LLVM KnownBits analysis, llvm/lib/Support/KnownBits.cpp

  Compute the optimal KnownBits for the result of
  {{LEAN_OP_DESCRIPTION}} on two KnownBits with optional nsw/nuw flags.
  The result must be the best abstract transformer (α ∘ f ∘ γ).
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

/-- Compute the optimal KnownBits for {{OPERATION_TITLE}}. -/
def {{LEAN_FUNC_NAME}} (a b : KnownBits) (nsw nuw : Bool) : KnownBits :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC_CORRECT (provided) ===

theorem {{LEAN_FUNC_NAME}}_correct (a b : KnownBits) (nsw nuw : Bool)
    (ha : validKB a) (hb : validKB b)
    -- Non-emptiness: at least one valid non-poison input exists (some
    -- input pair satisfies the nsw/nuw flag preconditions). Without it
    -- the set of concrete results can be empty, and no ⊑-least sound
    -- KnownBits exists (the domain has no ⊥).
    (hne : ∃ x y, inKBGamma a x ∧ inKBGamma b y ∧ {{LEAN_FLAGS_NAME}} x y nsw nuw) :
    let r := {{LEAN_FUNC_NAME}} a b nsw nuw
    -- Well-formedness: result is a valid KnownBits
    validKB r ∧
    -- Soundness: every concrete result is in the concretization
    (∀ x y, inKBGamma a x → inKBGamma b y →
      {{LEAN_FLAGS_NAME}} x y nsw nuw →
      inKBGamma r ({{LEAN_CONCRETE_OP_NAME}} x y)) ∧
    -- Optimality: r is the ⊑-least sound abstraction
    (∀ r' : KnownBits, validKB r' →
      (∀ x y, inKBGamma a x → inKBGamma b y →
        {{LEAN_FLAGS_NAME}} x y nsw nuw →
        inKBGamma r' ({{LEAN_CONCRETE_OP_NAME}} x y)) →
      (∀ z, inKBGamma r z → inKBGamma r' z)) := by
-- === END: SPEC_CORRECT ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end LLVM
