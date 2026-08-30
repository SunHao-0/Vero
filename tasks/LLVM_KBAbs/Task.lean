/-
  LLVM KnownBits verification task: Absolute Value
  Operator: @llvm.abs [IntMinIsPoison]
  Source: LLVM KnownBits analysis, llvm/lib/Support/KnownBits.cpp

  Compute the optimal KnownBits for the result of
  64-bit absolute value (signed interpretation) on a single KnownBits with an optional flag.
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
def concreteAbs (x : BitVec 64) : BitVec 64 :=
  if x.msb then -x else x

/-- Flag precondition. -/
def absIntMinPre (x : BitVec 64) : Prop :=
  x ≠ BitVec.ofInt 64 (-(2 ^ 63))

/-- Combined flag precondition. -/
def absFlags (x : BitVec 64) (flag : Bool) : Prop :=
  flag = true → absIntMinPre x

/-- Compute the optimal KnownBits for Absolute Value. -/
def kbAbs (a : KnownBits) (flag : Bool) : KnownBits :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC_CORRECT (provided) ===

theorem kbAbs_correct (a : KnownBits) (flag : Bool)
    (ha : validKB a)
    -- Non-emptiness: at least one valid non-poison input exists (some
    -- input satisfies the flag precondition). Without it the set of
    -- concrete results can be empty, and no ⊑-least sound KnownBits
    -- exists (the domain has no ⊥).
    (hne : ∃ x, inKBGamma a x ∧ absFlags x flag) :
    let r := kbAbs a flag
    -- Well-formedness: result is a valid KnownBits
    validKB r ∧
    -- Soundness: every concrete result is in the concretization
    (∀ x, inKBGamma a x → absFlags x flag →
      inKBGamma r (concreteAbs x)) ∧
    -- Optimality: r is the ⊑-least sound abstraction
    (∀ r' : KnownBits, validKB r' →
      (∀ x, inKBGamma a x → absFlags x flag →
        inKBGamma r' (concreteAbs x)) →
      (∀ z, inKBGamma r z → inKBGamma r' z)) := by
-- === END: SPEC_CORRECT ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end LLVM
