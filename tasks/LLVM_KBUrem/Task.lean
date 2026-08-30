/-
  LLVM KnownBits verification task: Unsigned Remainder
  Operator: urem
  Source: LLVM KnownBits analysis, llvm/lib/Support/KnownBits.cpp

  Compute the optimal KnownBits for the result of
  unsigned 64-bit remainder on two KnownBits where the divisor is non-zero.
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

/-- The concrete operation (divisor must be non-zero). -/
def concreteUrem (x y : BitVec 64) : BitVec 64 :=
  x % y

/-- Compute the optimal KnownBits for Unsigned Remainder. -/
def kbUrem (a b : KnownBits) : KnownBits :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC_CORRECT (provided) ===

theorem kbUrem_correct (a b : KnownBits)
    (ha : validKB a) (hb : validKB b)
    -- Non-emptiness: at least one valid non-poison input exists (the
    -- divisor is not forced to 0). Without it the set of concrete
    -- results can be empty, and no ⊑-least sound KnownBits exists
    -- (every valid KnownBits has a non-empty concretization, so the
    -- domain has no ⊥).
    (hne : ∃ x y, inKBGamma a x ∧ inKBGamma b y ∧ y ≠ 0) :
    let r := kbUrem a b
    -- Well-formedness: result is a valid KnownBits
    validKB r ∧
    -- Soundness: every concrete result is in the concretization
    (∀ x y, inKBGamma a x → inKBGamma b y → y ≠ 0 →
      inKBGamma r (concreteUrem x y)) ∧
    -- Optimality: r is the ⊑-least sound abstraction
    (∀ r' : KnownBits, validKB r' →
      (∀ x y, inKBGamma a x → inKBGamma b y → y ≠ 0 →
        inKBGamma r' (concreteUrem x y)) →
      (∀ z, inKBGamma r z → inKBGamma r' z)) := by
-- === END: SPEC_CORRECT ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end LLVM
