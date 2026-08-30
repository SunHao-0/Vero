/-
  LLVM KnownBits verification task: Unsigned Division
  Operator: udiv [exact]
  Source: LLVM KnownBits analysis, llvm/lib/Support/KnownBits.cpp

  Compute the optimal KnownBits for the result of
  unsigned 64-bit division on two KnownBits with an optional exact flag.
  The divisor is non-zero; if exact, the division has no remainder.
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
def concreteUdiv (x y : BitVec 64) : BitVec 64 :=
  x / y

/-- Exact precondition: division has no remainder. -/
def udivExactPre (x y : BitVec 64) : Prop :=
  x % y = 0

/-- Compute the optimal KnownBits for Unsigned Division. -/
def kbUdiv (a b : KnownBits) (exact : Bool) : KnownBits :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC_CORRECT (provided) ===

theorem kbUdiv_correct (a b : KnownBits) (exact : Bool)
    (ha : validKB a) (hb : validKB b)
    -- Non-emptiness: at least one valid non-poison input exists (the
    -- divisor is not forced to 0, and if `exact` the quotient is exact).
    -- Without it the set of concrete results can be empty, and no
    -- ⊑-least sound KnownBits exists (the domain has no ⊥).
    (hne : ∃ x y, inKBGamma a x ∧ inKBGamma b y ∧ y ≠ 0 ∧
      (exact = true → udivExactPre x y)) :
    let r := kbUdiv a b exact
    -- Well-formedness: result is a valid KnownBits
    validKB r ∧
    -- Soundness: every concrete result is in the concretization
    (∀ x y, inKBGamma a x → inKBGamma b y → y ≠ 0 →
      (exact = true → udivExactPre x y) →
      inKBGamma r (concreteUdiv x y)) ∧
    -- Optimality: r is the ⊑-least sound abstraction
    (∀ r' : KnownBits, validKB r' →
      (∀ x y, inKBGamma a x → inKBGamma b y → y ≠ 0 →
        (exact = true → udivExactPre x y) →
        inKBGamma r' (concreteUdiv x y)) →
      (∀ z, inKBGamma r z → inKBGamma r' z)) := by
-- === END: SPEC_CORRECT ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end LLVM
