/-
  LLVM KnownBits verification task: Signed Absolute Difference
  Operator: ISD::ABDS
  Source: LLVM KnownBits analysis, llvm/lib/Support/KnownBits.cpp

  Compute the optimal KnownBits for the result of
  signed 64-bit absolute difference (unsigned result) on two KnownBits.
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
def concreteAbds (x y : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (x.toInt - y.toInt).natAbs

/-- Compute the optimal KnownBits for Signed Absolute Difference. -/
def kbAbds (a b : KnownBits) : KnownBits :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC_CORRECT (provided) ===

theorem kbAbds_correct (a b : KnownBits)
    (ha : validKB a) (hb : validKB b) :
    let r := kbAbds a b
    -- Well-formedness: result is a valid KnownBits
    validKB r ∧
    -- Soundness: every concrete result is in the concretization
    (∀ x y, inKBGamma a x → inKBGamma b y →
      inKBGamma r (concreteAbds x y)) ∧
    -- Optimality: r is the ⊑-least sound abstraction
    (∀ r' : KnownBits, validKB r' →
      (∀ x y, inKBGamma a x → inKBGamma b y →
        inKBGamma r' (concreteAbds x y)) →
      (∀ z, inKBGamma r z → inKBGamma r' z)) := by
-- === END: SPEC_CORRECT ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end LLVM
