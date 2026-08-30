/-
  LLVM KnownBits verification task: Self-Multiplication (Squaring)
  Operator: mul [nsw] (x * x)
  Source: LLVM KnownBits analysis, llvm/lib/Support/KnownBits.cpp

  Compute the optimal KnownBits for the result of
  64-bit self-multiplication (x * x) on a single KnownBits with an optional flag.
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
def concreteMulSelf (x : BitVec 64) : BitVec 64 :=
  x * x

/-- Flag precondition. -/
def mulSelfNSWPre (x : BitVec 64) : Prop :=
  let sx := x.toInt
  let sr := sx * sx
  sr ≥ -(2 ^ 63 : Int) ∧ sr ≤ (2 ^ 63 - 1 : Int)

/-- Combined flag precondition. -/
def mulSelfFlags (x : BitVec 64) (flag : Bool) : Prop :=
  flag = true → mulSelfNSWPre x

/-- Compute the optimal KnownBits for Self-Multiplication (Squaring). -/
def kbMulSelf (a : KnownBits) (flag : Bool) : KnownBits :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC_CORRECT (provided) ===

theorem kbMulSelf_correct (a : KnownBits) (flag : Bool)
    (ha : validKB a)
    -- Non-emptiness: at least one valid non-poison input exists (some
    -- input satisfies the flag precondition). Without it the set of
    -- concrete results can be empty, and no ⊑-least sound KnownBits
    -- exists (the domain has no ⊥).
    (hne : ∃ x, inKBGamma a x ∧ mulSelfFlags x flag) :
    let r := kbMulSelf a flag
    -- Well-formedness: result is a valid KnownBits
    validKB r ∧
    -- Soundness: every concrete result is in the concretization
    (∀ x, inKBGamma a x → mulSelfFlags x flag →
      inKBGamma r (concreteMulSelf x)) ∧
    -- Optimality: r is the ⊑-least sound abstraction
    (∀ r' : KnownBits, validKB r' →
      (∀ x, inKBGamma a x → mulSelfFlags x flag →
        inKBGamma r' (concreteMulSelf x)) →
      (∀ z, inKBGamma r z → inKBGamma r' z)) := by
-- === END: SPEC_CORRECT ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end LLVM
