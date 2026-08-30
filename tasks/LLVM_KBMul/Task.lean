/-
  LLVM KnownBits verification task: Multiplication
  Operator: mul [nsw] [nuw]
  Source: LLVM KnownBits analysis, llvm/lib/Support/KnownBits.cpp

  Compute the optimal KnownBits for the result of
  64-bit multiplication on two KnownBits with optional nsw/nuw flags.
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
def concreteMul (x y : BitVec 64) : BitVec 64 :=
  x * y

/-- NSW precondition: signed operation does not overflow. -/
def mulNSWPre (x y : BitVec 64) : Prop :=
  let sx := x.toInt
  let sy := y.toInt
  let sr := sx * sy
  sr ≥ -(2 ^ 63 : Int) ∧ sr ≤ (2 ^ 63 - 1 : Int)

/-- NUW precondition: unsigned operation does not overflow. -/
def mulNUWPre (x y : BitVec 64) : Prop :=
  x.toNat * y.toNat < 2 ^ 64

/-- Combined flag precondition. -/
def mulFlags (x y : BitVec 64) (nsw nuw : Bool) : Prop :=
  (nsw = true → mulNSWPre x y) ∧ (nuw = true → mulNUWPre x y)

/-- Compute the optimal KnownBits for Multiplication. -/
def kbMul (a b : KnownBits) (nsw nuw : Bool) : KnownBits :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC_CORRECT (provided) ===

theorem kbMul_correct (a b : KnownBits) (nsw nuw : Bool)
    (ha : validKB a) (hb : validKB b)
    -- Non-emptiness: at least one valid non-poison input exists (some
    -- input pair satisfies the nsw/nuw flag preconditions). Without it
    -- the set of concrete results can be empty, and no ⊑-least sound
    -- KnownBits exists (the domain has no ⊥).
    (hne : ∃ x y, inKBGamma a x ∧ inKBGamma b y ∧ mulFlags x y nsw nuw) :
    let r := kbMul a b nsw nuw
    -- Well-formedness: result is a valid KnownBits
    validKB r ∧
    -- Soundness: every concrete result is in the concretization
    (∀ x y, inKBGamma a x → inKBGamma b y →
      mulFlags x y nsw nuw →
      inKBGamma r (concreteMul x y)) ∧
    -- Optimality: r is the ⊑-least sound abstraction
    (∀ r' : KnownBits, validKB r' →
      (∀ x y, inKBGamma a x → inKBGamma b y →
        mulFlags x y nsw nuw →
        inKBGamma r' (concreteMul x y)) →
      (∀ z, inKBGamma r z → inKBGamma r' z)) := by
-- === END: SPEC_CORRECT ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end LLVM
