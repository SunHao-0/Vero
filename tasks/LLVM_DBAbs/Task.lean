/-
  LLVM DemandedBits verification task: Backward Demanded Bits for Abs
  Operator: @llvm.abs [IntMinIsPoison]
  Source: LLVM DemandedBits analysis, llvm/lib/Analysis/DemandedBits.cpp (determineLiveOperandBits)

  Compute the optimal backward demanded bits for
  64-bit absolute value (signed interpretation) with an optional IntMinIsPoison flag.
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
def concreteAbs (x : BitVec 64) : BitVec 64 :=
  if x.msb then -x else x

/-- Flag precondition. -/
def absIntMinPre (x : BitVec 64) : Prop :=
  x ≠ BitVec.ofInt 64 (-(2 ^ 63))

/-- Combined flag precondition. -/
def absFlags (x : BitVec 64) (flag : Bool) : Prop :=
  flag = true → absIntMinPre x

/-- Compute optimal backward demanded bits for Backward Demanded Bits for Abs. -/
def dbAbs (demanded : BitVec 64) (a : KnownBits) (flag : Bool)
    : BitVec 64 :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC_CORRECT (provided) ===

theorem dbAbs_correct (demanded : BitVec 64) (a : KnownBits) (flag : Bool)
    (ha : validKB a) :
    let dA := dbAbs demanded a flag
    -- (1) Demanded bits are among unknown bits only
    (dA &&& (a.zero ||| a.one)) = 0 ∧
    -- (2) Soundness: undemanded bits do not affect demanded output bits
    (∀ (i : Fin 64), dA.getLsbD i.val = false →
      ∀ x, inKBGamma a x → absFlags x flag →
        inKBGamma a (flipBit x i.val) → absFlags (flipBit x i.val) flag →
        (concreteAbs x) &&& demanded = (concreteAbs (flipBit x i.val)) &&& demanded) ∧
    -- (3) Optimality: every demanded bit is truly needed
    (∀ (i : Fin 64), dA.getLsbD i.val = true →
      ∃ x₁ x₂, inKBGamma a x₁ ∧ inKBGamma a x₂ ∧
        absFlags x₁ flag ∧ absFlags x₂ flag ∧
        x₁ ^^^ x₂ = ((1 : BitVec 64) <<< i.val) ∧
        (concreteAbs x₁) &&& demanded ≠ (concreteAbs x₂) &&& demanded) := by
-- === END: SPEC_CORRECT ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end LLVM
