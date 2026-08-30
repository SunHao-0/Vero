/-
  LLVM DemandedBits verification task: Backward Demanded Bits for UDiv
  Operator: udiv [exact]
  Source: LLVM DemandedBits analysis, llvm/lib/Analysis/DemandedBits.cpp (determineLiveOperandBits)

  Compute the optimal backward demanded bits for
  unsigned 64-bit division with an optional exact flag.
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
def concreteUdiv (x y : BitVec 64) : BitVec 64 :=
  x / y

/-- Exact precondition: division is exact (no remainder). -/
def udivExactPre (x y : BitVec 64) : Prop :=
  x % y = 0

/-- Combined flag precondition. -/
def udivFlags (x y : BitVec 64) (exact : Bool) : Prop :=
  exact = true → udivExactPre x y

/-- Compute optimal backward demanded bits for Backward Demanded Bits for UDiv. -/
def dbUdiv (demanded : BitVec 64) (a b : KnownBits) (exact : Bool)
    : BitVec 64 × BitVec 64 :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC_CORRECT (provided) ===

theorem dbUdiv_correct (demanded : BitVec 64) (a b : KnownBits) (exact : Bool)
    (ha : validKB a) (hb : validKB b) :
    let (dA, dB) := dbUdiv demanded a b exact
    -- (1) Demanded bits are among unknown bits only
    ((dA &&& (a.zero ||| a.one)) = 0 ∧ (dB &&& (b.zero ||| b.one)) = 0) ∧
    -- (2) Soundness: undemanded bits do not affect demanded output bits
    ((∀ (i : Fin 64), dA.getLsbD i.val = false →
        ∀ x y, inKBGamma a x → inKBGamma b y → y ≠ 0 → udivFlags x y exact →
          inKBGamma a (flipBit x i.val) → udivFlags (flipBit x i.val) y exact →
          (concreteUdiv x y) &&& demanded = (concreteUdiv (flipBit x i.val) y) &&& demanded) ∧
     (∀ (j : Fin 64), dB.getLsbD j.val = false →
        ∀ x y, inKBGamma a x → inKBGamma b y → y ≠ 0 → udivFlags x y exact →
          inKBGamma b (flipBit y j.val) → (flipBit y j.val) ≠ 0 →
          udivFlags x (flipBit y j.val) exact →
          (concreteUdiv x y) &&& demanded = (concreteUdiv x (flipBit y j.val)) &&& demanded)) ∧
    -- (3) Optimality: every demanded bit is truly needed
    ((∀ (i : Fin 64), dA.getLsbD i.val = true →
        ∃ x₁ x₂ y, inKBGamma a x₁ ∧ inKBGamma a x₂ ∧ inKBGamma b y ∧ y ≠ 0 ∧
          udivFlags x₁ y exact ∧ udivFlags x₂ y exact ∧
          x₁ ^^^ x₂ = ((1 : BitVec 64) <<< i.val) ∧
          (concreteUdiv x₁ y) &&& demanded ≠ (concreteUdiv x₂ y) &&& demanded) ∧
     (∀ (j : Fin 64), dB.getLsbD j.val = true →
        ∃ x y₁ y₂, inKBGamma a x ∧ inKBGamma b y₁ ∧ inKBGamma b y₂ ∧
          y₁ ≠ 0 ∧ y₂ ≠ 0 ∧
          udivFlags x y₁ exact ∧ udivFlags x y₂ exact ∧
          y₁ ^^^ y₂ = ((1 : BitVec 64) <<< j.val) ∧
          (concreteUdiv x y₁) &&& demanded ≠ (concreteUdiv x y₂) &&& demanded)) := by
-- === END: SPEC_CORRECT ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end LLVM
