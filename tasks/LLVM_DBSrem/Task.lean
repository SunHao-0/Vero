/-
  LLVM DemandedBits verification task: Backward Demanded Bits for SRem
  Operator: srem
  Source: LLVM DemandedBits analysis, llvm/lib/Analysis/DemandedBits.cpp (determineLiveOperandBits)

  Compute the optimal backward demanded bits for
  signed 64-bit remainder.
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
def concreteSrem (x y : BitVec 64) : BitVec 64 :=
  BitVec.ofInt 64 (x.toInt.tmod y.toInt)

/-- Compute optimal backward demanded bits for Backward Demanded Bits for SRem. -/
def dbSrem (demanded : BitVec 64) (a b : KnownBits)
    : BitVec 64 × BitVec 64 :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC_CORRECT (provided) ===

theorem dbSrem_correct (demanded : BitVec 64) (a b : KnownBits)
    (ha : validKB a) (hb : validKB b) :
    let (dA, dB) := dbSrem demanded a b
    -- (1) Demanded bits are among unknown bits only
    ((dA &&& (a.zero ||| a.one)) = 0 ∧ (dB &&& (b.zero ||| b.one)) = 0) ∧
    -- (2) Soundness: undemanded bits do not affect demanded output bits
    ((∀ (i : Fin 64), dA.getLsbD i.val = false →
        ∀ x y, inKBGamma a x → inKBGamma b y → y ≠ 0 →
          inKBGamma a (flipBit x i.val) →
          (concreteSrem x y) &&& demanded = (concreteSrem (flipBit x i.val) y) &&& demanded) ∧
     (∀ (j : Fin 64), dB.getLsbD j.val = false →
        ∀ x y, inKBGamma a x → inKBGamma b y → y ≠ 0 →
          inKBGamma b (flipBit y j.val) → (flipBit y j.val) ≠ 0 →
          (concreteSrem x y) &&& demanded = (concreteSrem x (flipBit y j.val)) &&& demanded)) ∧
    -- (3) Optimality: every demanded bit is truly needed
    ((∀ (i : Fin 64), dA.getLsbD i.val = true →
        ∃ x₁ x₂ y, inKBGamma a x₁ ∧ inKBGamma a x₂ ∧ inKBGamma b y ∧ y ≠ 0 ∧
          x₁ ^^^ x₂ = ((1 : BitVec 64) <<< i.val) ∧
          (concreteSrem x₁ y) &&& demanded ≠ (concreteSrem x₂ y) &&& demanded) ∧
     (∀ (j : Fin 64), dB.getLsbD j.val = true →
        ∃ x y₁ y₂, inKBGamma a x ∧ inKBGamma b y₁ ∧ inKBGamma b y₂ ∧
          y₁ ≠ 0 ∧ y₂ ≠ 0 ∧
          y₁ ^^^ y₂ = ((1 : BitVec 64) <<< j.val) ∧
          (concreteSrem x y₁) &&& demanded ≠ (concreteSrem x y₂) &&& demanded)) := by
-- === END: SPEC_CORRECT ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end LLVM
