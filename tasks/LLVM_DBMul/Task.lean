/-
  LLVM DemandedBits verification task: Backward Demanded Bits for Mul
  Operator: mul [nsw] [nuw]
  Source: LLVM DemandedBits analysis, llvm/lib/Analysis/DemandedBits.cpp (determineLiveOperandBits)

  Compute the optimal backward demanded bits for
  64-bit multiplication with optional nsw/nuw flags.
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

/-- Compute optimal backward demanded bits for Backward Demanded Bits for Mul. -/
def dbMul (demanded : BitVec 64) (a b : KnownBits) (nsw nuw : Bool)
    : BitVec 64 × BitVec 64 :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC_CORRECT (provided) ===

theorem dbMul_correct (demanded : BitVec 64) (a b : KnownBits) (nsw nuw : Bool)
    (ha : validKB a) (hb : validKB b) :
    let (dA, dB) := dbMul demanded a b nsw nuw
    -- (1) Demanded bits are among unknown bits only
    ((dA &&& (a.zero ||| a.one)) = 0 ∧ (dB &&& (b.zero ||| b.one)) = 0) ∧
    -- (2) Soundness: undemanded bits do not affect demanded output bits
    ((∀ (i : Fin 64), dA.getLsbD i.val = false →
        ∀ x y, inKBGamma a x → inKBGamma b y → mulFlags x y nsw nuw →
          inKBGamma a (flipBit x i.val) → mulFlags (flipBit x i.val) y nsw nuw →
          (concreteMul x y) &&& demanded = (concreteMul (flipBit x i.val) y) &&& demanded) ∧
     (∀ (j : Fin 64), dB.getLsbD j.val = false →
        ∀ x y, inKBGamma a x → inKBGamma b y → mulFlags x y nsw nuw →
          inKBGamma b (flipBit y j.val) → mulFlags x (flipBit y j.val) nsw nuw →
          (concreteMul x y) &&& demanded = (concreteMul x (flipBit y j.val)) &&& demanded)) ∧
    -- (3) Optimality: every demanded bit is truly needed
    ((∀ (i : Fin 64), dA.getLsbD i.val = true →
        ∃ x₁ x₂ y, inKBGamma a x₁ ∧ inKBGamma a x₂ ∧ inKBGamma b y ∧
          mulFlags x₁ y nsw nuw ∧ mulFlags x₂ y nsw nuw ∧
          x₁ ^^^ x₂ = ((1 : BitVec 64) <<< i.val) ∧
          (concreteMul x₁ y) &&& demanded ≠ (concreteMul x₂ y) &&& demanded) ∧
     (∀ (j : Fin 64), dB.getLsbD j.val = true →
        ∃ x y₁ y₂, inKBGamma a x ∧ inKBGamma b y₁ ∧ inKBGamma b y₂ ∧
          mulFlags x y₁ nsw nuw ∧ mulFlags x y₂ nsw nuw ∧
          y₁ ^^^ y₂ = ((1 : BitVec 64) <<< j.val) ∧
          (concreteMul x y₁) &&& demanded ≠ (concreteMul x y₂) &&& demanded)) := by
-- === END: SPEC_CORRECT ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end LLVM
