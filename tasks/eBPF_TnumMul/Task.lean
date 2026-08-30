/-
  BPF tnum verification task: Tnum Multiplication
  Operator: TNUM_MUL
  Source: Linux eBPF verifier tnum analysis, kernel/bpf/tnum.c

  Compute the optimal tnum for the result of
  wrapping 64-bit multiplication of two tnums on two tnums.
  The result must be the best abstract transformer (α ∘ f ∘ γ).
-/
import Mathlib.Tactic
import Plausible

namespace BPF

-- === BEGIN: DEFINITIONS (provided) ===

/-- A tnum represents a set of 64-bit values:
    known bits are fixed by `value`, unknown bits are indicated by `mask`. -/
structure Tnum where
  value : BitVec 64
  mask  : BitVec 64

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

/-- A value `x` satisfies a 64-bit tnum constraint. -/
def satisfiesTnum64 (x tval tmask : BitVec 64) : Prop :=
  (x &&& ~~~tmask) = tval

/-- A tnum is well-formed: known bits and unknown bits don't overlap. -/
def validTnum (t : Tnum) : Prop :=
  (t.value &&& t.mask) = 0

/-- A concrete value `x` is in the concretization of a tnum. -/
def inTnumGamma (t : Tnum) (x : BitVec 64) : Prop :=
  satisfiesTnum64 x t.value t.mask

-- === END: PREDICATES ===

-- === BEGIN: SPEC (provided) ===

/-- The concrete operation. -/
def concreteMul (a b : BitVec 64) : BitVec 64 :=
  a * b

/-- Compute the optimal tnum for Tnum Multiplication. -/
def tnumMul (a b : Tnum) : Tnum :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC_CORRECT (provided) ===

theorem tnumMul_correct (a b : Tnum)
    (ha : validTnum a) (hb : validTnum b) :
    let r := tnumMul a b
    -- Well-formedness: result is a valid tnum
    validTnum r ∧
    -- Soundness: every concrete result satisfies r
    (∀ x y, inTnumGamma a x → inTnumGamma b y →
      inTnumGamma r (concreteMul x y)) ∧
    -- Optimality: r is the ⊑-least sound abstraction
    (∀ r' : Tnum, validTnum r' →
      (∀ x y, inTnumGamma a x → inTnumGamma b y →
        inTnumGamma r' (concreteMul x y)) →
      (∀ z, inTnumGamma r z → inTnumGamma r' z)) := by
-- === END: SPEC_CORRECT ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end BPF
