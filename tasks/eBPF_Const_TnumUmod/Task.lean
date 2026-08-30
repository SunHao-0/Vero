/-
  BPF tnum verification task: Tnum Unsigned Modulo by Constant
  Operator: TNUM_UMOD
  Source: Linux eBPF verifier tnum analysis, kernel/bpf/tnum.c

  Compute the optimal tnum for the result of
  unsigned 64-bit modulo of a tnum by a non-zero constant where the second operand is a non-zero constant.
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

/-- The concrete operation with a non-zero constant. -/
def concreteUmod (a c : BitVec 64) : BitVec 64 :=
  a % c

/-- Compute the optimal tnum for Tnum Unsigned Modulo by Constant. -/
def tnumUmod (a : Tnum) (c : BitVec 64) : Tnum :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC_CORRECT (provided) ===

theorem tnumUmod_correct (a : Tnum) (c : BitVec 64)
    (ha : validTnum a) (hc : c ≠ 0) :
    let r := tnumUmod a c
    -- Well-formedness: result is a valid tnum
    validTnum r ∧
    -- Soundness: every concrete result satisfies r
    (∀ x, inTnumGamma a x →
      inTnumGamma r (concreteUmod x c)) ∧
    -- Optimality: r is the ⊑-least sound abstraction
    (∀ r' : Tnum, validTnum r' →
      (∀ x, inTnumGamma a x →
        inTnumGamma r' (concreteUmod x c)) →
      (∀ z, inTnumGamma r z → inTnumGamma r' z)) := by
-- === END: SPEC_CORRECT ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end BPF
