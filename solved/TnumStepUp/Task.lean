/-
  BPF tnum helper verification task: Find smallest value above z satisfying a tnum
  Operator: TNUM_STEP_UP
-/
import Mathlib.Tactic

namespace BPF

-- === BEGIN: DEFINITIONS (provided) ===

/-- A value `x` satisfies a 64-bit tnum constraint. -/
def satisfiesTnum64 (x tval tmask : BitVec 64) : Prop :=
  (x &&& ~~~tmask) = tval

/-- Find smallest value above z satisfying a tnum -/
def tnumStepUp (tval tmask z : BitVec 64) : BitVec 64 :=
-- === END: DEFINITIONS ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  let d := z - tval
  let carry := d &&& ~~~tmask
  let carry := carry ||| (carry >>> 1)
  let carry := carry ||| (carry >>> 2)
  let carry := carry ||| (carry >>> 4)
  let carry := carry ||| (carry >>> 8)
  let carry := carry ||| (carry >>> 16)
  let carry := carry ||| (carry >>> 32)
  let inc := ((d ||| carry ||| ~~~tmask) + 1) &&& tmask
  tval ||| inc
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC (provided) ===

theorem tnumStepUp_correct (tval tmask z : BitVec 64)
    (h_consistent : (tval &&& tmask) = 0)
    (h_lo : tval ≤ z)
    (h_hi : z < (tval ||| tmask)) :
    let r := tnumStepUp tval tmask z
    satisfiesTnum64 r tval tmask ∧
    tval ≤ r ∧ r ≤ (tval ||| tmask) ∧
    z < r ∧
    ∀ w, satisfiesTnum64 w tval tmask → z < w → r ≤ w := by
-- === END: SPEC ===
-- === BEGIN: PROOF (editable) ===
  unfold tnumStepUp satisfiesTnum64
  simp only []
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · bv_decide
  · bv_decide
  · bv_decide
  · bv_decide
  · intro w hw1 hw2; bv_decide
-- === END: PROOF ===

end BPF
