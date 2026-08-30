/-
  BPF tnum helper verification task: Find smallest value above z satisfying a tnum
  Source: Linux eBPF verifier tnum analysis, kernel/bpf/tnum.c; merged in bpf-next commit 833ef4a954e1
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
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC (provided) ===

theorem tnumStepUp_correct (tval tmask z : BitVec 64)
    (h_consistent : (tval &&& tmask) = 0)
    (h_lo : tval ≤ z)
    (h_hi : z < (tval ||| tmask)) :
    -- result is within tnum range
    tval ≤ tnumStepUp tval tmask z ∧
    tnumStepUp tval tmask z ≤ (tval ||| tmask) ∧
    -- result satisfies the tnum
    satisfiesTnum64 (tnumStepUp tval tmask z) tval tmask ∧
    -- result is strictly above z
    z < tnumStepUp tval tmask z ∧
    -- result is optimal (smallest value above z)
    (∀ (w : BitVec 64), satisfiesTnum64 w tval tmask → z < w → tnumStepUp tval tmask z ≤ w) := by
-- === END: SPEC ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end BPF
