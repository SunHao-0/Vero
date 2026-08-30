/-
  LLVM KnownBits verification task: Unsigned Maximum
  Operator: @llvm.umax

  Compute the optimal KnownBits for the result of
  unsigned 64-bit maximum on two KnownBits.
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
def concreteUmax (x y : BitVec 64) : BitVec 64 :=
  if x.toNat ≥ y.toNat then x else y

/-- Compute the optimal KnownBits for Unsigned Maximum. -/
def kbUmax (a b : KnownBits) : KnownBits :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  let minA := a.one
  let maxA := ~~~a.zero
  let minB := b.one
  let maxB := ~~~b.zero
  if maxB.toNat ≤ minA.toNat then a
  else if maxA.toNat < minB.toNat then b
  else
    let rz := a.zero &&& b.zero
    let ro :=
      if minB.toNat ≤ minA.toNat then
        let d := maxB - minA
        let v := d - 1
        let v := v ||| (v >>> 1)
        let v := v ||| (v >>> 2)
        let v := v ||| (v >>> 4)
        let v := v ||| (v >>> 8)
        let v := v ||| (v >>> 16)
        let v := v ||| (v >>> 32)
        minA &&& (minB ||| (~~~(b.zero ||| b.one) &&& ~~~v))
      else
        let e := maxA - minB
        let v := e ||| (e >>> 1)
        let v := v ||| (v >>> 2)
        let v := v ||| (v >>> 4)
        let v := v ||| (v >>> 8)
        let v := v ||| (v >>> 16)
        let v := v ||| (v >>> 32)
        (minA ||| (~~~(a.zero ||| a.one) &&& ~~~v)) &&& minB
    ⟨rz, ro⟩

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC_CORRECT (provided) ===

theorem kbUmax_correct (a b : KnownBits)
    (ha : validKB a) (hb : validKB b) :
    let r := kbUmax a b
    -- Well-formedness: result is a valid KnownBits
    validKB r ∧
    -- Soundness: every concrete result is in the concretization
    (∀ x y, inKBGamma a x → inKBGamma b y →
      inKBGamma r (concreteUmax x y)) ∧
    -- Optimality: r is the ⊑-least sound abstraction
    (∀ r' : KnownBits, validKB r' →
      (∀ x y, inKBGamma a x → inKBGamma b y →
        inKBGamma r' (concreteUmax x y)) →
      (∀ z, inKBGamma r z → inKBGamma r' z)) := by
-- === END: SPEC_CORRECT ===
-- === BEGIN: PROOF (editable) ===
  simp only [validKB] at ha hb
  simp only [kbUmax]
  split
  · -- Case 1: maxB ≤ minA, result = a
    rename_i h1
    have h1' : ~~~b.zero ≤ a.one := BitVec.le_def.mpr h1
    simp only [validKB, inKBGamma, concreteUmax]
    refine ⟨ha, ?_, ?_⟩
    · -- Soundness
      intro x y ⟨hxz, hxo⟩ ⟨hyz, hyo⟩
      split
      · exact ⟨hxz, hxo⟩
      · rename_i hlt
        push_neg at hlt
        exfalso
        have : ¬(x ≥ y) := by intro h; exact absurd (BitVec.le_def.mp h) (by omega)
        bv_decide
    · -- Optimality
      intro r' hr' hsound' z ⟨hzz, hzo⟩
      have hbz : b.one &&& b.zero = 0 := by bv_decide
      have hbo : b.one &&& b.one = b.one := by bv_decide
      have := hsound' z b.one ⟨hzz, hzo⟩ ⟨hbz, hbo⟩
      simp only [] at this
      split at this
      · exact this
      · rename_i hlt
        push_neg at hlt
        exfalso
        have : ¬(z ≥ b.one) := by intro h; exact absurd (BitVec.le_def.mp h) (by omega)
        bv_decide
  · split
    · -- Case 2: maxA < minB, result = b
      rename_i h1 h2
      push_neg at h1
      have h1' : ¬(~~~b.zero ≤ a.one) := by
        intro h; exact absurd (BitVec.le_def.mp h) (by omega)
      have h2' : ~~~a.zero < b.one := BitVec.lt_def.mpr h2
      simp only [validKB, inKBGamma, concreteUmax]
      refine ⟨hb, ?_, ?_⟩
      · -- Soundness
        intro x y ⟨hxz, hxo⟩ ⟨hyz, hyo⟩
        split
        · rename_i hge
          exfalso
          have : x ≥ y := BitVec.le_def.mpr (by omega)
          bv_decide
        · exact ⟨hyz, hyo⟩
      · -- Optimality
        intro r' hr' hsound' z ⟨hzz, hzo⟩
        have haz : a.one &&& a.zero = 0 := by bv_decide
        have hao : a.one &&& a.one = a.one := by bv_decide
        have := hsound' a.one z ⟨haz, hao⟩ ⟨hzz, hzo⟩
        simp only [] at this
        split at this
        · rename_i hge
          exfalso
          have : a.one ≥ z := BitVec.le_def.mpr (by omega)
          bv_decide
        · exact this
    · -- Case 3: overlap
      rename_i h1 h2
      push_neg at h1 h2
      have h1' : a.one < ~~~b.zero := BitVec.lt_def.mpr h1
      have h2' : b.one ≤ ~~~a.zero := BitVec.le_def.mpr h2
      simp only [validKB, inKBGamma, concreteUmax]
      refine ⟨?wf, ?sound, ?opt⟩
      case wf => split <;> bv_decide
      case sound =>
        intro x y ⟨hxz, hxo⟩ ⟨hyz, hyo⟩
        -- After split <;> split, we get 4 goals with various .toNat hypotheses
        -- Convert all .toNat hypotheses to BitVec comparisons, then bv_decide
        split <;> split <;> rename_i h_a h_b
        · -- x ≥ y, minB ≤ minA
          have := BitVec.le_def.mpr h_a -- x ≥ y
          have := BitVec.le_def.mpr h_b -- b.one ≤ a.one
          exact ⟨by bv_decide, by bv_decide⟩
        · -- x ≥ y, minA < minB
          have := BitVec.le_def.mpr h_a -- x ≥ y
          have : ¬(b.one ≤ a.one) := fun hc => absurd (BitVec.le_def.mp hc) (by omega)
          exact ⟨by bv_decide, by bv_decide⟩
        · -- x < y, minB ≤ minA
          have : x < y := BitVec.lt_def.mpr (by omega)
          have := BitVec.le_def.mpr h_b -- b.one ≤ a.one
          exact ⟨by bv_decide, by bv_decide⟩
        · -- x < y, minA < minB
          have : x < y := BitVec.lt_def.mpr (by omega)
          have : ¬(b.one ≤ a.one) := fun hc => absurd (BitVec.le_def.mp hc) (by omega)
          exact ⟨by bv_decide, by bv_decide⟩
      case opt =>
        intro r' hr' hsound' z ⟨hzz, hzo⟩
        -- Establish common witness membership facts
        have hw_xa : (~~~a.zero) &&& a.zero = 0 := by bv_decide
        have hw_xo : (~~~a.zero) &&& a.one = a.one := by bv_decide
        have hw_yz : b.one &&& b.zero = 0 := by bv_decide
        have hw_yo : b.one &&& b.one = b.one := by bv_decide
        have hw_az : a.one &&& a.zero = 0 := by bv_decide
        have hw_ao : a.one &&& a.one = a.one := by bv_decide
        have hw_bz : (~~~b.zero) &&& b.zero = 0 := by bv_decide
        have hw_bo : (~~~b.zero) &&& b.one = b.one := by bv_decide
        -- Witness 1: (~~~a.zero, b.one) → umax = ~~~a.zero (since ~~~a.zero ≥ b.one)
        have hw1 := hsound' (~~~a.zero) b.one ⟨hw_xa, hw_xo⟩ ⟨hw_yz, hw_yo⟩
        simp only [] at hw1
        rw [if_pos (BitVec.le_def.mp h2')] at hw1
        obtain ⟨hw1_z, hw1_o⟩ := hw1
        -- Witness 2: (a.one, ~~~b.zero) → umax = ~~~b.zero (since a.one < ~~~b.zero)
        have hw2 := hsound' a.one (~~~b.zero) ⟨hw_az, hw_ao⟩ ⟨hw_bz, hw_bo⟩
        simp only [] at hw2
        rw [if_neg (Nat.not_le.mpr (BitVec.lt_def.mp h1'))] at hw2
        obtain ⟨hw2_z, hw2_o⟩ := hw2
        -- Case split on the inner if condition (which appears in hzo)
        by_cases h_sub : b.one.toNat ≤ a.one.toNat
        · -- Subcase 1: minB ≤ minA
          rw [if_pos h_sub] at hzo
          -- Witness 3: (a.one, b.one) → umax = a.one (since b.one ≤ a.one)
          have hw3 := hsound' a.one b.one ⟨hw_az, hw_ao⟩ ⟨hw_yz, hw_yo⟩
          simp only [] at hw3
          rw [if_pos h_sub] at hw3
          obtain ⟨hw3_z, hw3_o⟩ := hw3
          -- Witness 4: (a.one, y_all) where y_all removes smear-range bits
          set unk_b := ~~~(b.zero ||| b.one) with unk_b_def
          set d := ~~~b.zero - a.one with d_def
          set v0 := d - 1 with v0_def
          set v1 := v0 ||| (v0 >>> 1) with v1_def
          set v2 := v1 ||| (v1 >>> 2) with v2_def
          set v3 := v2 ||| (v2 >>> 4) with v3_def
          set v4 := v3 ||| (v3 >>> 8) with v4_def
          set v5 := v4 ||| (v4 >>> 16) with v5_def
          set v := v5 ||| (v5 >>> 32) with v_def
          set y_all := (~~~b.zero) &&& ~~~(a.one &&& unk_b &&& v) with y_all_def
          have hy_bz : y_all &&& b.zero = 0 := by subst_eqs; bv_decide
          have hy_bo : y_all &&& b.one = b.one := by subst_eqs; bv_decide
          have hy_gt : y_all > a.one := by subst_eqs; bv_decide
          have hw4 := hsound' a.one y_all ⟨hw_az, hw_ao⟩ ⟨hy_bz, hy_bo⟩
          simp only [] at hw4
          rw [if_neg (Nat.not_le.mpr (BitVec.lt_def.mp hy_gt))] at hw4
          obtain ⟨hw4_z, hw4_o⟩ := hw4
          exact ⟨by bv_decide, by subst_eqs; bv_decide⟩
        · -- Subcase 2: minA < minB
          rw [if_neg h_sub] at hzo
          -- Witness 3: (a.one, b.one) → umax = b.one (since b.one > a.one)
          have hw3 := hsound' a.one b.one ⟨hw_az, hw_ao⟩ ⟨hw_yz, hw_yo⟩
          simp only [] at hw3
          rw [if_neg (by omega : ¬(a.one.toNat ≥ b.one.toNat))] at hw3
          obtain ⟨hw3_z, hw3_o⟩ := hw3
          -- Witness 4: (x_all, b.one) where x_all removes smear-range bits
          set unk_a := ~~~(a.zero ||| a.one) with unk_a_def
          set e := ~~~a.zero - b.one with e_def
          set v0 := e ||| (e >>> 1) with v0_def
          set v1 := v0 ||| (v0 >>> 2) with v1_def
          set v2 := v1 ||| (v1 >>> 4) with v2_def
          set v3 := v2 ||| (v2 >>> 8) with v3_def
          set v4 := v3 ||| (v3 >>> 16) with v4_def
          set v := v4 ||| (v4 >>> 32) with v_def
          set x_all := (~~~a.zero) &&& ~~~(b.one &&& unk_a &&& v) with x_all_def
          have hx_az : x_all &&& a.zero = 0 := by subst_eqs; bv_decide
          have hx_ao : x_all &&& a.one = a.one := by subst_eqs; bv_decide
          have hx_ge : x_all ≥ b.one := by subst_eqs; bv_decide
          have hw4 := hsound' x_all b.one ⟨hx_az, hx_ao⟩ ⟨hw_yz, hw_yo⟩
          simp only [] at hw4
          rw [if_pos (BitVec.le_def.mp hx_ge)] at hw4
          obtain ⟨hw4_z, hw4_o⟩ := hw4
          exact ⟨by bv_decide, by subst_eqs; bv_decide⟩
-- === END: PROOF ===

end LLVM
