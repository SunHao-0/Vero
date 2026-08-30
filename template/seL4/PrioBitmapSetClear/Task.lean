/-
  seL4 Optimization Task: Two-level priority bitmap state machine
  Source: src/object/tcb.c (addToBitmap, removeFromBitmap); include/kernel/thread.h (getHighestPrio)

  seL4's scheduler maintains a two-level bitmap:
    L1 : 8 bits (one bit per group of 32 priorities)
    L2 : 8 × 32-bit words (one bit per priority)
  with the invariant that L1 bit `i` is set iff L2 word `i` is non-zero.

  Naive: linear scan each query.
  Optimized: O(1) `set / clear / highest` via bit manipulation, but
             you must keep the L1 ↔ L2 invariant in lockstep across
             every operation, AND the algebraic laws between operations
             must hold.

  this task is a four-function STATE MACHINE. The model must
  implement `setBit`, `clearBit`, `contains`, and `highest`, and prove
  ~12 algebraic / invariant clauses tying them together. Single-function
  shortcuts cannot satisfy the cross-function laws.
-/
import Mathlib
import Std

namespace seL4.PrioBitmapSetClear

-- === BEGIN: DEFINITIONS (provided) ===

abbrev Prio := Fin 256

structure BitmapState where
  l1 : BitVec 8
  l2 : Fin 8 → BitVec 32

/-- Logical group index for a priority (top 3 bits). -/
def Prio.group (p : Prio) : Fin 8 :=
  ⟨p.val / 32, by omega⟩

/-- Logical bit index within the L2 word (low 5 bits). -/
def Prio.bit (p : Prio) : Fin 32 :=
  ⟨p.val % 32, by omega⟩

/-- Reconstruct a priority from a (group, bit) pair. -/
def Prio.ofParts (g : Fin 8) (b : Fin 32) : Prio :=
  ⟨g.val * 32 + b.val, by omega⟩

/-- The empty bitmap. -/
def BitmapState.empty : BitmapState :=
  ⟨0, fun _ => 0⟩

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

/-- The L1 ↔ L2 consistency invariant: L1 bit `i` is set iff the
    corresponding L2 word is non-zero. This must be maintained by
    `setBit` and `clearBit`. -/
def consistent (s : BitmapState) : Prop :=
  ∀ i : Fin 8, s.l1.getLsbD i.val = true ↔ s.l2 i ≠ 0

/-- Inductive characterization of which priorities are present. -/
inductive Holds : BitmapState → Prio → Prop where
  | mk (s : BitmapState) (p : Prio)
       (h_l2 : (s.l2 p.group).getLsbD p.bit.val = true)
       (h_l1 : s.l1.getLsbD p.group.val = true) :
       Holds s p

-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No axioms.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

/-- Set priority `p` in the bitmap, maintaining the L1 ↔ L2 invariant. -/
def setBit (s : BitmapState) (p : Prio) : BitmapState :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable, setBit) ===
  sorry
-- === END: IMPLEMENTATION (setBit) ===

-- === BEGIN: SPEC (provided, clearBit) ===
/-- Clear priority `p`, maintaining the L1 ↔ L2 invariant. -/
def clearBit (s : BitmapState) (p : Prio) : BitmapState :=
-- === END: SPEC (clearBit) ===
-- === BEGIN: IMPLEMENTATION (editable, clearBit) ===
  sorry
-- === END: IMPLEMENTATION (clearBit) ===

-- === BEGIN: SPEC (provided, contains) ===
/-- Test whether priority `p` is present. -/
def contains (s : BitmapState) (p : Prio) : Bool :=
-- === END: SPEC (contains) ===
-- === BEGIN: IMPLEMENTATION (editable, contains) ===
  sorry
-- === END: IMPLEMENTATION (contains) ===

-- === BEGIN: SPEC (provided, highest) ===
/-- O(1) highest-priority lookup using L1 + L2 CLZ. -/
def highest (s : BitmapState) : Option Prio :=
-- === END: SPEC (highest) ===
-- === BEGIN: IMPLEMENTATION (editable, highest) ===
  sorry
-- === END: IMPLEMENTATION (highest) ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem bitmap_state_machine_correct :
    -- (1) `empty` is consistent and `contains` is everywhere false.
    consistent BitmapState.empty ∧
    (∀ p : Prio, contains BitmapState.empty p = false) ∧
    -- (2) `setBit` preserves consistency.
    (∀ s p, consistent s → consistent (setBit s p)) ∧
    -- (3) `clearBit` preserves consistency.
    (∀ s p, consistent s → consistent (clearBit s p)) ∧
    -- (4) `setBit` adds exactly one priority: `contains (setBit s p) q`
    --     iff `q = p` or `contains s q`.
    (∀ s p q, consistent s →
      contains (setBit s p) q = (q = p ∨ contains s q = true)) ∧
    -- (5) `clearBit` removes exactly one priority.
    (∀ s p q, consistent s →
      contains (clearBit s p) q = (q ≠ p ∧ contains s q = true)) ∧
    -- (6) `Holds` agrees with `contains` under consistency.
    (∀ s p, consistent s → (Holds s p ↔ contains s p = true)) ∧
    -- (7) ALGEBRAIC LAW: `setBit ∘ setBit p = setBit p` (idempotence).
    (∀ s p, consistent s → setBit (setBit s p) p = setBit s p) ∧
    -- (8) ALGEBRAIC LAW: `clearBit ∘ clearBit p = clearBit p`.
    (∀ s p, consistent s → clearBit (clearBit s p) p = clearBit s p) ∧
    -- (9) ALGEBRAIC LAW: setting then clearing the same bit equals
    --     just clearing (regardless of whether `p` was originally set).
    (∀ s p, consistent s → clearBit (setBit s p) p = clearBit s p) ∧
    -- (9') ALGEBRAIC LAW: clearing then setting the same bit equals
    --      just setting.
    (∀ s p, consistent s → setBit (clearBit s p) p = setBit s p) ∧
    -- (10) ALGEBRAIC LAW: distinct `setBit`s commute.
    (∀ s p q, consistent s → p ≠ q →
      setBit (setBit s p) q = setBit (setBit s q) p) ∧
    -- (11) ALGEBRAIC LAW: distinct `clearBit`s commute.
    (∀ s p q, consistent s → p ≠ q →
      clearBit (clearBit s p) q = clearBit (clearBit s q) p) ∧
    -- (12) ALGEBRAIC LAW: `setBit p` and `clearBit q` commute when `p ≠ q`.
    (∀ s p q, consistent s → p ≠ q →
      clearBit (setBit s p) q = setBit (clearBit s q) p) ∧
    -- (13) `highest` is `none` iff `contains` is everywhere false.
    (∀ s, consistent s →
      (highest s = none ↔ ∀ p, contains s p = false)) ∧
    -- (14) When `highest s = some p`, `contains s p` is true and every
    --      `q > p` has `contains s q = false`.
    (∀ s p, consistent s → highest s = some p →
      contains s p = true ∧
      ∀ q : Prio, q.val > p.val → contains s q = false) ∧
    -- (15) `highest` is uniquely determined: any `p` satisfying clause
    --      (14)'s body equals `highest s`.
    (∀ s p, consistent s →
      contains s p = true →
      (∀ q : Prio, q.val > p.val → contains s q = false) →
      highest s = some p) ∧
    -- (16) Inserting then querying highest: `highest (setBit s p)` is at
    --      least as high as `p` (in priority order).
    (∀ s p, consistent s →
      ∃ p', highest (setBit s p) = some p' ∧ p.val ≤ p'.val) ∧
    -- (17) Removing the current highest moves the highest strictly down
    --      (or to none).
    (∀ s p, consistent s → highest s = some p →
      ∀ q, highest (clearBit s p) = some q → q.val < p.val) ∧
    -- (18) Composition: starting from `empty`, the order of `setBit`s
    --      doesn't affect the final state up to consistency.
    (∀ ps : List Prio, ps.Nodup →
      ∀ qs : List Prio, qs.Perm ps →
      ps.foldl setBit BitmapState.empty =
        qs.foldl setBit BitmapState.empty) ∧
    -- (19) One-way restatement of emptiness characterization.
    (∀ s, consistent s → (∀ p, contains s p = false) → highest s = none) := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4.PrioBitmapSetClear
