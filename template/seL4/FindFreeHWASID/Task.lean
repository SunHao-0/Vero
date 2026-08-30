/-
  seL4 Optimization Task: findFreeHWASID — Segment Tree variant
  Original: O(256) linear scan through armKSHWASIDTable
  Optimized: O(log 256) segment tree query

  The bitmap is replaced by a segment tree. Each node
  tracks the count of free slots. The solver must implement segment
  tree query for the LAST (highest-indexed) free slot and prove
  segment tree invariant maintenance.

  Source: seL4/src/arch/arm/kernel/vspace.c
-/
import Mathlib
import Std

namespace seL4.FindFreeHWASID

-- === BEGIN: DEFINITIONS (provided) ===

abbrev HwAsid := Fin 256
abbrev AsidEntry := Option (Fin (2^17))
abbrev AsidTable := Fin 256 → AsidEntry

/-- Segment tree over ASID range.
    - `leaf b` represents a single ASID: `b = true` means free.
    - `node l r freeCount rangeSize` -/
inductive SegTree where
  | leaf : Bool → SegTree
  | node : SegTree → SegTree → Nat → Nat → SegTree
  deriving Repr

def SegTree.freeCount : SegTree → Nat
  | .leaf b => if b then 1 else 0
  | .node _ _ fc _ => fc

def SegTree.rangeSize : SegTree → Nat
  | .leaf _ => 1
  | .node _ _ _ rs => rs

def SegTree.WellFormed : SegTree → Prop
  | .leaf _ => True
  | .node l r fc rs =>
    l.WellFormed ∧ r.WellFormed ∧
    fc = l.freeCount + r.freeCount ∧
    rs = l.rangeSize + r.rangeSize ∧
    l.rangeSize > 0 ∧ r.rangeSize > 0

def SegTree.getBit : SegTree → Nat → Bool
  | .leaf b, _ => b
  | .node l r _ _, i =>
    if i < l.rangeSize then l.getBit i
    else r.getBit (i - l.rangeSize)

/-- Segment tree consistent with ASID table: bit i is true iff ASID i is free. -/
def segConsistent (table : AsidTable) (seg : SegTree) : Prop :=
  seg.rangeSize = 256 ∧
  ∀ i : Fin 256, seg.getBit i.val = true ↔ (table i).isNone

/-- Last free slot: free and all higher-indexed slots are allocated. -/
def isLastFree (table : AsidTable) (asid : HwAsid) : Prop :=
  (table asid).isNone ∧
  ∀ (j : Fin 256), j.val > asid.val → (table j).isSome

/-- All slots are allocated. -/
def allAllocated (table : AsidTable) : Prop :=
  ∀ (j : Fin 256), (table j).isSome

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===
-- No additional predicates.
-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No axioms.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

/-- Segment-tree-based free ASID lookup: find the highest-indexed free slot
    by traversing the segment tree rightward. -/
def segTreeScanLast (seg : SegTree) : Option Nat :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem segTreeScanLast_correct (table : AsidTable) (seg : SegTree)
    (h_wf : seg.WellFormed)
    (h_consistent : segConsistent table seg) :
    let out := segTreeScanLast seg
    -- (1) If result returned, it is the last free slot.
    (∀ idx, out = some idx →
      ∃ h : idx < 256, isLastFree table ⟨idx, h⟩) ∧
    -- (2) Returns none iff all allocated.
    (out = none ↔ allAllocated table) ∧
    -- (3) Returns none iff freeCount = 0.
    (out = none ↔ seg.freeCount = 0) ∧
    -- (4) Completeness.
    ((∃ j : Fin 256, (table j).isNone) → ∃ idx, out = some idx) ∧
    -- (5) Uniqueness.
    (∀ asid : HwAsid, isLastFree table asid → out = some asid.val) ∧
    -- (6) The result is the rightmost true-bit in the tree.
    (∀ idx, out = some idx →
      seg.getBit idx = true ∧
      ∀ j, j > idx → j < seg.rangeSize → seg.getBit j = false) ∧
    -- (7) Bounds.
    (∀ idx, out = some idx → idx < seg.rangeSize) ∧
    -- (8) Monotonicity: allocating a slot (so `seg'` has a subset of free
    --     bits relative to `seg`) cannot make a higher free slot appear.
    (∀ seg' : SegTree, seg'.WellFormed → seg'.rangeSize = 256 →
      (∀ i, i < 256 → seg'.getBit i = true → seg.getBit i = true) →
      ∀ idx idx', out = some idx → segTreeScanLast seg' = some idx' →
        idx' ≤ idx) ∧
    -- (9) Empty tree: all bits free means result is 255.
    ((∀ i, i < 256 → seg.getBit i = true) →
      out = some 255) ∧
    -- (10) Option exclusivity.
    (out = none → ¬ ∃ idx, out = some idx) := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4.FindFreeHWASID
