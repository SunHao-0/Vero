/-
  seL4 Haskell Spec Optimization: allocRegion
  Source: SEL4/Kernel/Init.lhs:93-122

  Kernel-init memory allocator: scan the free-region list for a place
  to carve out an aligned block of size 2^bits. A region whose base is
  already aligned (pass 1, no alignment waste) is preferred over one
  that is merely usable after aligning the base up (pass 2).
-/
import Mathlib

namespace seL4.AllocRegion

-- === BEGIN: DEFINITIONS (provided) ===

/-- A free memory region [base, base + size). -/
structure MemRegion where
  base : Nat
  size : Nat
  h_pos : size > 0


/-- Free memory is a list of non-overlapping regions. -/
abbrev FreeMemory := List MemRegion

/-- Alignment: round up addr to next 2^bits boundary. -/
def alignUp (addr bits : Nat) : Nat :=
  let mask := 2^bits - 1
  (addr + mask) / (2^bits) * (2^bits)

/-- Preferred predicate (pass 1): base is already aligned and region is large enough.
    No alignment waste — allocation can start directly at base. -/
def isAlignedUsable (r : MemRegion) (bits : Nat) : Bool :=
  decide (r.base % 2^bits = 0) && decide (r.size ≥ 2^bits)

/-- Fallback predicate (pass 2): after aligning base up, allocation still fits. -/
def isUsable (r : MemRegion) (bits : Nat) : Bool :=
  decide (alignUp r.base bits + 2^bits ≤ r.base + r.size)

-- === END: DEFINITIONS ===

-- === BEGIN: SPEC (provided) ===

/-- Optimized allocRegion. -/
def allocOptimized (freeMem : FreeMemory) (bits : Nat) : Option Nat :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem alloc_spec (freeMem : FreeMemory) (bits : Nat) :
    -- (1) If an isAlignedUsable region exists, return alignUp of the first one
    (∀ r pre suf, freeMem = pre ++ r :: suf →
      isAlignedUsable r bits = true →
      (∀ r' ∈ pre, isAlignedUsable r' bits = false) →
      allocOptimized freeMem bits = some (alignUp r.base bits)) ∧
    -- (2) If no isAlignedUsable but an isUsable region exists,
    --     return alignUp of the first isUsable
    (∀ r pre suf, freeMem = pre ++ r :: suf →
      (∀ r' ∈ freeMem, isAlignedUsable r' bits = false) →
      isUsable r bits = true →
      (∀ r' ∈ pre, isUsable r' bits = false) →
      allocOptimized freeMem bits = some (alignUp r.base bits)) ∧
    -- (3) If no isUsable region exists, return none
    ((∀ r ∈ freeMem, isUsable r bits = false) →
      allocOptimized freeMem bits = none) := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4.AllocRegion
