/-
  seL4 Optimization Task: Scheduling Context Refill Merge
  Original: O(n) repeated single-entry refills
  Optimized: O(n) single-pass merge of adjacent refills

  In MCS scheduling, each scheduling context maintains a list of
  "refill" entries — (time, amount) pairs representing when budget
  becomes available. When entries are adjacent or overlapping in time,
  they can be merged to reduce list length. Prove the merge preserves
  total budget and time coverage while eliminating all overlaps.

  Source: seL4/src/kernel/sporadic.c (refill_budget_check, refill_unblock_check)
-/
import Mathlib
import Std

namespace seL4.RefillMerge

-- === BEGIN: DEFINITIONS (provided) ===



/-- Custom sequence type (no Mathlib automation). -/
inductive Seq (α : Type) where
  | nil : Seq α
  | cons : α → Seq α → Seq α
  deriving Repr


def Seq.mem {α : Type} (a : α) : Seq α → Prop
  | .nil => False
  | .cons x xs => a = x ∨ Seq.mem a xs


def Seq.length {α : Type} : Seq α → Nat
  | .nil => 0
  | .cons _ xs => xs.length + 1

def Seq.foldl {α : Type} {β : Type} (f : β → α → β) (init : β) : Seq α → β
  | .nil => init
  | .cons x xs => Seq.foldl f (f init x) xs

def Seq.Pairwise {α : Type} (R : α → α → Prop) : Seq α → Prop
  | .nil => True
  | .cons x xs => (∀ y, Seq.mem y xs → R x y) ∧ Seq.Pairwise R xs

/-- Get element at index (partial, with proof). -/
def Seq.get {α : Type} : (s : Seq α) → (i : Nat) → i < s.length → α
  | .cons x _, 0, _ => x
  | .cons _ xs, n + 1, h => Seq.get xs n (by simp [length] at h; omega)

instance {α : Type} : Membership α (Seq α) where
  mem s a := @Seq.mem α a s




/-- A refill entry: budget of `amount` ticks available starting at `time`. -/
structure Refill where
  time : Nat
  amount : Nat
  h_pos : amount > 0
  deriving Repr

/-- Refill list: sorted by time, representing budget availability windows. -/
abbrev RefillList := Seq Refill

/-- Total budget across all refill entries. -/
def totalBudget (rs : RefillList) : Nat :=
  rs.foldl (fun acc r => acc + r.amount) 0

/-- A time tick is covered by a refill entry. -/
def Refill.covers (r : Refill) (t : Nat) : Prop :=
  r.time ≤ t ∧ t < r.time + r.amount

/-- A time tick is covered by some entry in the refill list. -/
def coveredBy (rs : RefillList) (t : Nat) : Prop :=
  ∃ r, r ∈ rs ∧ r.covers t

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

/-- Refills are sorted by start time (ascending, non-overlapping). -/
def timeSorted (rs : RefillList) : Prop :=
  rs.Pairwise (fun a b => a.time + a.amount ≤ b.time)

/-- Two refills are adjacent or overlapping. -/
def adjacent (r1 r2 : Refill) : Prop :=
  r1.time + r1.amount ≥ r2.time

/-- A refill list is fully merged: no two consecutive entries are adjacent. -/
def fullyMerged (rs : RefillList) : Prop :=
  ∀ i, (h1 : i < rs.length) → (h2 : i + 1 < rs.length) →
    ¬ adjacent (rs.get i h1) (rs.get (i + 1) h2)

-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No additional axioms.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

/-- Merge adjacent/overlapping refill entries in a sorted list.
    Returns a new sorted list with no adjacent entries and the
    same total budget and time coverage. -/
def mergeRefills (rs : RefillList) : RefillList :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem mergeRefills_correct (rs : RefillList) (h_sorted : timeSorted rs) :
    let result := mergeRefills rs
    -- Total budget is preserved
    totalBudget result = totalBudget rs ∧
    -- Result is sorted
    timeSorted result ∧
    -- Result is fully merged (no adjacent entries)
    fullyMerged result ∧
    -- Result is no longer than input
    result.length ≤ rs.length ∧
    -- Time coverage equivalence: same set of ticks covered
    (∀ t : Nat, coveredBy result t ↔ coveredBy rs t) ∧
    -- All entries in result have positive amount
    (∀ r, r ∈ result → r.amount > 0) ∧
    -- Idempotence: merging an already-merged list is the identity
    mergeRefills result = result ∧
    -- Determinism: any list satisfying budget + sorted + merged + coverage
    -- must equal the result
    (∀ rs' : RefillList,
      totalBudget rs' = totalBudget rs →
      timeSorted rs' →
      fullyMerged rs' →
      (∀ t : Nat, coveredBy rs' t ↔ coveredBy rs t) →
      (∀ r, r ∈ rs' → r.amount > 0) →
      rs' = result) ∧
    -- Minimality: any schedule with equivalent behavior has at least as many
    -- refill segments as the optimized result.
    (∀ rs' : RefillList,
      timeSorted rs' →
      fullyMerged rs' →
      totalBudget rs' = totalBudget rs →
      (∀ t : Nat, coveredBy rs' t ↔ coveredBy rs t) →
      (∀ r, r ∈ rs' → r.amount > 0) →
      result.length ≤ rs'.length) ∧
    -- Prefix-stability: the first covered tick (if any) is preserved.
    (∀ t0 : Nat,
      coveredBy rs t0 →
      (∀ t, t < t0 → ¬ coveredBy rs t) →
      coveredBy result t0 ∧
      (∀ t, t < t0 → ¬ coveredBy result t)) := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4.RefillMerge
