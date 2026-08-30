/-
  seL4 Optimization Task: tcbReleaseEnqueue — BST-based Sorted Insertion
  Source: src/object/tcb.c (tcbReleaseEnqueue, MCS release queue)

  In MCS scheduling, tcbReleaseEnqueue inserts a thread into a
  time-ordered release queue. The queue is stored as a BST keyed by
  release time.

  Release queue stored as BST. The solver must implement
  BST insert and prove ordering invariant preservation.
-/
import Mathlib
import Std

namespace seL4.ReleaseEnqueue

-- === BEGIN: DEFINITIONS (provided) ===

/-- Release time is a 64-bit tick count. -/
abbrev Ticks := Nat

/-- A thread entry in the release queue. -/
structure ReleaseEntry where
  threadId : Nat
  releaseTime : Ticks
  deriving DecidableEq, Repr

/-- BST of release entries, ordered by releaseTime. -/
inductive ReleaseBST where
  | leaf : ReleaseBST
  | node : ReleaseBST → ReleaseEntry → ReleaseBST → ReleaseBST
  deriving Repr

def ReleaseBST.mem (e : ReleaseEntry) : ReleaseBST → Prop
  | .leaf => False
  | .node l x r => e = x ∨ ReleaseBST.mem e l ∨ ReleaseBST.mem e r

instance : Membership ReleaseEntry ReleaseBST where
  mem t e := ReleaseBST.mem e t

def ReleaseBST.All (p : ReleaseEntry → Prop) : ReleaseBST → Prop
  | .leaf => True
  | .node l x r => p x ∧ ReleaseBST.All p l ∧ ReleaseBST.All p r

/-- BST ordering by releaseTime. -/
def ReleaseBST.Ordered : ReleaseBST → Prop
  | .leaf => True
  | .node l x r =>
    ReleaseBST.All (fun e => e.releaseTime < x.releaseTime) l ∧
    ReleaseBST.All (fun e => x.releaseTime < e.releaseTime) r ∧
    ReleaseBST.Ordered l ∧ ReleaseBST.Ordered r

def ReleaseBST.NoDup : ReleaseBST → Prop
  | .leaf => True
  | .node l x r =>
    x ∉ l ∧ x ∉ r ∧
    ReleaseBST.NoDup l ∧ ReleaseBST.NoDup r

def ReleaseBST.size : ReleaseBST → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

def ReleaseBST.height : ReleaseBST → Nat
  | .leaf => 0
  | .node l _ r => Nat.succ (Nat.max l.height r.height)

def ReleaseBST.Balanced : ReleaseBST → Prop
  | .leaf => True
  | .node l _ r =>
    ReleaseBST.Balanced l ∧ ReleaseBST.Balanced r ∧
    l.height ≤ r.height + 1 ∧ r.height ≤ l.height + 1

def ReleaseBST.memTid (tid : Nat) : ReleaseBST → Prop
  | .leaf => False
  | .node l x r => tid = x.threadId ∨ ReleaseBST.memTid tid l ∨ ReleaseBST.memTid tid r


/-- Kernel monad. -/
structure KM (σ α : Type) where
  run : σ → Option (α × σ)

def KM.ret {σ α : Type} (a : α) : KM σ α := ⟨fun s => some (a, s)⟩
def KM.bind {σ α β : Type} (ma : KM σ α) (f : α → KM σ β) : KM σ β :=
  ⟨fun s => match ma.run s with
    | none => none
    | some (a, s') => (f a).run s'⟩
def KM.get {σ : Type} : KM σ σ := ⟨fun s => some (s, s)⟩
def KM.set {σ : Type} (s : σ) : KM σ Unit := ⟨fun _ => some ((), s)⟩
def KM.fail {σ α : Type} : KM σ α := ⟨fun _ => none⟩


/-- Kernel state for release queue. -/
structure EnqueueState where
  queue : ReleaseBST

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===
-- No additional predicates.
-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No axioms.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

/-- Insert an entry into the release BST via the kernel monad. -/
def sortedInsertM (entry : ReleaseEntry) : KM EnqueueState Unit :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem sortedInsertM_correct (es : EnqueueState) (entry : ReleaseEntry)
    (h_ordered : es.queue.Ordered)
    (h_nodup : es.queue.NoDup)
    (h_fresh : ¬ es.queue.memTid entry.threadId)
    -- Strict BST ordering on releaseTime requires the inserted entry's
    -- releaseTime to be distinct from every existing entry; otherwise
    -- property (1) is unprovable since two entries with the same
    -- releaseTime cannot coexist in a strictly-ordered BST.
    (h_fresh_time : ∀ e, e ∈ es.queue → e.releaseTime ≠ entry.releaseTime) :
    -- Non-failure.
    (∃ es', (sortedInsertM entry).run es = some ((), es')) ∧
    -- Correctness.
    (∀ es', (sortedInsertM entry).run es = some ((), es') →
      let q := es.queue
      let out := es'.queue
      -- (1) BST ordering preserved.
      out.Ordered ∧
      -- (2) No duplicates preserved.
      out.NoDup ∧
      -- (3) Anti-degeneration: output BST is balanced.
      out.Balanced ∧
      -- (4) Log-height bound for output BST.
      (out.height ≤ Nat.log2 (out.size + 1) + 1) ∧
      -- (5) The entry is in the result.
      entry ∈ out ∧
      -- (6) All previous entries preserved.
      (∀ e, e ∈ q → e ∈ out) ∧
      -- (7) Only the new entry was added.
      (∀ e, e ∈ out → e = entry ∨ e ∈ q) ∧
      -- (8) Size grows by one.
      out.size = q.size + 1 ∧
      -- (9) Entries with smaller releaseTime are in the left subtree
      --     structure of the BST (relational ordering property).
      (∀ e, e ∈ out → e.releaseTime < entry.releaseTime → e ∈ q) ∧
      -- (10) Entries with larger releaseTime are in the right subtree
      --     structure of the BST (relational ordering property).
      (∀ e, e ∈ out → entry.releaseTime < e.releaseTime → e ∈ q) ∧
      -- (11) Determinism.
      (∀ es'', (sortedInsertM entry).run es = some ((), es'') → es'' = es') ∧
      -- (12) Bind-consistency: inserting two entries preserves ordering.
      (∀ entry2 : ReleaseEntry,
        ¬ out.memTid entry2.threadId →
        entry2.releaseTime ≠ entry.releaseTime →
        ∀ es'', (KM.bind (sortedInsertM entry) (fun _ => sortedInsertM entry2)).run es = some ((), es'') →
          es''.queue.Ordered) ∧
      -- (13) Output queue is non-empty after successful insertion.
      out ≠ .leaf) := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4.ReleaseEnqueue
