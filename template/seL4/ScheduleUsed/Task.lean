/-
  seL4 Optimization Task: schedule_used / refill_budget_check budget merge
  Source: src/kernel/sporadic.c:213-349

  Refill list stored as a BST keyed by rTime. The merge/
  append decision becomes BST insert with possible node merging.
  The solver must maintain BST ordering through insert-or-merge operations.
-/
import Mathlib
import Std

namespace seL4.ScheduleUsed

-- === BEGIN: DEFINITIONS (provided) ===

structure Refill where
  rTime   : Nat
  rAmount : Nat
  deriving DecidableEq, Repr

/-- BST of refills, ordered by rTime. -/
inductive RefillBST where
  | leaf : RefillBST
  | node : RefillBST → Refill → RefillBST → RefillBST
  deriving Repr

def RefillBST.mem (r : Refill) : RefillBST → Prop
  | .leaf => False
  | .node l x rt => r = x ∨ RefillBST.mem r l ∨ RefillBST.mem r rt

instance : Membership Refill RefillBST where
  mem t r := RefillBST.mem r t

def RefillBST.All (p : Refill → Prop) : RefillBST → Prop
  | .leaf => True
  | .node l x r => p x ∧ RefillBST.All p l ∧ RefillBST.All p r

def RefillBST.Ordered : RefillBST → Prop
  | .leaf => True
  | .node l x r =>
    RefillBST.All (fun e => e.rTime < x.rTime) l ∧
    RefillBST.All (fun e => x.rTime < e.rTime) r ∧
    RefillBST.Ordered l ∧ RefillBST.Ordered r

def RefillBST.NoDup : RefillBST → Prop
  | .leaf => True
  | .node l x r =>
    x ∉ l ∧ x ∉ r ∧
    RefillBST.NoDup l ∧ RefillBST.NoDup r

def RefillBST.size : RefillBST → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

def RefillBST.height : RefillBST → Nat
  | .leaf => 0
  | .node l _ r => Nat.succ (Nat.max l.height r.height)

def RefillBST.Balanced : RefillBST → Prop
  | .leaf => True
  | .node l _ r =>
    RefillBST.Balanced l ∧ RefillBST.Balanced r ∧
    l.height ≤ r.height + 1 ∧ r.height ≤ l.height + 1

/-- Sum of refill amounts (the "budget"). -/
def RefillBST.budgetSum : RefillBST → Nat
  | .leaf => 0
  | .node l x r => l.budgetSum + x.rAmount + r.budgetSum

/-- Find the entry with maximum rTime (rightmost node). -/
def RefillBST.maxEntry : RefillBST → Option Refill
  | .leaf => none
  | .node _ x .leaf => some x
  | .node _ _ r => RefillBST.maxEntry r


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


/-- Kernel state for scheduling: the refill BST. -/
structure SchedState where
  refills : RefillBST

/-- Budget conservation. -/
def budgetConserved (input output : RefillBST) (new : Refill) : Prop :=
  output.budgetSum = input.budgetSum + new.rAmount

/-- The new refill is "tail-overlapping" with the last (max-time) refill. -/
def tailOverlapping (last : Refill) (new : Refill) : Prop :=
  new.rTime ≤ last.rTime + last.rAmount

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===
-- No additional predicates.
-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No axioms.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

/-- Monadic schedule: merge or insert a new refill into the BST. -/
def scheduleUsedM (new : Refill) : KM SchedState Unit :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem scheduleUsedM_correct (new : Refill) (ss : SchedState)
    (h_ord : ss.refills.Ordered)
    (h_nodup : ss.refills.NoDup)
    (h_lastOk : ∀ last, ss.refills.maxEntry = some last → last.rTime ≤ new.rTime) :
    let rs := ss.refills
    -- The operation must succeed.
    (scheduleUsedM new).run ss ≠ none ∧
    (∀ ss' : SchedState,
      (scheduleUsedM new).run ss = some ((), ss') →
      let out := ss'.refills
      -- (1) Budget conservation.
      budgetConserved rs out new ∧
      -- (2) BST ordering preserved.
      out.Ordered ∧
      -- (3) No duplicates preserved.
      out.NoDup ∧
      -- (4) Anti-degeneration: output tree is balanced.
      out.Balanced ∧
      -- (5) Log-height bound for output tree.
      (out.height ≤ Nat.log2 (out.size + 1) + 1) ∧
      -- (6) Size grows by 0 (merge) or 1 (insert).
      (out.size = rs.size ∨ out.size = rs.size + 1) ∧
      -- (7) Empty input.
      (rs = .leaf → out = .node .leaf new .leaf) ∧
      -- (8) Append case: non-overlapping new refill is inserted.
      (∀ last, rs.maxEntry = some last → last.rTime + last.rAmount < new.rTime →
        new ∈ out) ∧
      -- (9) Merge case: overlapping refill merges amounts.
      (∀ last, rs.maxEntry = some last → tailOverlapping last new →
        out.size = rs.size ∧
        ∃ merged, merged ∈ out ∧
          merged.rAmount = last.rAmount + new.rAmount) ∧
      -- (10) All previous entries (except possibly merged) are in output.
      (∀ r, r ∈ rs → r ∈ out ∨
        (∃ last, rs.maxEntry = some last ∧ r = last ∧ tailOverlapping last new)) ∧
      -- (11) Determinism.
      (∀ ss₂ : SchedState, ss₂.refills = rs →
        ∀ ss₂', (scheduleUsedM new).run ss₂ = some ((), ss₂') →
          ss₂'.refills = out) ∧
      -- (12) Bind-consistency: scheduling two refills preserves budget.
      (∀ new' : Refill,
        ∀ ss_ab : SchedState,
          (KM.bind (scheduleUsedM new) (fun _ => scheduleUsedM new')).run ss
            = some ((), ss_ab) →
          ss_ab.refills.budgetSum = rs.budgetSum + new.rAmount + new'.rAmount) ∧
      -- (13) Cardinality monotonicity.
      rs.size ≤ out.size) := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4.ScheduleUsed
