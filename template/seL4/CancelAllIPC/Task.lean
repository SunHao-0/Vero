/-
  seL4 Optimization Task: cancelAllIPC — batch waiter restart
  Source: src/object/endpoint.c:400-434, src/object/notification.c:243-274

  Naive: walk the EP/notification waiter queue, restart and ready-enqueue
  one thread at a time.
  Optimized: zero the endpoint first, then group the captured waiter list
  by (domain, priority) and splice each per-(d,p) sublist into the ready
  queues with a single bitmap update.

  Ready queues use a BST (binary search tree) keyed by
  thread id. The implementation must insert waiters into BSTs while
  maintaining the BST ordering invariant. Proofs require comparison-based
  case splits at every node — fundamentally harder than flat-list induction.
-/
import Mathlib
import Std

namespace seL4.CancelAllIPC

-- === BEGIN: DEFINITIONS (provided) ===

/-- Custom sequence type for waiter lists (input only). -/
inductive Seq (α : Type) where
  | nil : Seq α
  | cons : α → Seq α → Seq α
  deriving Repr

def Seq.mem {α : Type} (a : α) : Seq α → Prop
  | .nil => False
  | .cons x xs => a = x ∨ Seq.mem a xs

instance {α : Type} : Membership α (Seq α) where
  mem s a := @Seq.mem α a s

def Seq.map {α : Type} {β : Type} (f : α → β) : Seq α → Seq β
  | .nil => .nil
  | .cons x xs => .cons (f x) (Seq.map f xs)

def Seq.Nodup {α : Type} : Seq α → Prop
  | .nil => True
  | .cons x xs => x ∉ xs ∧ Seq.Nodup xs


/-- Binary search tree keyed by natural number. -/
inductive BST where
  | leaf : BST
  | node : BST → Nat → BST → BST
  deriving Repr

/-- Membership in a BST. -/
def BST.mem (k : Nat) : BST → Prop
  | .leaf => False
  | .node l x r => k = x ∨ BST.mem k l ∨ BST.mem k r

instance : Membership Nat BST where
  mem t k := BST.mem k t

/-- Size (number of keys). -/
def BST.size : BST → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

def BST.height : BST → Nat
  | .leaf => 0
  | .node l _ r => Nat.succ (Nat.max l.height r.height)

/-- All keys in the tree satisfy a predicate. -/
def BST.All (p : Nat → Prop) : BST → Prop
  | .leaf => True
  | .node l x r => p x ∧ BST.All p l ∧ BST.All p r

/-- BST ordering invariant: left keys < root < right keys. -/
def BST.Ordered : BST → Prop
  | .leaf => True
  | .node l x r =>
    BST.All (· < x) l ∧ BST.All (x < ·) r ∧
    BST.Ordered l ∧ BST.Ordered r

/-- No duplicate keys. -/
def BST.NoDup : BST → Prop
  | .leaf => True
  | .node l x r => x ∉ l ∧ x ∉ r ∧ BST.NoDup l ∧ BST.NoDup r

/-- Height-balanced BST (AVL-style local balance condition). -/
def BST.Balanced : BST → Prop
  | .leaf => True
  | .node l _ r =>
    BST.Balanced l ∧ BST.Balanced r ∧
    l.height ≤ r.height + 1 ∧ r.height ≤ l.height + 1



/-- Kernel monad: threads state σ and can fail. -/
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


abbrev ThreadId := Nat
abbrev Domain   := Fin 16
abbrev Priority := Fin 256

/-- A waiting thread in an endpoint queue. -/
structure Waiter where
  tid  : ThreadId
  dom  : Domain
  prio : Priority
  deriving DecidableEq, Repr

/-- Per-(domain, priority) ready queue stored as a BST. -/
abbrev ReadyQueues := Domain → Priority → BST

/-- Bitmap recording which (domain, priority) cells are non-empty. -/
abbrev ReadyBitmap := Domain → Priority → Bool

/-- A combined ready-queue/bitmap state. -/
structure ReadyState where
  queues : ReadyQueues
  bitmap : ReadyBitmap

/-- Bitmap is consistent with queues: bit set ↔ tree non-empty. -/
def bitmapConsistent (rs : ReadyState) : Prop :=
  ∀ d p, rs.bitmap d p = true ↔ rs.queues d p ≠ .leaf

/-- All ready queues satisfy the BST ordering invariant. -/
def allOrdered (rs : ReadyState) : Prop :=
  ∀ d p, (rs.queues d p).Ordered

/-- All ready queues are height-balanced. -/
def allBalanced (rs : ReadyState) : Prop :=
  ∀ d p, (rs.queues d p).Balanced

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

/-- All waiters are pairwise distinct on `tid`. -/
def waitersDistinct (ws : Seq Waiter) : Prop :=
  (ws.map Waiter.tid).Nodup

/-- Number of waiters targeting a specific (domain, priority) cell. -/
def waiterCountAt (ws : Seq Waiter) (d : Domain) (p : Priority) : Nat :=
  match ws with
  | .nil => 0
  | .cons w rest =>
      let here := if w.dom = d ∧ w.prio = p then 1 else 0
      here + waiterCountAt rest d p

-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No axioms.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

/-- Batch transition: take an endpoint waiter sequence and produce a kernel
    monadic action that inserts all waiters into the ready-state BSTs
    while maintaining BST ordering. -/
def cancelAllM (waiters : Seq Waiter) : KM ReadyState Unit :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem cancelAll_correct (waiters : Seq Waiter) (rs : ReadyState)
    (h_distinct : waitersDistinct waiters)
    (h_bm : bitmapConsistent rs)
    (h_ordered : allOrdered rs)
    (h_nodup : ∀ d p, (rs.queues d p).NoDup)
    (h_disjoint : ∀ w, w ∈ waiters → w.tid ∉ rs.queues w.dom w.prio)
    -- Input queues must already be balanced (otherwise property (7)
    -- `allBalanced rs'` combined with property (4) `untargeted cells
    -- unchanged` would force an unbalanced input cell to be balanced).
    (h_balanced : allBalanced rs)
    -- Input queues must already meet the logarithmic height bound for
    -- the same reason combined with property (8).
    (h_logh : ∀ d p, (rs.queues d p).height ≤ Nat.log2 ((rs.queues d p).size + 1) + 1) :
    -- Non-failure assertion.
    (∃ rs', (cancelAllM waiters).run rs = some ((), rs')) ∧
    -- Correctness properties.
    (∀ rs', (cancelAllM waiters).run rs = some ((), rs') →
    -- (1) Bitmap consistency preserved.
    bitmapConsistent rs' ∧
    -- (2) BST ordering invariant preserved.
    allOrdered rs' ∧
    -- (3) Membership: a tid is in the (d,p) BST iff it was there before
    --     or belongs to a waiter targeting (d,p).
    (∀ d p tid, tid ∈ rs'.queues d p ↔
      tid ∈ rs.queues d p ∨
        (∃ w, w ∈ waiters ∧ w.tid = tid ∧ w.dom = d ∧ w.prio = p)) ∧
    -- (4) Stability: BSTs not targeted by any waiter are unchanged.
    (∀ d p, (∀ w, w ∈ waiters → ¬(w.dom = d ∧ w.prio = p)) →
      rs'.queues d p = rs.queues d p) ∧
    -- (5) Bitmap characterization.
    (∀ d p, rs'.bitmap d p = true ↔
      rs.bitmap d p = true ∨ ∃ w, w ∈ waiters ∧ w.dom = d ∧ w.prio = p) ∧
    -- (6) No-dup preservation.
    (∀ d p, (rs'.queues d p).NoDup) ∧
    -- (7) Anti-degeneration: all output queues remain balanced.
    (allBalanced rs') ∧
    -- (8) Per-queue logarithmic height bound.
    (∀ d p, (rs'.queues d p).height ≤ Nat.log2 ((rs'.queues d p).size + 1) + 1) ∧
    -- (9) No-op on empty waiter sequence.
    (waiters = .nil → rs'.queues = rs.queues ∧ rs'.bitmap = rs.bitmap) ∧
    -- (10) Exact size delta: each BST grows by exactly its matching waiters.
    (∀ d p, (rs'.queues d p).size = (rs.queues d p).size + waiterCountAt waiters d p) ∧
    -- (11) Waiter inclusion: every waiter's tid ends up in its target BST.
    (∀ w, w ∈ waiters → w.tid ∈ rs'.queues w.dom w.prio) ∧
    -- (12) Targeted-cell liveness: any targeted cell is non-empty after batch.
    (∀ d p, waiterCountAt waiters d p > 0 → rs'.queues d p ≠ .leaf)) ∧
    -- Determinism.
    (∀ rs₁ rs₂, (cancelAllM waiters).run rs = some ((), rs₁) →
                 (cancelAllM waiters).run rs = some ((), rs₂) → rs₁ = rs₂) ∧
    -- Empty waiter batch is a full-state no-op.
    (waiters = .nil → ∀ rs', (cancelAllM waiters).run rs = some ((), rs') → rs' = rs) := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4.CancelAllIPC
