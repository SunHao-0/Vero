/-
  seL4 Optimization Task: createNewObjects — batch cap installation
                          (BST-based slot map variant)
  Source: src/object/objecttype.c:595-622

  Modified to a five-function STATE MACHINE with a global cap-id
  injectivity invariant. The slot map is represented as a binary
  search tree keyed by SlotAddr.
-/
import Mathlib
import Std

namespace seL4.CreateNewObjects

-- === BEGIN: DEFINITIONS (provided) ===

abbrev SlotAddr := Nat
abbrev CapId    := Nat

/-- A binary search tree keyed by `SlotAddr`, storing `CapId` values. -/
inductive SlotBST where
  | leaf : SlotBST
  | node : SlotBST → (SlotAddr × CapId) → SlotBST → SlotBST

/-- Membership: `(a, id)` is stored somewhere in the tree. -/
def SlotBST.mem : SlotBST → SlotAddr × CapId → Prop
  | .leaf, _ => False
  | .node l p r, q => p = q ∨ l.mem q ∨ r.mem q

/-- Lookup the `CapId` associated with a `SlotAddr`, if any. -/
def SlotBST.lookup : SlotBST → SlotAddr → Option CapId
  | .leaf, _ => none
  | .node l (a, id) r, k =>
    if k < a then l.lookup k
    else if k > a then r.lookup k
    else some id

/-- All entries in the tree satisfy a predicate. -/
def SlotBST.All (P : SlotAddr × CapId → Prop) : SlotBST → Prop
  | .leaf => True
  | .node l p r => P p ∧ l.All P ∧ r.All P

/-- BST ordering invariant: all keys in the left subtree are less than the
    node key, and all keys in the right subtree are greater. -/
def SlotBST.Ordered : SlotBST → Prop
  | .leaf => True
  | .node l (a, _) r =>
    l.All (fun p => p.1 < a) ∧
    r.All (fun p => p.1 > a) ∧
    l.Ordered ∧ r.Ordered

/-- No duplicate `SlotAddr` keys in the tree. -/
def SlotBST.NoDup : SlotBST → Prop
  | .leaf => True
  | .node l (a, _) r =>
    l.All (fun p => p.1 ≠ a) ∧
    r.All (fun p => p.1 ≠ a) ∧
    (∀ p q, l.mem p → r.mem q → p.1 ≠ q.1) ∧
    l.NoDup ∧ r.NoDup

/-- Number of entries in the tree. -/
def SlotBST.size : SlotBST → Nat
  | .leaf => 0
  | .node l _ r => 1 + l.size + r.size

/-- Set of `SlotAddr` keys present in the tree. -/
def SlotBST.keys : SlotBST → Set SlotAddr
  | .leaf => ∅
  | .node l (a, _) r => l.keys ∪ {a} ∪ r.keys

/-- An object window: `count` slots starting at `base`, each
    `2 ^ objBits` apart. -/
structure Window where
  base    : Nat
  objBits : Nat
  count   : Nat

def Window.addrAt (w : Window) (i : Nat) : SlotAddr :=
  w.base + i * 2 ^ w.objBits

/-- The empty BST (state-machine zero element). -/
def emptyBST : SlotBST := .leaf

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

/-- All window slots are currently empty (lookup returns none). -/
def windowFree (m : SlotBST) (w : Window) : Prop :=
  ∀ i, i < w.count → m.lookup (w.addrAt i) = none

/-- Global cap-id injectivity invariant: no two distinct addresses in the
    BST are mapped to the same cap id. -/
def capIdInjective (m : SlotBST) : Prop :=
  ∀ a₁ a₂ id, m.lookup a₁ = some id → m.lookup a₂ = some id → a₁ = a₂

/-- A "fresh range" of cap ids: an interval `[firstCapId, firstCapId + n)`
    in which none of the ids is currently used by `m`. -/
def freshRange (m : SlotBST) (firstCapId : CapId) (n : Nat) : Prop :=
  ∀ a k, firstCapId ≤ k → k < firstCapId + n → m.lookup a ≠ some k

-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No axioms.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

/-- Insert a single cap at one slot in the BST. -/
def createOne (m : SlotBST) (a : SlotAddr) (id : CapId) : SlotBST :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable, createOne) ===
  sorry
-- === END: IMPLEMENTATION (createOne) ===

-- === BEGIN: SPEC (provided, createBatch) ===
/-- Batch-install `count` fresh caps with consecutive ids starting at
    `firstCapId` into the window `w`. -/
def createBatch (m : SlotBST) (w : Window) (firstCapId : CapId) : SlotBST :=
-- === END: SPEC (createBatch) ===
-- === BEGIN: IMPLEMENTATION (editable, createBatch) ===
  sorry
-- === END: IMPLEMENTATION (createBatch) ===

-- === BEGIN: SPEC (provided, deleteOne) ===
/-- Delete the cap at one slot in the BST. -/
def deleteOne (m : SlotBST) (a : SlotAddr) : SlotBST :=
-- === END: SPEC (deleteOne) ===
-- === BEGIN: IMPLEMENTATION (editable, deleteOne) ===
  sorry
-- === END: IMPLEMENTATION (deleteOne) ===

-- === BEGIN: SPEC (provided, deleteBatch) ===
/-- Delete all caps in a window from the BST. -/
def deleteBatch (m : SlotBST) (w : Window) : SlotBST :=
-- === END: SPEC (deleteBatch) ===
-- === BEGIN: IMPLEMENTATION (editable, deleteBatch) ===
  sorry
-- === END: IMPLEMENTATION (deleteBatch) ===

-- === BEGIN: SPEC (provided, query) ===
/-- Lookup a slot address in the BST. -/
def query (m : SlotBST) (a : SlotAddr) : Option CapId :=
-- === END: SPEC (query) ===
-- === BEGIN: IMPLEMENTATION (editable, query) ===
  sorry
-- === END: IMPLEMENTATION (query) ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem createBatch_state_machine_correct :
    -- (1) Empty BST: every query returns `none`, injectivity holds.
    (∀ a, query emptyBST a = none) ∧
    emptyBST.Ordered ∧
    emptyBST.NoDup ∧
    capIdInjective emptyBST ∧
    -- (2) `query` equals `lookup`.
    (∀ m, m.Ordered → ∀ a, query m a = m.lookup a) ∧
    -- (3) `createOne` updates exactly one slot and preserves Ordered.
    (∀ m a id, m.Ordered →
      (createOne m a id).lookup a = some id) ∧
    (∀ m a id b, m.Ordered → b ≠ a →
      (createOne m a id).lookup b = m.lookup b) ∧
    (∀ m a id, m.Ordered → (createOne m a id).Ordered) ∧
    -- (4) `deleteOne` clears exactly one slot and preserves Ordered.
    (∀ m a, m.Ordered →
      (deleteOne m a).lookup a = none) ∧
    (∀ m a b, m.Ordered → b ≠ a →
      (deleteOne m a).lookup b = m.lookup b) ∧
    (∀ m a, m.Ordered → (deleteOne m a).Ordered) ∧
    -- (5) Round-trip: `deleteOne ∘ createOne` cancels when pre-state
    --     did not map that slot.
    (∀ m a id, m.Ordered → m.lookup a = none →
      ∀ b, (deleteOne (createOne m a id) a).lookup b = m.lookup b) ∧
    -- (6) Round-trip: `createOne ∘ deleteOne` restores when pre-state
    --     mapped that slot to the same id.
    (∀ m a id, m.Ordered → m.lookup a = some id →
      ∀ b, (createOne (deleteOne m a) a id).lookup b = m.lookup b) ∧
    -- (7) Distinct-slot writes commute (on lookups).
    (∀ m a₁ a₂ id₁ id₂, m.Ordered → a₁ ≠ a₂ →
      ∀ b, (createOne (createOne m a₁ id₁) a₂ id₂).lookup b =
           (createOne (createOne m a₂ id₂) a₁ id₁).lookup b) ∧
    -- (8) Distinct-slot deletes commute (on lookups).
    (∀ m a₁ a₂, m.Ordered → a₁ ≠ a₂ →
      ∀ b, (deleteOne (deleteOne m a₁) a₂).lookup b =
           (deleteOne (deleteOne m a₂) a₁).lookup b) ∧
    -- (9) `createBatch` pointwise: installs at window addresses,
    --     preserves rest.
    (∀ m w firstCapId, m.Ordered →
      (∀ i, i < w.count →
        (createBatch m w firstCapId).lookup (w.addrAt i) = some (firstCapId + i)) ∧
      (∀ a, (∀ i, i < w.count → a ≠ w.addrAt i) →
        (createBatch m w firstCapId).lookup a = m.lookup a)) ∧
    -- (10) `deleteBatch` pointwise: clears window addresses,
    --      preserves rest.
    (∀ m w, m.Ordered →
      (∀ i, i < w.count →
        (deleteBatch m w).lookup (w.addrAt i) = none) ∧
      (∀ a, (∀ i, i < w.count → a ≠ w.addrAt i) →
        (deleteBatch m w).lookup a = m.lookup a)) ∧
    -- (11) Injectivity preservation under `createBatch`.
    (∀ m w firstCapId,
      m.Ordered →
      capIdInjective m →
      windowFree m w →
      freshRange m firstCapId w.count →
      w.objBits ≥ 1 →
      capIdInjective (createBatch m w firstCapId)) ∧
    -- (12) Round-trip: `deleteBatch` undoes `createBatch` (on lookups).
    (∀ m w firstCapId,
      m.Ordered →
      capIdInjective m →
      windowFree m w →
      freshRange m firstCapId w.count →
      w.objBits ≥ 1 →
      ∀ a, (deleteBatch (createBatch m w firstCapId) w).lookup a = m.lookup a) ∧
    -- (13) Disjoint-window commutativity (on lookups).
    (∀ m w₁ w₂ id₁ id₂,
      m.Ordered →
      capIdInjective m →
      (∀ i j, i < w₁.count → j < w₂.count → w₁.addrAt i ≠ w₂.addrAt j) →
      (∀ k₁ k₂, id₁ ≤ k₁ → k₁ < id₁ + w₁.count →
                 id₂ ≤ k₂ → k₂ < id₂ + w₂.count → k₁ ≠ k₂) →
      windowFree m w₁ →
      windowFree m w₂ →
      freshRange m id₁ w₁.count →
      freshRange m id₂ w₂.count →
      ∀ a,
        (createBatch (createBatch m w₁ id₁) w₂ id₂).lookup a =
        (createBatch (createBatch m w₂ id₂) w₁ id₁).lookup a) ∧
    -- (14) Singleton case: a one-slot window equals `createOne` (on lookups).
    (∀ m b objBits id, m.Ordered →
      ∀ a, (createBatch m ⟨b, objBits, 1⟩ id).lookup a =
           (createOne m b id).lookup a) ∧
    -- (15) Empty-window case: a zero-slot window is the identity (on lookups).
    (∀ m b objBits id, m.Ordered →
      ∀ a, (createBatch m ⟨b, objBits, 0⟩ id).lookup a = m.lookup a) ∧
    -- (16) Address-existential: every cap-id in the new range has a
    --      preimage address in the window.
    (∀ m w firstCapId,
      m.Ordered →
      capIdInjective m →
      windowFree m w →
      freshRange m firstCapId w.count →
      w.objBits ≥ 1 →
      ∀ k, firstCapId ≤ k → k < firstCapId + w.count →
        ∃ i, i < w.count ∧
          (createBatch m w firstCapId).lookup (w.addrAt i) = some k ∧
          k = firstCapId + i) ∧
    -- (17) BST Ordered preservation for `createBatch` and `deleteBatch`.
    (∀ m w firstCapId, m.Ordered → (createBatch m w firstCapId).Ordered) ∧
    (∀ m w, m.Ordered → (deleteBatch m w).Ordered) ∧
    -- (18) NoDup preservation for all operations.
    (∀ m a id, m.Ordered → m.NoDup → (createOne m a id).NoDup) ∧
    (∀ m a, m.Ordered → m.NoDup → (deleteOne m a).NoDup) ∧
    (∀ m w firstCapId, m.Ordered → m.NoDup → (createBatch m w firstCapId).NoDup) ∧
    (∀ m w, m.Ordered → m.NoDup → (deleteBatch m w).NoDup) ∧
    -- (19) Empty-window delete is identity.
    (∀ m b objBits, m.Ordered → deleteBatch m ⟨b, objBits, 0⟩ = m) := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4.CreateNewObjects
