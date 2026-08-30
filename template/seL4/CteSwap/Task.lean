/-
  seL4 Optimization Task: cteSwap — MDB doubly-linked swap
  Source: src/object/cnode.c:489-527

  Naive: six conditional pointer updates touching four neighbour slots.
  Optimized: a single transposition on the MDB BST view.

  No reference function. The swap must be characterized
  intrinsically by BST-order/permutation properties. Implementation lives
  inside the KM kernel monad.
-/
import Mathlib
import Std

namespace seL4.CteSwap

-- === BEGIN: DEFINITIONS (provided) ===

abbrev CapId := Nat

structure MDBNode where
  capId : CapId
  payload : Nat
  deriving DecidableEq, Repr

/-- Binary search tree keyed by `MDBNode.capId`. -/
inductive MDBTree where
  | leaf : MDBTree
  | node : MDBTree → MDBNode → MDBTree → MDBTree
  deriving DecidableEq, Repr

/-- Membership of a full `MDBNode` in the tree. -/
def MDBTree.mem (n : MDBNode) : MDBTree → Prop
  | .leaf => False
  | .node l v r => n = v ∨ MDBTree.mem n l ∨ MDBTree.mem n r

instance : Membership MDBNode MDBTree where
  mem t n := MDBTree.mem n t

/-- A `CapId` appears somewhere in the tree. -/
def MDBTree.memId (id : CapId) : MDBTree → Prop
  | .leaf => False
  | .node l v r => v.capId = id ∨ MDBTree.memId id l ∨ MDBTree.memId id r

/-- Every node in the tree satisfies `P`. -/
def MDBTree.All (P : MDBNode → Prop) : MDBTree → Prop
  | .leaf => True
  | .node l v r => P v ∧ MDBTree.All P l ∧ MDBTree.All P r

/-- BST ordering invariant: every key in the left subtree is less than
    the root key, and every key in the right subtree is greater. -/
def MDBTree.Ordered : MDBTree → Prop
  | .leaf => True
  | .node l v r =>
    MDBTree.All (fun n => n.capId < v.capId) l ∧
    MDBTree.All (fun n => v.capId < n.capId) r ∧
    MDBTree.Ordered l ∧
    MDBTree.Ordered r

/-- No duplicate `capId`s in the tree. -/
def MDBTree.NoDup : MDBTree → Prop
  | .leaf => True
  | .node l v r =>
    ¬ MDBTree.memId v.capId l ∧
    ¬ MDBTree.memId v.capId r ∧
    MDBTree.NoDup l ∧
    MDBTree.NoDup r

/-- Number of internal nodes. -/
def MDBTree.size : MDBTree → Nat
  | .leaf => 0
  | .node l _ r => 1 + MDBTree.size l + MDBTree.size r

/-- Height of the tree. -/
def MDBTree.height : MDBTree → Nat
  | .leaf => 0
  | .node l _ r => Nat.succ (Nat.max l.height r.height)

/-- AVL-style local balance condition. -/
def MDBTree.Balanced : MDBTree → Prop
  | .leaf => True
  | .node l _ r =>
    MDBTree.Balanced l ∧ MDBTree.Balanced r ∧
    l.height ≤ r.height + 1 ∧ r.height ≤ l.height + 1

/-- Look up the `MDBNode` with the given `capId` (BST search). -/
def MDBTree.find (id : CapId) : MDBTree → Option MDBNode
  | .leaf => none
  | .node l v r =>
    if id < v.capId then MDBTree.find id l
    else if v.capId < id then MDBTree.find id r
    else some v

/-- Replace the payload of the node with the given `capId`,
    keeping BST structure intact (key unchanged). -/
def MDBTree.updatePayload (id : CapId) (p : Nat) : MDBTree → MDBTree
  | .leaf => .leaf
  | .node l v r =>
    if id < v.capId then .node (MDBTree.updatePayload id p l) v r
    else if v.capId < id then .node l v (MDBTree.updatePayload id p r)
    else .node l { v with payload := p } r

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

-- Equational lemmas for `.run` (proved before sealing)
theorem KM.ret_run {σ α : Type} (a : α) (s : σ) : (KM.ret a).run s = some (a, s) := rfl
theorem KM.bind_run {σ α β : Type} (m : KM σ α) (f : α → KM σ β) (s : σ) :
    (KM.bind m f).run s = match m.run s with
      | none => none
      | some (a, s') => (f a).run s' := rfl
theorem KM.get_run {σ : Type} (s : σ) : (KM.get : KM σ σ).run s = some (s, s) := rfl
theorem KM.set_run {σ : Type} (s' : σ) (s : σ) : (KM.set s').run s = some ((), s') := rfl
theorem KM.fail_run {σ α : Type} (s : σ) : (KM.fail : KM σ α).run s = none := rfl

-- Seal KM operations: solver cannot unfold these
attribute [irreducible] KM.ret KM.bind KM.get KM.set KM.fail

/-- Kernel state for swap: just the MDB tree. -/
structure SwapState where
  mdb : MDBTree

-- MDBTree API lemmas (proved before sealing)
theorem MDBTree.mem_leaf (n : MDBNode) : n ∈ (MDBTree.leaf : MDBTree) ↔ False := by
  constructor <;> intro h <;> exact h.elim

theorem MDBTree.mem_node (n : MDBNode) (l : MDBTree) (v : MDBNode) (r : MDBTree) :
    n ∈ MDBTree.node l v r ↔ n = v ∨ n ∈ l ∨ n ∈ r := Iff.rfl

-- Seal MDBTree operations
attribute [irreducible] MDBTree.mem MDBTree.memId MDBTree.All
    MDBTree.Ordered MDBTree.NoDup MDBTree.size MDBTree.height MDBTree.Balanced
    MDBTree.find MDBTree.updatePayload

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

/-- Two capIds are present and distinct in the MDB tree. -/
def validSwap (mdb : MDBTree) (a b : CapId) : Prop :=
  a ≠ b ∧ mdb.memId a ∧ mdb.memId b

-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No axioms.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

/-- Monadic swap: exchange the payloads of two MDB entries identified
    by `capId`, keeping BST keys in place. Must not fail when both
    capIds exist. -/
def swapM (a b : CapId) : KM SwapState Unit :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem swapM_correct (a b : CapId) (ss : SwapState)
    (h_valid : validSwap ss.mdb a b)
    (h_ord : ss.mdb.Ordered)
    (h_nodup : ss.mdb.NoDup)
    -- The swap exchanges two payloads and keeps the BST shape, so it is a
    -- structure-preserving involution. Clauses (11)/(12) require the RESULT
    -- to be balanced and log-height-bounded; since the shape is unchanged,
    -- those must hold of the INPUT. Without these the theorem is
    -- unsatisfiable: clause (11) (result balanced) together with clause (13)
    -- (self-inverse) would force every admissible input to be balanced,
    -- which an unbalanced ordered tree (e.g. the chain 1<2<3) contradicts.
    (h_bal : ss.mdb.Balanced)
    (h_logh : ss.mdb.height ≤ Nat.log2 (ss.mdb.size + 1) + 1) :
    -- (1) Non-failure: the operation must succeed.
    (swapM a b).run ss ≠ none ∧
    (∀ ss' : SwapState,
      (swapM a b).run ss = some ((), ss') →
      let mdb := ss.mdb
      let mdb' := ss'.mdb
      -- (2) BST ordering preserved.
      mdb'.Ordered ∧
      -- (3) No-duplicate-ids preserved.
      mdb'.NoDup ∧
      -- (4) Size preserved.
      mdb'.size = mdb.size ∧
      -- (5) Membership preserved: same set of capIds.
      (∀ id : CapId, mdb'.memId id ↔ mdb.memId id) ∧
      -- (6) Payload swap: node with capId = a gets b's old payload
      --     and vice versa.
      (∀ na nb : MDBNode,
        mdb.find a = some na → mdb.find b = some nb →
        mdb'.find a = some { capId := a, payload := nb.payload } ∧
        mdb'.find b = some { capId := b, payload := na.payload }) ∧
      -- (7) Non-swapped nodes are untouched.
      (∀ id : CapId, id ≠ a → id ≠ b →
        mdb'.find id = mdb.find id) ∧
      -- (8) Self-inverse via monadic bind.
      (∀ ss'' : SwapState,
        (KM.bind (swapM a b) (fun _ => swapM a b)).run ss = some ((), ss'') →
        ss''.mdb = mdb) ∧
      -- (9) Symmetry: swap a b and swap b a yield the same tree.
      (∀ ss_ab ss_ba : SwapState,
        (swapM a b).run ss = some ((), ss_ab) →
        (swapM b a).run ss = some ((), ss_ba) →
        ss_ab.mdb = ss_ba.mdb) ∧
      -- (10) Determinism: result depends only on the MDB.
      (∀ ss₂ : SwapState, ss₂.mdb = mdb →
        ∀ ss₂' : SwapState, (swapM a b).run ss₂ = some ((), ss₂') →
          ss₂'.mdb = mdb') ∧
      -- (11) Anti-degeneration: balanced shape preserved.
      mdb'.Balanced ∧
      -- (12) Log-height bound for the resulting tree.
      (mdb'.height ≤ Nat.log2 (mdb'.size + 1) + 1) ∧
      -- (13) Exact involution: applying the same swap twice restores full state.
      ((KM.bind (swapM a b) (fun _ => swapM a b)).run ss = some ((), ss)) ∧
      -- (14) Option-shape exclusivity.
      ((swapM a b).run ss = none → False)) := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4.CteSwap
