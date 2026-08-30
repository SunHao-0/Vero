/-
  seL4 Haskell Spec Optimization: deleteASIDPool
  Source: SEL4/Kernel/VSpace/ARM.lhs:778

  Output stored as a BST keyed by pool index.
  The solver must implement BST insertion while maintaining the
  ordering invariant. Custom inductive predicates removed in favor
  of BST invariant requirements.
-/
import Mathlib
import Std

namespace seL4.DeleteASIDPool

-- === BEGIN: DEFINITIONS (provided) ===

def poolSize : Nat := 1024

abbrev AsidPool := Fin poolSize → Option Nat

/-- Custom sequence type for sparse pool input. -/
inductive Seq (α : Type) where
  | nil : Seq α
  | cons : α → Seq α → Seq α
  deriving Repr

def Seq.mem {α : Type} (a : α) : Seq α → Prop
  | .nil => False
  | .cons x xs => a = x ∨ Seq.mem a xs

instance {α : Type} : Membership α (Seq α) where
  mem s a := @Seq.mem α a s

def Seq.length {α : Type} : Seq α → Nat
  | .nil => 0
  | .cons _ xs => xs.length + 1

def Seq.map {α : Type} {β : Type} (f : α → β) : Seq α → Seq β
  | .nil => .nil
  | .cons x xs => .cons (f x) (Seq.map f xs)

def Seq.Nodup {α : Type} : Seq α → Prop
  | .nil => True
  | .cons x xs => x ∉ xs ∧ Seq.Nodup xs


/-- Sparse representation: only allocated entries (index, page directory). -/
abbrev SparsePool := Seq (Fin poolSize × Nat)


/-- BST keyed by Fin poolSize, storing (Fin poolSize × Nat) pairs. -/
inductive PoolBST where
  | leaf : PoolBST
  | node : PoolBST → (Fin poolSize × Nat) → PoolBST → PoolBST
  deriving Repr

def PoolBST.mem (p : Fin poolSize × Nat) : PoolBST → Prop
  | .leaf => False
  | .node l x r => p = x ∨ PoolBST.mem p l ∨ PoolBST.mem p r

instance : Membership (Fin poolSize × Nat) PoolBST where
  mem t p := PoolBST.mem p t

def PoolBST.memKey (k : Fin poolSize) : PoolBST → Prop
  | .leaf => False
  | .node l x r => k = x.1 ∨ PoolBST.memKey k l ∨ PoolBST.memKey k r

def PoolBST.All (p : (Fin poolSize × Nat) → Prop) : PoolBST → Prop
  | .leaf => True
  | .node l x r => p x ∧ PoolBST.All p l ∧ PoolBST.All p r

def PoolBST.Ordered : PoolBST → Prop
  | .leaf => True
  | .node l x r =>
    PoolBST.All (fun p => p.1.val < x.1.val) l ∧
    PoolBST.All (fun p => x.1.val < p.1.val) r ∧
    PoolBST.Ordered l ∧ PoolBST.Ordered r

def PoolBST.NoDup : PoolBST → Prop
  | .leaf => True
  | .node l x r =>
    ¬PoolBST.memKey x.1 l ∧ ¬PoolBST.memKey x.1 r ∧
    PoolBST.NoDup l ∧ PoolBST.NoDup r

def PoolBST.size : PoolBST → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

def PoolBST.height : PoolBST → Nat
  | .leaf => 0
  | .node l _ r => Nat.succ (Nat.max l.height r.height)

/-- Height-balanced BST (AVL-style local balance condition). -/
def PoolBST.Balanced : PoolBST → Prop
  | .leaf => True
  | .node l _ r =>
    PoolBST.Balanced l ∧ PoolBST.Balanced r ∧
    l.height ≤ r.height + 1 ∧ r.height ≤ l.height + 1

/-- Set of keys present. -/
def PoolBST.keySet : PoolBST → Set (Fin poolSize)
  | .leaf => ∅
  | .node l x r => PoolBST.keySet l ∪ {x.1} ∪ PoolBST.keySet r


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


/-- Sparse pool is consistent with full pool. -/
def sparseConsistent (pool : AsidPool) (sparse : SparsePool) : Prop :=
  (∀ p, p ∈ sparse → pool p.1 = some p.2) ∧
  (∀ idx, (pool idx).isSome → ∃ p, p ∈ sparse ∧ p.1 = idx)

/-- The abstract semantic view: the set of keys present in `sparse`. -/
def absView (sparse : SparsePool) : Set (Fin poolSize) :=
  { idx | ∃ p, p ∈ sparse ∧ p.1 = idx }

/-- Kernel state for collect operation. -/
structure CollectState where
  result : PoolBST

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===
-- No additional predicates.
-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No additional axioms.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

/-- Monadic collect: walk the sparse pool and produce a BST result
    in `CollectState.result`. Must not fail. -/
def collectM (sparse : SparsePool) : KM CollectState Unit :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem deletePool_correct (pool : AsidPool) (sparse : SparsePool)
    (h_consistent : sparseConsistent pool sparse)
    (h_nodup : (sparse.map Prod.fst).Nodup) :
    -- The operation must succeed.
    ∀ cs : CollectState,
    (collectM sparse).run cs ≠ none ∧
    (∀ cs' : CollectState,
      (collectM sparse).run cs = some ((), cs') →
      let result := cs'.result
      -- (1) BST ordering invariant.
      result.Ordered ∧
      -- (2) No duplicate keys.
      result.NoDup ∧
      -- (3) Soundness: every key in the BST corresponds to an entry in sparse.
      (∀ p, p ∈ result → p ∈ sparse) ∧
      -- (4) Completeness: every entry in sparse is in the BST.
      (∀ p, p ∈ sparse → p ∈ result) ∧
      -- (5) Size equals sparse length.
      result.size = sparse.length ∧
      -- (6) Key set equals abstract view.
      result.keySet = absView sparse ∧
      -- (7) Pool soundness: every allocated pool slot has its key in the BST.
      (∀ idx, (pool idx).isSome ↔ PoolBST.memKey idx result) ∧
      -- (8) Empty case.
      (sparse = .nil → result = .leaf) ∧
      -- (9) Anti-degeneration: resulting BST must be height-balanced.
      result.Balanced ∧
      -- (10) Log-height bound to rule out linear-height trees.
      (result.height ≤ Nat.log2 (result.size + 1) + 1) ∧
      -- (11) Non-trivial lower bound for height (tightens shape constraints).
      (Nat.log2 (result.size + 1) ≤ result.height + 1) ∧
      -- (12) Determinism: result depends only on sparse, not on initial state.
      (∀ cs₂ : CollectState,
        ∀ cs₂' : CollectState,
          (collectM sparse).run cs₂ = some ((), cs₂') →
          cs₂'.result = result) ∧
      -- (13) View-robustness: any nodup sparse representation with same
      --      abstract key-view yields same keySet and size.
      (∀ sparse2 : SparsePool,
        sparseConsistent pool sparse2 →
        (sparse2.map Prod.fst).Nodup →
        absView sparse2 = absView sparse →
        ∀ cs2 cs2',
          (collectM sparse2).run cs2 = some ((), cs2') →
          cs2'.result.keySet = result.keySet ∧
          cs2'.result.size = result.size) ∧
      -- (14) Size upper bound by sparse length.
      result.size ≤ sparse.length) := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4.DeleteASIDPool
