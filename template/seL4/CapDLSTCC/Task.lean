/-
  CapDL Optimization Task: Static Capability Checker — reachability closure.
  Source: capdl/capDL-tool/CapDL/STCC.hs

  Computes the transitive closure of the "subject can grant cap to object"
  relation in a CapDL model.

  The result is stored as a BST (visited set). The solver
  must implement BST-based graph traversal while maintaining the BST
  ordering invariant through incremental node insertion.
-/
import Mathlib
import Std

namespace seL4.CapDLSTCC

-- === BEGIN: DEFINITIONS (provided) ===

abbrev Node := Nat

/-- Custom sequence type for edge lists. -/
inductive Seq (α : Type) where
  | nil : Seq α
  | cons : α → Seq α → Seq α
  deriving Repr

def Seq.mem {α : Type} (a : α) : Seq α → Prop
  | .nil => False
  | .cons x xs => a = x ∨ Seq.mem a xs

instance {α : Type} : Membership α (Seq α) where
  mem s a := @Seq.mem α a s

/-- A directed edge `a → b`. -/
abbrev Edge := Node × Node

/-- A graph is a finite sequence of edges. -/
abbrev Graph := Seq Edge

/-- One step of the relation. -/
def stepRel (g : Graph) (a b : Node) : Prop :=
  (a, b) ∈ g

/-- `n`-step reachability. -/
def reachableInN (g : Graph) : Nat → Node → Node → Prop
  | 0,     a, b => a = b
  | k + 1, a, b => ∃ c, stepRel g a c ∧ reachableInN g k c b

/-- General reachability. -/
def reachable (g : Graph) (a b : Node) : Prop :=
  ∃ k, reachableInN g k a b


/-- BST storing the set of reachable nodes. -/
inductive NodeBST where
  | leaf : NodeBST
  | node : NodeBST → Node → NodeBST → NodeBST
  deriving Repr

def NodeBST.mem (k : Nat) : NodeBST → Prop
  | .leaf => False
  | .node l x r => k = x ∨ NodeBST.mem k l ∨ NodeBST.mem k r

instance : Membership Nat NodeBST where
  mem t k := NodeBST.mem k t

def NodeBST.All (p : Nat → Prop) : NodeBST → Prop
  | .leaf => True
  | .node l x r => p x ∧ NodeBST.All p l ∧ NodeBST.All p r

def NodeBST.Ordered : NodeBST → Prop
  | .leaf => True
  | .node l x r =>
    NodeBST.All (· < x) l ∧ NodeBST.All (x < ·) r ∧
    NodeBST.Ordered l ∧ NodeBST.Ordered r

def NodeBST.NoDup : NodeBST → Prop
  | .leaf => True
  | .node l x r => x ∉ l ∧ x ∉ r ∧ NodeBST.NoDup l ∧ NodeBST.NoDup r

def NodeBST.size : NodeBST → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

def NodeBST.height : NodeBST → Nat
  | .leaf => 0
  | .node l _ r => Nat.succ (Nat.max l.height r.height)

def NodeBST.Balanced : NodeBST → Prop
  | .leaf => True
  | .node l _ r =>
    NodeBST.Balanced l ∧ NodeBST.Balanced r ∧
    l.height ≤ r.height + 1 ∧ r.height ≤ l.height + 1

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===
-- No additional predicates.
-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No axioms.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

/-- Transitive closure starting from a single seed node. Returns the
    set of all nodes (as an ordered BST) reachable from `seed`. -/
def reachClosure (g : Graph) (seed : Node) : NodeBST :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem reachClosure_correct (g : Graph) (seed : Node) :
    let result := reachClosure g seed
    -- (1) The seed is always in the result.
    seed ∈ result ∧
    -- (2) Soundness: every node in the result is reachable.
    (∀ n, n ∈ result → reachable g seed n) ∧
    -- (3) Completeness: every reachable node is in the result.
    (∀ n, reachable g seed n → n ∈ result) ∧
    -- (4) BST ordering invariant.
    result.Ordered ∧
    -- (5) No duplicates.
    result.NoDup ∧
    -- (6) Bidirectional characterization.
    (∀ n, n ∈ result ↔ reachable g seed n) ∧
    -- (7) Minimality: any set containing seed and closed under stepRel
    --     contains result.
    (∀ (s : Set Nat),
      seed ∈ s →
      (∀ a, a ∈ s → ∀ b, stepRel g a b → b ∈ s) →
      ∀ n, n ∈ result → n ∈ s) ∧
    -- (8) Closed under one-step.
    (∀ a, a ∈ result → ∀ b, stepRel g a b → b ∈ result) ∧
    -- (9) Monotonicity: adding edges can only enlarge reachable set.
    (∀ g' : Graph, (∀ e, e ∈ g → e ∈ g') →
      ∀ n, n ∈ result → n ∈ reachClosure g' seed) ∧
    -- (10) Idempotence: re-running from any reachable node ⊆ result.
    (∀ n, n ∈ result → ∀ m, m ∈ reachClosure g n → m ∈ result) ∧
    -- (11) Empty graph: result is a singleton BST containing seed.
    (g = .nil → result = .node .leaf seed .leaf) ∧
    -- (12) Anti-degeneration: result BST is balanced.
    result.Balanced ∧
    -- (13) Log-height bound for result BST.
    (result.height ≤ Nat.log2 (result.size + 1) + 1) ∧
    -- (14) Predecessor witness: every reachable n ≠ seed has a
    --      predecessor in result.
    (∀ n, n ∈ result → n ≠ seed →
      ∃ p, p ∈ result ∧ stepRel g p n) ∧
    -- (15) Non-emptiness: closure always contains at least the seed.
    result ≠ .leaf := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4.CapDLSTCC
