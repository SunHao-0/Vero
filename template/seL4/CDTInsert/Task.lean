/-
  seL4 Optimization Task: CDT Insert with well-foundedness invariant
  Source: src/object/cnode.c:728-799 (cdt_node insert helpers); src/api/syscall.c (cap derivation tree maintenance)

  The capability derivation tree (CDT) tracks parent → child relationships
  among capabilities. Inserting a new cap requires:
    1. finding the deepest existing cap whose physical region strictly
       contains the new cap (the parent),
    2. splicing the new cap into that parent's `children` list, and
       MOVING any existing siblings now contained in the new cap into
       the new cap's children,
    3. preserving the global well-formedness invariant.

  spec via custom `WF` and `InsertSpec` inductive predicates.
  No `mergeSort` / `eraseFirst` / `Finset.image` / etc. shortcut applies.
  Termination of the insertion uses the structural size of the CDT.
-/
import Mathlib
import Std

namespace seL4.CDTInsert

-- === BEGIN: DEFINITIONS (provided) ===

abbrev CapId := Nat

/-- A simplified physical-region capability. `size > 0`. -/
structure Cap where
  id   : CapId
  base : Nat
  size : Nat
  hpos : 0 < size
  deriving Repr

/-- The closed-open physical region `[base, base + size)` covered by a cap. -/
def Cap.endAddr (c : Cap) : Nat := c.base + c.size

/-- A capability derivation tree node. -/
inductive CDT where
  | node (cap : Cap) (children : List CDT)

/-- Top cap of a CDT. -/
def CDT.cap : CDT → Cap
  | .node c _ => c

/-- Direct children list. -/
def CDT.children : CDT → List CDT
  | .node _ cs => cs

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

/-- Cap `c` is *strictly* contained in cap `p` (proper subregion). -/
def strictContained (c p : Cap) : Prop :=
  p.base ≤ c.base ∧ c.endAddr ≤ p.endAddr ∧ (p.base < c.base ∨ c.endAddr < p.endAddr)

/-- Cap `c` is contained (possibly equal) in `p`. -/
def contained (c p : Cap) : Prop :=
  p.base ≤ c.base ∧ c.endAddr ≤ p.endAddr

/-- Two caps' regions are disjoint. -/
def capDisjoint (a b : Cap) : Prop :=
  a.endAddr ≤ b.base ∨ b.endAddr ≤ a.base

/-- A CDT is well-formed iff at every node:
    every direct child is strictly contained in the parent cap,
    every pair of direct children has disjoint regions,
    and every subtree is well-formed. -/
inductive WF : CDT → Prop where
  | mk (cap : Cap) (children : List CDT)
       (h_contained : ∀ c ∈ children, strictContained c.cap cap)
       (h_pairwise  : children.Pairwise (fun a b => capDisjoint a.cap b.cap))
       (h_wfChildren : ∀ c ∈ children, WF c) :
       WF (.node cap children)

/-- The "kept" / "moved" partition of an existing children list when
    inserting `newCap`: each existing child is `moved` iff strictly
    contained in `newCap`, otherwise `kept` (preserving order). -/
inductive InsertPartition : Cap → List CDT → List CDT → List CDT → Prop where
  | nil (newCap : Cap) : InsertPartition newCap [] [] []
  | move (newCap : Cap) (t : CDT) (ts kept moved : List CDT)
         (h_in : strictContained t.cap newCap)
         (h_rec : InsertPartition newCap ts kept moved) :
         InsertPartition newCap (t :: ts) kept (t :: moved)
  | keep (newCap : Cap) (t : CDT) (ts kept moved : List CDT)
         (h_out : ¬ strictContained t.cap newCap)
         (h_rec : InsertPartition newCap ts kept moved) :
         InsertPartition newCap (t :: ts) (t :: kept) moved

/-- The structural insertion specification, given as a custom inductive
    relation `InsertSpec t newCap t'`: inserting `newCap` into the
    well-formed CDT `t` produces the CDT `t'`. -/
inductive InsertSpec : CDT → Cap → CDT → Prop where
  /-- Direct insertion at this node: no existing child strictly contains
      `newCap`, but the *current* node `cap` does. The new cap becomes
      a fresh child here. Existing children that are now strictly
      contained in `newCap` are moved into `newCap`'s children. -/
  | here  (cap : Cap) (children : List CDT) (newCap : Cap)
          (kept moved : List CDT)
          (h_partition : InsertPartition newCap children kept moved)
          (h_strict    : strictContained newCap cap)
          (h_no_inner  :
            ∀ c ∈ children, ¬ strictContained newCap c.cap) :
          InsertSpec (.node cap children) newCap
            (.node cap (.node newCap moved :: kept))
  /-- Recursive descent into the unique child that strictly contains
      `newCap`. -/
  | descend (cap : Cap) (children : List CDT) (newCap : Cap)
            (pre : List CDT) (focus : CDT) (suf : List CDT)
            (focus' : CDT)
            (h_split   : children = pre ++ focus :: suf)
            (h_strict  : strictContained newCap focus.cap)
            (h_others  : ∀ c ∈ pre ++ suf, ¬ strictContained newCap c.cap)
            (h_rec     : InsertSpec focus newCap focus') :
            InsertSpec (.node cap children) newCap
              (.node cap (pre ++ focus' :: suf))

/-- Membership of a cap-id reachable from a CDT (transitive). -/
inductive InCDT : CapId → CDT → Prop where
  | here (id : CapId) (children : List CDT) (c : Cap)
         (h : c.id = id) : InCDT id (.node c children)
  | child (id : CapId) (cap : Cap) (children : List CDT) (t : CDT)
          (h_mem : t ∈ children) (h_rec : InCDT id t) :
          InCDT id (.node cap children)

/-- Membership of a full `Cap` reachable from a CDT (transitive). -/
inductive CapMem : Cap → CDT → Prop where
  | here (c : Cap) (children : List CDT) : CapMem c (.node c children)
  | child (c : Cap) (cap : Cap) (children : List CDT) (t : CDT)
          (h_mem : t ∈ children) (h_rec : CapMem c t) :
          CapMem c (.node cap children)

/-- Laminarity of `newCap` against every cap already in `t`: for each,
    one strictly contains the other or they are disjoint. This is the
    fundamental seL4 capability invariant (regions never partially
    overlap), and it is exactly what keeps the inserted cap's siblings
    disjoint so the result stays well-formed. -/
def laminarWith (newCap : Cap) (t : CDT) : Prop :=
  ∀ c : Cap, CapMem c t →
    strictContained newCap c ∨ strictContained c newCap ∨ capDisjoint newCap c

-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No axioms.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

/-- Insert `newCap` into the well-formed CDT `t`. The implementation
    must terminate via the structural size of the CDT and produce a
    new CDT satisfying `InsertSpec t newCap (cdtInsert t newCap)`. -/
def cdtInsert (t : CDT) (newCap : Cap) : CDT :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem cdtInsert_correct (t : CDT) (newCap : Cap)
    (h_wf : WF t)
    (h_root : strictContained newCap t.cap)
    (h_fresh : ¬ InCDT newCap.id t)
    -- Laminarity: `newCap` never partially overlaps an existing cap.
    -- Without it a new cap can be spliced as a sibling of a cap it
    -- overlaps but does not contain, and clause (2) `WF t'` becomes
    -- unsatisfiable (e.g. root [0,100), child [15,25), newCap [10,20):
    -- the forced result makes [10,20) and [15,25) overlapping siblings).
    (h_laminar : laminarWith newCap t) :
    let t' := cdtInsert t newCap
    -- (1) The result satisfies the structural `InsertSpec` relation.
    InsertSpec t newCap t' ∧
    -- (2) Well-formedness preserved.
    WF t' ∧
    -- (3) The new id is reachable in `t'`.
    InCDT newCap.id t' ∧
    -- (4) Every previously reachable id is still reachable.
    (∀ id : CapId, InCDT id t → InCDT id t') ∧
    -- (5) Every reachable id in `t'` is either the new one or was
    --     reachable in `t`.
    (∀ id : CapId, InCDT id t' → id = newCap.id ∨ InCDT id t) ∧
    -- (6) The top-level cap is unchanged.
    t'.cap = t.cap ∧
    -- (7) Functional uniqueness via `InsertSpec`: any other CDT
    --     satisfying `InsertSpec t newCap _` equals `t'`.
    (∀ s : CDT, InsertSpec t newCap s → s = t') ∧
    -- (8) Determinism via `InsertPartition` (uniqueness lemma):
    --     for any `cap` and `children`, the partition is unique.
    (∀ cap : Cap, ∀ children kept₁ moved₁ kept₂ moved₂ : List CDT,
      InsertPartition cap children kept₁ moved₁ →
      InsertPartition cap children kept₂ moved₂ →
      kept₁ = kept₂ ∧ moved₁ = moved₂) ∧
    -- (9) Inserting two distinct fresh caps with disjoint regions
    --     commutes on reachable id-sets.
    (∀ newCap₂ : Cap, newCap₂.id ≠ newCap.id →
      ¬ InCDT newCap₂.id t →
      capDisjoint newCap newCap₂ →
      strictContained newCap₂ t.cap →
      ∀ id,
        InCDT id (cdtInsert t' newCap₂) ↔
        InCDT id (cdtInsert (cdtInsert t newCap₂) newCap)) ∧
    -- (10) Root cap-id is preserved.
    t'.cap.id = t.cap.id := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4.CDTInsert
