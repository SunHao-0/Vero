/-
  seL4 Optimization Task: cteRevoke — MDB Revocation

  Original: O(n²) — find direct child, delete + re-parent grandchildren,
            restart from beginning (because new direct children appear)
  Optimized: O(n) — compute all transitive descendants, batch remove

  cteRevoke removes all capabilities derived from a target in the MDB
  (Mapping Database). The MDB forms a tree via parent pointers. Implement
  a single-pass removal of all transitive descendants and prove correctness.

  The implementation lives inside a custom kernel monad `KM` that threads
  kernel state and can fail.

  Source: seL4/src/object/cnode.c
-/
import Mathlib
import Std

namespace seL4.CteRevoke

-- === BEGIN: DEFINITIONS (provided) ===

/-- Custom sequence type (no Mathlib automation). -/
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

def Seq.filter {α : Type} (p : α → Bool) : Seq α → Seq α
  | .nil => .nil
  | .cons x xs => if p x then .cons x (Seq.filter p xs) else Seq.filter p xs

def Seq.Pairwise {α : Type} (R : α → α → Prop) : Seq α → Prop
  | .nil => True
  | .cons x xs => (∀ y, y ∈ xs → R x y) ∧ Seq.Pairwise R xs

inductive Seq.Subseq {α : Type} : Seq α → Seq α → Prop where
  | nil : Seq.Subseq .nil .nil
  | cons (x : α) {xs ys : Seq α} : Seq.Subseq xs ys → Seq.Subseq (.cons x xs) (.cons x ys)
  | skip (x : α) {xs ys : Seq α} : Seq.Subseq xs ys → Seq.Subseq xs (.cons x ys)

/-- Kernel monad: threads state σ and can fail. No Lean Monad instance
    registered — the solver must reason about `bind`/`ret` manually. -/
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
def KM.modify {σ : Type} (f : σ → σ) : KM σ Unit := ⟨fun s => some ((), f s)⟩

-- Equational lemmas for `.run` (proved before sealing)
theorem KM.ret_run {σ α : Type} (a : α) (s : σ) : (KM.ret a).run s = some (a, s) := rfl
theorem KM.bind_run {σ α β : Type} (m : KM σ α) (f : α → KM σ β) (s : σ) :
    (KM.bind m f).run s = match m.run s with
      | none => none
      | some (a, s') => (f a).run s' := rfl
theorem KM.get_run {σ : Type} (s : σ) : (KM.get : KM σ σ).run s = some (s, s) := rfl
theorem KM.set_run {σ : Type} (s' : σ) (s : σ) : (KM.set s').run s = some ((), s') := rfl
theorem KM.fail_run {σ α : Type} (s : σ) : (KM.fail : KM σ α).run s = none := rfl
theorem KM.modify_run {σ : Type} (f : σ → σ) (s : σ) : (KM.modify f).run s = some ((), f s) := rfl

-- Seal KM operations: solver cannot unfold these
attribute [irreducible] KM.ret KM.bind KM.get KM.set KM.fail KM.modify

/-- MDB node with parent pointer forming a derivation tree. -/
structure CapNode where
  capId : Nat
  parentId : Option Nat
  deriving DecidableEq, Repr

abbrev MDB := Seq CapNode

/-- Kernel state: the MDB plus a revocation log. -/
structure KernelState where
  mdb : MDB
  revLog : Seq Nat    -- log of revoked capIds

/-- Transitive descendant: reachable from nodeId to ancestorId
    via parent-pointer chain in the MDB. -/
inductive IsDesc (mdb : MDB) : Nat → Nat → Prop where
  | child (node : CapNode) (cId aId : Nat) :
      node ∈ mdb → node.capId = cId → node.parentId = some aId →
      IsDesc mdb cId aId
  | trans (cId mId aId : Nat) :
      IsDesc mdb cId mId → IsDesc mdb mId aId →
      IsDesc mdb cId aId

/-- All capIds are unique. -/
def uniqueIds (mdb : MDB) : Prop :=
  mdb.Pairwise (fun a b => a.capId ≠ b.capId)

/-- Parent-pointer graph is acyclic. -/
def acyclic (mdb : MDB) : Prop :=
  ∀ id, ¬ IsDesc mdb id id

def wellFormed (mdb : MDB) : Prop :=
  uniqueIds mdb ∧ acyclic mdb

-- Seq API lemmas (proved before sealing)
theorem Seq.mem_nil {α : Type} (a : α) : a ∈ (Seq.nil : Seq α) ↔ False := by
  constructor <;> intro h <;> exact h.elim
theorem Seq.mem_cons {α : Type} (a x : α) (xs : Seq α) :
    a ∈ Seq.cons x xs ↔ a = x ∨ a ∈ xs := Iff.rfl

-- Seal Seq operations
attribute [irreducible] Seq.mem Seq.length Seq.filter Seq.Pairwise

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===
-- No additional predicates.
-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No axioms. You must derive any structural lemmas about `IsDesc`,
-- `Seq`, and `KM` from their inductive/structural definitions.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

/-- Monadic revocation: remove all transitive descendants of targetId
    from the MDB in the kernel state, logging each revoked capId.
    Must not fail on well-formed inputs.
    You may define any auxiliary functions or lemmas you need. -/
def revokeM (targetId : Nat) : KM KernelState Unit :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem revokeM_correct (targetId : Nat) (ks : KernelState)
    (h_wf : wellFormed ks.mdb)
    (h_log : ks.revLog = .nil) :
    -- The operation must succeed (not fail).
    (revokeM targetId).run ks ≠ none ∧
    -- All properties hold on the resulting state.
    (∀ ks' : KernelState,
      (revokeM targetId).run ks = some ((), ks') →
      let mdb := ks.mdb
      let result := ks'.mdb
      let revoked := ks'.revLog
      -- (1) No transitive descendants of targetId remain.
      (∀ n, n ∈ result → ¬ IsDesc mdb n.capId targetId) ∧
      -- (2) All non-descendants are preserved.
      (∀ n, n ∈ mdb → ¬ IsDesc mdb n.capId targetId → n ∈ result) ∧
      -- (3) Result only contains nodes from the original MDB.
      (∀ n, n ∈ result → n ∈ mdb) ∧
      -- (4) Exact characterization: a node survives iff it is not a descendant.
      (∀ n, n ∈ result ↔ n ∈ mdb ∧ ¬ IsDesc mdb n.capId targetId) ∧
      -- (5) Well-formedness preserved.
      wellFormed result ∧
      -- (6) The result is a subsequence of the original MDB.
      result.Subseq mdb ∧
      -- (7) Revocation log contains exactly the removed capIds.
      (∀ id, id ∈ revoked ↔
        (∃ n, n ∈ mdb ∧ n.capId = id ∧ IsDesc mdb id targetId)) ∧
      -- (8) Exact length partition.
      (result.length + revoked.length = mdb.length) ∧
      -- (9) Idempotence: revoking again on the result state is a no-op.
      (∀ ks'', (revokeM targetId).run ks' = some ((), ks'') →
        ks''.mdb = result ∧ ks''.revLog = .nil) ∧
      -- (10) Determinism: the result depends only on the input MDB and targetId.
      (∀ ks₂ : KernelState, ks₂.mdb = mdb → ks₂.revLog = .nil →
        ∀ ks₂', (revokeM targetId).run ks₂ = some ((), ks₂') →
          ks₂'.mdb = result ∧ ks₂'.revLog = revoked) ∧
      -- (11) Bind-consistency: revoking two distinct targets in sequence
      --     is equivalent regardless of order (on disjoint descendant sets).
      (∀ tgt2 : Nat,
        (∀ id, ¬ (IsDesc mdb id targetId ∧ IsDesc mdb id tgt2)) →
        ∀ ks_ab ks_ba : KernelState,
          (KM.bind (revokeM targetId) (fun _ => revokeM tgt2)).run ks = some ((), ks_ab) →
          (KM.bind (revokeM tgt2) (fun _ => revokeM targetId)).run ks = some ((), ks_ba) →
          ks_ab.mdb = ks_ba.mdb)) := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4.CteRevoke
