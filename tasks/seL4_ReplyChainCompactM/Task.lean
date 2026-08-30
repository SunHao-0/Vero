/-
  Candidate seL4-style optimization task: reply chain compaction
  Source: models the seL4 MCS reply chain, src/object/reply.c (reply_push, reply_pop, reply_remove)

  This benchmark models a kernel reply chain (the linked list of reply objects
  threaded through a call stack) together with a secondary index mapping each
  thread id to its position in the chain. Over time entries get marked
  `cancelled` (the corresponding call was aborted) but remain physically linked.
  The optimization drops every cancelled entry from the chain and rebuilds the
  tid -> position index in a single pass so that lookups remain correct and no
  stale index entries survive.

  Correctness has three teeth. First, the surviving chain must be exactly the
  sublist of live (non-cancelled) entries, in their original order. Second, the
  rebuilt index must map every surviving tid to its NEW position in the
  compacted chain (positions shift down as cancelled entries are removed, so the
  old index is stale and must be recomputed). Third, the index must not retain
  any entry for a tid that no longer appears — dropping a cancelled entry must
  also retract its index slot, otherwise a later lookup would dereference a
  freed reply object.

  The thread ids occurring in the chain are assumed distinct (`h_nodup`); this
  is what makes "the position of tid t" well defined and the index a function.

  Expected solution style: a single traversal that filters out cancelled
  entries and recomputes the position index against the compacted chain.
-/
import Mathlib
import Std

namespace seL4Cand.ReplyChainCompactM

-- === BEGIN: DEFINITIONS (provided) ===

structure KM (σ α : Type) where
  run : σ → Option (α × σ)

def KM.ret {σ α : Type} (a : α) : KM σ α := ⟨fun s => some (a, s)⟩
def KM.bind {σ α β : Type} (ma : KM σ α) (f : α → KM σ β) : KM σ β :=
  ⟨fun s =>
    match ma.run s with
    | none => none
    | some (a, s') => (f a).run s'⟩
def KM.get {σ : Type} : KM σ σ := ⟨fun s => some (s, s)⟩
def KM.set {σ : Type} (s : σ) : KM σ Unit := ⟨fun _ => some ((), s)⟩
def KM.fail {σ α : Type} : KM σ α := ⟨fun _ => none⟩

@[simp] theorem KM.ret_run {σ α : Type} (a : α) (s : σ) :
    (KM.ret a).run s = some (a, s) := rfl
@[simp] theorem KM.get_run {σ : Type} (s : σ) :
    (KM.get).run s = some (s, s) := rfl
@[simp] theorem KM.set_run {σ : Type} (s s' : σ) :
    (KM.set s').run s = some ((), s') := rfl

def KM.modify {σ : Type} (f : σ → σ) : KM σ Unit := ⟨fun s => some ((), f s)⟩
@[simp] theorem KM.modify_run {σ : Type} (f : σ → σ) (s : σ) :
    (KM.modify f).run s = some ((), f s) := rfl

structure Entry where
  tid : Nat
  cancelled : Bool
  deriving DecidableEq, Repr

structure KernelState where
  chain : List Entry
  index : Nat → Option Nat

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

/-- An entry is live iff it is not cancelled. -/
def isLive : Entry → Bool := fun e => !e.cancelled

/-- Position of the first entry with the given tid in a chain, if present. -/
def posOf : List Entry → Nat → Option Nat
  | [], _ => none
  | e :: tl, t =>
      if e.tid = t then some 0
      else (posOf tl t).map (· + 1)

/-- A tid occurs in a chain. -/
def occurs (c : List Entry) (t : Nat) : Prop := ∃ e ∈ c, e.tid = t

/-- The number of live (surviving) entries in a chain. -/
def liveCount : List Entry → Nat
  | [] => 0
  | e :: tl => (if e.cancelled then 0 else 1) + liveCount tl

-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No additional axioms.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

def compactChainM : KM KernelState Unit :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem compactChainM_correct (st : KernelState)
    (h_nodup : (st.chain.map Entry.tid).Nodup) :
    (∃ st', compactChainM.run st = some ((), st')) ∧
    (∀ st', compactChainM.run st = some ((), st') →
      -- (a) exact characterization: the chain keeps exactly the live entries.
      st'.chain = st.chain.filter (fun e => isLive e) ∧
      -- (b) the rebuilt index points each surviving tid at its new position.
      (∀ t, occurs st'.chain t → st'.index t = posOf st'.chain t) ∧
      -- (c) no stale index entries: tids absent from the new chain map to none.
      (∀ t, ¬ occurs st'.chain t → st'.index t = none) ∧
      -- (d) the compacted chain has exactly the live-entry count of the input.
      st'.chain.length = liveCount st.chain) ∧
    (∀ s1 s2, compactChainM.run st = some ((), s1) → compactChainM.run st = some ((), s2) → s1 = s2) := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4Cand.ReplyChainCompactM
