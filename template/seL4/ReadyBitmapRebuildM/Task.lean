/-
  Candidate seL4-style optimization task: ready bitmap rebuild
  Source: models the seL4 scheduler bitmap, src/object/tcb.c (addToBitmap, removeFromBitmap); ksReadyQueuesL1Bitmap

  The scheduler keeps, alongside the per-priority ready queues, a summary
  bitmap whose `p`-th bit records whether priority level `p` has any
  runnable thread. After bulk queue surgery this bitmap can become stale
  or inconsistent. The `rebuildM` operation recomputes the bitmap (for
  every priority below `prioBound`) directly from the current queues,
  leaving the queues themselves untouched. It takes no arguments — the
  whole bitmap is reconstructed unconditionally, so the identity
  transformation is incorrect whenever the input bitmap is stale.

  This benchmark is intentionally monadic and data-structure heavy.
  Expected solution style: recursive stateful recomputation of a summary
  bitmap from the underlying ready queues.
-/
import Mathlib
import Std

namespace seL4Cand.ReadyBitmapRebuildM

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
def KM.modify {σ : Type} (f : σ → σ) : KM σ Unit := ⟨fun s => some ((), f s)⟩
def KM.fail {σ α : Type} : KM σ α := ⟨fun _ => none⟩

@[simp] theorem KM.ret_run {σ α : Type} (a : α) (s : σ) :
    (KM.ret a).run s = some (a, s) := rfl
@[simp] theorem KM.bind_run {σ α β : Type} (ma : KM σ α) (f : α → KM σ β) (s : σ) :
    (KM.bind ma f).run s =
      (match ma.run s with
       | none => none
       | some (a, s') => (f a).run s') := rfl
@[simp] theorem KM.get_run {σ : Type} (s : σ) : (KM.get).run s = some (s, s) := rfl
@[simp] theorem KM.set_run {σ : Type} (s s' : σ) : (KM.set s').run s = some ((), s') := rfl
@[simp] theorem KM.modify_run {σ : Type} (f : σ → σ) (s : σ) :
    (KM.modify f).run s = some ((), f s) := rfl

abbrev Prio := Nat
abbrev Tid := Nat

structure KernelState where
  queues : Prio → List Tid
  bitmap : Prio → Bool
  prioBound : Nat

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

/-- A priority level is occupied when its ready queue is nonempty. -/
def occupied (s : KernelState) (p : Prio) : Prop := s.queues p ≠ []
-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No additional axioms.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

def rebuildM : KM KernelState Unit :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem rebuildM_correct (st : KernelState) :
    (∃ st', (rebuildM).run st = some ((), st')) ∧
    (∀ st', (rebuildM).run st = some ((), st') →
      -- Exact characterization: below the bound a bit is set iff the queue is nonempty.
      (∀ p, p < st.prioBound → (st'.bitmap p = true ↔ st.queues p ≠ [])) ∧
      -- Frame: queues are never modified.
      (∀ p, st'.queues p = st.queues p) ∧
      -- Frame: the priority bound is unchanged.
      (st'.prioBound = st.prioBound) ∧
      -- Frame: bits at or above the bound are unchanged.
      (∀ p, st.prioBound ≤ p → st'.bitmap p = st.bitmap p)) ∧
    (∀ s1 s2, (rebuildM).run st = some ((), s1) → (rebuildM).run st = some ((), s2) → s1 = s2) := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4Cand.ReadyBitmapRebuildM
