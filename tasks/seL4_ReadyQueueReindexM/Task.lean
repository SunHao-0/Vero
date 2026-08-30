/-
  Candidate seL4-style optimization task: ready queue reindexing
  Source: models the seL4 ready queues, src/object/tcb.c (tcbSchedEnqueue, tcbSchedDequeue); ksReadyQueues

  A priority remapping `f` is applied to the scheduler's ready-queue
  array (and its summary bitmap): the queue and bit that lived at
  priority `p` move to priority `f p`. The remap is required to send the
  in-bounds range into itself (`f p < prioBound` for `p < prioBound`) and
  to be injective on that range, which makes it a permutation of the
  in-bounds priorities. Indices at or above the bound are left untouched.

  This benchmark is intentionally monadic and data-structure heavy.
  Expected solution style: recursive stateful permutation of a
  per-priority queue array and its companion bitmap.
-/
import Mathlib
import Std

namespace seL4Cand.ReadyQueueReindexM

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

/-- `f` maps the in-bounds priority range into itself. -/
def mapsInBounds (s : KernelState) (f : Nat → Nat) : Prop :=
  ∀ p, p < s.prioBound → f p < s.prioBound

/-- `f` is injective on the in-bounds priority range. -/
def injOnBound (s : KernelState) (f : Nat → Nat) : Prop :=
  ∀ p q, p < s.prioBound → q < s.prioBound → f p = f q → p = q
-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No additional axioms.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

def reindexM (f : Nat → Nat) : KM KernelState Unit :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem reindexM_correct (f : Nat → Nat) (st : KernelState)
    (h_maps : mapsInBounds st f)
    (h_inj : injOnBound st f) :
    (∃ st', (reindexM f).run st = some ((), st')) ∧
    (∀ st', (reindexM f).run st = some ((), st') →
      -- Each in-bounds queue moves to its remapped index.
      (∀ p, p < st.prioBound → st'.queues (f p) = st.queues p) ∧
      -- Each in-bounds bit moves to its remapped index.
      (∀ p, p < st.prioBound → st'.bitmap (f p) = st.bitmap p) ∧
      -- Frame: out-of-bounds queue slots are unchanged.
      (∀ p, st.prioBound ≤ p → st'.queues p = st.queues p) ∧
      -- Frame: out-of-bounds bitmap slots are unchanged.
      (∀ p, st.prioBound ≤ p → st'.bitmap p = st.bitmap p) ∧
      -- Frame: the priority bound is unchanged.
      (st'.prioBound = st.prioBound)) ∧
    (∀ s1 s2, (reindexM f).run st = some ((), s1) → (reindexM f).run st = some ((), s2) → s1 = s2) := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4Cand.ReadyQueueReindexM
