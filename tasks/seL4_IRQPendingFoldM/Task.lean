/-
  Candidate seL4-style optimization task: IRQ pending-bit fold into a dispatch list
  Source: models seL4 interrupt handling, src/object/interrupt.c (handleInterrupt); per-IRQ pending/mask state

  This benchmark models the kernel's interrupt scan loop. The controller keeps a
  per-IRQ pending bit (`pending : Irq → Bool`) over a fixed range `[0, irqBound)`
  together with a per-IRQ mask (`masked : Irq → Bool`). One pass of the fold walks
  the IRQ range in ascending order, and for every IRQ that is BOTH pending and
  unmasked it appends the IRQ number to a batch; this batch is then prepended to
  the existing `dispatch` queue (newest scan first, ascending within the scan).
  Unmasked pendings are cleared (acknowledged) while masked pendings are RETAINED
  so they remain latched until the mask is lifted. The mask map and any pending
  bits at or above the bound are untouched.

  Expected solution style: a single deterministic pass over `List.range irqBound`,
  building the filtered ascending batch and rewriting the pending function.
-/
import Mathlib
import Std

namespace seL4Cand.IRQPendingFoldM

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
@[simp] theorem KM.set_run {σ : Type} (s s' : σ) : (KM.set s).run s' = some ((), s) := rfl
@[simp] theorem KM.modify_run {σ : Type} (f : σ → σ) (s : σ) :
    (KM.modify f).run s = some ((), f s) := rfl

abbrev Irq := Nat

structure KernelState where
  pending : Irq → Bool
  masked : Irq → Bool
  dispatch : List Irq
  irqBound : Nat
-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

/-- The ascending batch produced by one fold: every IRQ below the bound that is
    pending and unmasked, in increasing order. -/
def foldBatch (st : KernelState) : List Irq :=
  (List.range st.irqBound).filter (fun i => st.pending i && !st.masked i)

/-- Pending bit after the fold for an IRQ below the bound: unmasked pendings are
    acknowledged (cleared), masked pendings stay latched. -/
def clearedPending (st : KernelState) (i : Irq) : Bool := st.pending i && st.masked i
-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No additional axioms.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

def foldPendingM : KM KernelState Unit :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem foldPendingM_correct (st : KernelState) :
    (∃ st', foldPendingM.run st = some ((), st')) ∧
    (∀ st', foldPendingM.run st = some ((), st') →
      -- (a) Exact dispatch characterization: ascending unmasked-pending batch prepended.
      (st'.dispatch =
        (List.range st.irqBound).filter (fun i => st.pending i && !st.masked i) ++ st.dispatch) ∧
      -- (b) Cleared: below the bound, unmasked pendings are cleared, masked retained.
      (∀ i, i < st.irqBound → st'.pending i = (st.pending i && st.masked i)) ∧
      -- (c) Frame: pending bits at or above the bound are unchanged.
      (∀ i, st.irqBound ≤ i → st'.pending i = st.pending i) ∧
      -- (d) Frame: the mask map is never modified.
      (∀ i, st'.masked i = st.masked i) ∧
      -- (e) The IRQ bound is unchanged.
      st'.irqBound = st.irqBound) ∧
    (∀ s1 s2, foldPendingM.run st = some ((), s1) → foldPendingM.run st = some ((), s2) → s1 = s2) := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4Cand.IRQPendingFoldM
