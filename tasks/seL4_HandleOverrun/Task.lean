/-
  seL4 Optimization Task: handle_overrun — sporadic refill convergence
  Source: src/kernel/sporadic.c:272-291

  Naive: while (head_refill_overrun) charge_entire_head_refill — repeated
         single-step charging.
  Optimized: closed-form `k = min(usage / headAmount, room)` step computing
             how many head refills to consume in one shot.

  No reference loop is provided. The closed-form must satisfy
  the same fixpoint property and pass the explicit witness invariants.
-/
import Mathlib
import Std

namespace seL4.HandleOverrun

-- === BEGIN: DEFINITIONS (provided) ===



/-- Custom sequence type (no Mathlib automation). -/
inductive Seq (α : Type) where
  | nil : Seq α
  | cons : α → Seq α → Seq α
  deriving Repr


def Seq.mem {α : Type} (a : α) : Seq α → Prop
  | .nil => False
  | .cons x xs => a = x ∨ Seq.mem a xs


def Seq.length {α : Type} : Seq α → Nat
  | .nil => 0
  | .cons _ xs => xs.length + 1

/-- `xs` is a suffix of `ys`. -/
inductive Seq.IsSuffix {α : Type} : Seq α → Seq α → Prop where
  | refl (xs : Seq α) : IsSuffix xs xs
  | drop (x : α) {xs ys : Seq α} : IsSuffix xs ys → IsSuffix xs (.cons x ys)

instance {α : Type} : Membership α (Seq α) where
  mem s a := @Seq.mem α a s


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

-- Seq API lemmas (proved before sealing)
theorem Seq.mem_nil {α : Type} (a : α) : a ∈ (Seq.nil : Seq α) ↔ False := by
  constructor <;> intro h <;> exact h.elim
theorem Seq.mem_cons {α : Type} (a x : α) (xs : Seq α) :
    a ∈ Seq.cons x xs ↔ a = x ∨ a ∈ xs := Iff.rfl

-- Seal Seq operations
attribute [irreducible] Seq.mem Seq.length

/-- A refill entry: (release time, amount). -/
structure Refill where
  rTime   : Nat
  rAmount : Nat
  deriving DecidableEq, Repr

/-- A refill list (modeling the circular buffer's logical view). -/
abbrev RefillList := Seq Refill

/-- Sum of refill amounts. -/
def refillSum : RefillList → Nat
  | .nil => 0
  | .cons r rs => r.rAmount + refillSum rs

/-- Kernel state for overrun handling. -/
structure OverrunState where
  refills : RefillList
  leftover : Nat

/-- A single charge step: if the head refill is fully consumed by the
    remaining usage, drop it and subtract its amount from usage. -/
def chargeStep : RefillList × Nat → RefillList × Nat
  | (.nil, u) => (.nil, u)
  | (.cons r rs, u) =>
    if r.rAmount ≤ u then (rs, u - r.rAmount)
    else (.cons r rs, u)

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

/-- A refill list is "in overrun" against `usage` if the head is wholly
    consumed by `usage`. -/
def headOverrun (usage : Nat) : RefillList → Prop
  | .nil => False
  | .cons r _ => r.rAmount ≤ usage

/-- `k` charging steps reach a non-overrun fixpoint from `(rs, usage)`. -/
def reachesFixpoint (k : Nat) (rs : RefillList) (usage : Nat) : Prop :=
  let out := Nat.iterate chargeStep k (rs, usage)
  ¬ headOverrun out.2 out.1

/-- `k` is the first step count that reaches a non-overrun fixpoint. -/
def minimalFixpointK (k : Nat) (rs : RefillList) (usage : Nat) : Prop :=
  reachesFixpoint k rs usage ∧
  ∀ j, j < k → ¬ reachesFixpoint j rs usage

/-- Number of head entries removed when transitioning from `before` to `after`.
    Defined only via lengths because `after` is required to be a suffix of `before`. -/
def removedCount (before after : RefillList) : Nat :=
  before.length - after.length

-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No axioms.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

/-- Closed-form overrun handler: given `usage`, charge as many whole
    head refills as needed in one step. Operates monadically over
    OverrunState, consuming refills and recording leftover usage. -/
def handleOverrunM (usage : Nat) : KM OverrunState Unit :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem handleOverrunM_correct (usage : Nat) (os : OverrunState)
    (h_pos : ∀ r, r ∈ os.refills → r.rAmount > 0) :
    -- Non-failure: the computation always succeeds.
    (handleOverrunM usage).run os ≠ none ∧
    -- For the resulting state:
    ∀ os', (handleOverrunM usage).run os = some ((), os') →
    -- (1) The leftover usage no longer overruns the new head (or list empty).
    (¬ headOverrun os'.leftover os'.refills) ∧
    -- (2) Sum identity: amounts removed equal the consumed usage portion.
    (refillSum os.refills = refillSum os'.refills + (usage - os'.leftover)) ∧
    -- (3) The leftover never exceeds the original usage.
    os'.leftover ≤ usage ∧
    -- (4) Result is a suffix of the original list (only head entries removed).
    os'.refills.IsSuffix os.refills ∧
    -- (5) Closed-form witness: there exists a bounded minimal step-count `k`
    --     such that exactly `k` iterations reach this result.
    (∃ k : Nat,
      k ≤ usage ∧
      Nat.iterate chargeStep k (os.refills, usage) = (os'.refills, os'.leftover) ∧
      minimalFixpointK k os.refills usage) ∧
    -- (6) The minimal witness is unique.
    (∀ k1 k2,
      minimalFixpointK k1 os.refills usage →
      minimalFixpointK k2 os.refills usage →
      k1 = k2) ∧
    -- (7) Witness-step count equals the number of removed head entries.
    (∀ k,
      minimalFixpointK k os.refills usage →
      k = removedCount os.refills os'.refills) ∧
    -- (8) Idempotence: applying `handleOverrunM os'.leftover` on the result state is a no-op.
    (handleOverrunM os'.leftover).run os' = some ((), os') ∧
    -- (9) When `usage = 0`, refills are unchanged and leftover is zero.
    (usage = 0 → os'.refills = os.refills ∧ os'.leftover = 0) ∧
    -- (10) Determinism: result depends only on refills content.
    (∀ os2 : OverrunState, os2.refills = os.refills →
      (handleOverrunM usage).run os2 = some ((), { refills := os'.refills, leftover := os'.leftover })) ∧
    -- (11) Bind-consistency: sequential handleOverrunM preserves sum identity.
    (∀ u2 : Nat,
      ∀ os'' : OverrunState,
        (KM.bind (handleOverrunM usage) (fun _ => handleOverrunM u2)).run os = some ((), os'') →
        refillSum os.refills = refillSum os''.refills + (usage - os'.leftover) + (u2 - os''.leftover)) ∧
    -- (12) Suffix shape implies non-increasing refill-list length.
    os'.refills.length ≤ os.refills.length := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4.HandleOverrun
