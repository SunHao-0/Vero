/-
  Candidate seL4-style optimization task: CNode guard compression
  Source: models seL4 CSpace resolution, src/kernel/cspace.c (resolveAddressBits); CNode guard/radix capabilities, src/object/cnode.c

  This benchmark models the seL4 capability-space resolution path as a list
  of segments. Each segment carries a guard (a fixed sequence of bits matched
  and skipped during lookup) and a radix (the number of bits consumed by a
  table-indexed step). A "pure guard" segment is one whose radix is zero: it
  contributes only matched guard bits and forces an extra table access without
  consuming any index bits. The optimization fuses each such pure-guard segment
  into its successor, prepending its guard bits, so that one fewer table access
  is performed while the decoded bit sequence is preserved.

  Expected solution style: a single left-to-right fold over the segment list
  that, whenever it sees a zero-radix segment, defers its guard bits and merges
  them into the next segment via `fuse`.
-/
import Mathlib
import Std

namespace seL4Cand.CNodeGuardCompressM

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

structure Seg where
  guard : List Bool
  radix : Nat
  deriving DecidableEq, Repr

structure KernelState where
  path : List Seg

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

/-- One table access per segment. -/
def cost : List Seg → Nat := fun p => p.length

/-- Bits accounted for by a single segment: matched guard bits plus index bits. -/
def bitsOf : Seg → Nat := fun s => s.guard.length + s.radix

/-- Total bits accounted for by the whole resolution path. -/
def totalBits : List Seg → Nat := fun p => (p.map bitsOf).sum

/-- The legal rewrite: a pure-guard segment (radix 0) folds into its
    successor, prepending its guard bits. Non-pure segments cannot be fused. -/
def fuse : Seg → Seg → Option Seg :=
  fun a b => if a.radix = 0 then some { guard := a.guard ++ b.guard, radix := b.radix } else none

/-- Semantic trace of a single segment: its guard bits (as `inl`) followed by
    a single radix marker (as `inr`). -/
def segTrace : Seg → List (Bool ⊕ Nat) :=
  fun s => s.guard.map Sum.inl ++ [Sum.inr s.radix]

/-- Semantic trace of the whole path. -/
def trace : List Seg → List (Bool ⊕ Nat) :=
  fun p => (p.map segTrace).flatten

/-- Normalize a trace by dropping `inr 0` markers: a zero-radix step performs
    no table index step, so it is invisible to the decoded bit sequence. -/
def normTrace : List (Bool ⊕ Nat) → List (Bool ⊕ Nat)
  | [] => []
  | Sum.inr 0 :: tl => normTrace tl
  | x :: tl => x :: normTrace tl

-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No additional axioms.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

def compressM : KM KernelState Unit :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem compressM_correct (st : KernelState) :
    (∃ st', compressM.run st = some ((), st')) ∧
    (∀ st', compressM.run st = some ((), st') →
      -- (a) total accounted bits are preserved (no bit is gained or lost).
      totalBits st'.path = totalBits st.path ∧
      -- (b) the decoded bit sequence is preserved up to elided zero-radix steps.
      normTrace (trace st'.path) = normTrace (trace st.path) ∧
      -- (c) full compression: no pure-guard segment remains except a possible
      --     trailing one (a final pure guard has no successor to fold into).
      (∀ s ∈ st'.path.dropLast, s.radix ≠ 0) ∧
      -- (d) cost consequence: the compressed path is no longer than the input.
      st'.path.length ≤ st.path.length ∧
      -- (e) conservativity: a non-empty path never compresses to empty.
      (st.path ≠ [] → st'.path ≠ [])) ∧
    (∀ s1 s2, compressM.run st = some ((), s1) → compressM.run st = some ((), s2) → s1 = s2) := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4Cand.CNodeGuardCompressM
