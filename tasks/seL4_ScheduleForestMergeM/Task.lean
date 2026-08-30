/-
  Candidate seL4-style optimization task: schedule-forest merge with weighted node accumulation
  Source: synthetic composite modeled on seL4 scheduling-state surgery (src/object/schedcontext.c, src/kernel/thread.c); no single upstream routine

  This benchmark is intentionally monadic and data-structure heavy.
  Expected solution style: recursive stateful transformation over
  a mixed trie/forest/adjacency state with interval summaries.
-/
import Mathlib
import Std

namespace seL4Cand.ScheduleForestMergeM

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

abbrev NodeId := Nat
abbrev Weight := Nat

inductive Trie where
  | empty : Trie
  | node : Nat → List Trie → Trie
  deriving Repr

structure Forest where
  roots : List NodeId
  child : NodeId → List NodeId

abbrev Adj := NodeId → List NodeId
abbrev IntervalMap := NodeId → Option (Nat × Nat)

structure WorkItem where
  id : NodeId
  key : Nat
  budget : Weight
  deriving DecidableEq, Repr

structure KernelState where
  trie : Trie
  forest : Forest
  adj : Adj
  ivals : IntervalMap
  score : NodeId → Weight
  active : NodeId → Bool

inductive Op where
  | touch (w : WorkItem)
  | merge (dst src : NodeId)
  | split (x : NodeId) (k : Nat)
  | relabel (x : NodeId) (tag : Nat)
  | drop (x : NodeId)
  deriving DecidableEq, Repr
-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

def trieWeight : Trie → Nat
  | .empty => 0
  | .node k cs => k + cs.foldl (fun acc t => acc + trieWeight t) 0

def forestNodes (f : Forest) (fuel : Nat) (x : NodeId) : Nat :=
  match fuel with
  | 0 => 0
  | Nat.succ n => 1 + (f.child x).foldl (fun acc y => acc + forestNodes f n y) 0

def wellFormedForest (f : Forest) : Prop :=
  ∀ r, r ∈ f.roots → f.child r ≠ []

def nonZeroIntervals (s : KernelState) : Prop :=
  ∀ i a b, s.ivals i = some (a, b) → b > 0

def opCost : Op → Nat
  | .touch w => w.budget + w.key
  | .merge _ _ => 3
  | .split _ k => k + 1
  | .relabel _ t => t + 1
  | .drop _ => 1

def batchCost : List Op → Nat := List.foldl (fun acc op => acc + opCost op) 0

def mentionsNode : Op → NodeId → Prop
  | .touch w, i => w.id = i
  | .merge dst src, i => dst = i ∨ src = i
  | .split x _, i => x = i
  | .relabel x _, i => x = i
  | .drop x, i => x = i

def mentionsAny (ops : List Op) (i : NodeId) : Prop := ∃ op, op ∈ ops ∧ mentionsNode op i

def touchBudgetAt (ops : List Op) (i : NodeId) : Nat :=
  match ops with
  | [] => 0
  | .touch w :: tl => (if w.id = i then w.budget + w.key else 0) + touchBudgetAt tl i
  | _ :: tl => touchBudgetAt tl i

def hasDrop (ops : List Op) (i : NodeId) : Prop := ∃ op, op ∈ ops ∧ op = .drop i

def hasMergePair (ops : List Op) (dst src : NodeId) : Prop := ∃ op, op ∈ ops ∧ op = .merge dst src

def hasSplitPair (ops : List Op) (x k : NodeId) : Prop := ∃ op, op ∈ ops ∧ op = .split x k

def hasRelabelPair (ops : List Op) (x tag : NodeId) : Prop := ∃ op, op ∈ ops ∧ op = .relabel x tag

def touchedRoot (ops : List Op) (r : NodeId) : Prop := ∃ w, .touch w ∈ ops ∧ w.id = r

def removedRoot (ops : List Op) (r : NodeId) : Prop := hasDrop ops r ∨ ∃ dst, hasMergePair ops dst r

/-- Conflict-free `ops`: no two operations target the same node in
    mutually contradictory ways. Required to make the post-conditions
    of `mergeForestM_correct` simultaneously satisfiable. -/
def noConflictingOps (ops : List Op) : Prop :=
  (∀ r, ¬(touchedRoot ops r ∧ removedRoot ops r)) ∧
  (∀ x tag, hasDrop ops x → ¬hasRelabelPair ops x tag) ∧
  (∀ dst src tag, hasMergePair ops dst src → ¬hasRelabelPair ops src tag) ∧
  (∀ x k, hasDrop ops x → ¬hasSplitPair ops x k) ∧
  (∀ dst src k, hasMergePair ops dst src → ¬hasSplitPair ops src k) ∧
  (∀ x t1 t2, hasRelabelPair ops x t1 → hasRelabelPair ops x t2 → t1 = t2) ∧
  (∀ dst1 dst2 src, hasMergePair ops dst1 src → hasMergePair ops dst2 src → dst1 = dst2)
-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- no axioms
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

def mergeForestM (ops : List Op) : KM KernelState Unit :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem mergeForestM_correct (ops : List Op) (st : KernelState)
    (h_forest : wellFormedForest st.forest)
    (h_intervals : nonZeroIntervals st)
    (h_noconfl : noConflictingOps ops) :
    (∃ st', (mergeForestM ops).run st = some ((), st')) ∧
    (∀ st', (mergeForestM ops).run st = some ((), st') →
      nonZeroIntervals st' ∧
      (ops = [] → st' = st) ∧
      (∀ i, ¬mentionsAny ops i → st'.score i = st.score i ∧ st'.active i = st.active i) ∧
      (∀ i, touchBudgetAt ops i > 0 → st'.score i ≥ st.score i + touchBudgetAt ops i) ∧
      (∀ i, hasDrop ops i → st'.active i = false ∧ st'.ivals i = none ∧ st'.adj i = []) ∧
      (∀ dst src, hasMergePair ops dst src → ∀ j, j ∈ st.forest.child src → j ∈ st'.forest.child dst) ∧
      (∀ x k, hasSplitPair ops x k → k ∈ st'.forest.child x) ∧
      (∀ x tag, hasRelabelPair ops x tag → st'.adj x ≠ [] ∧ List.head? (st'.adj x) = some tag) ∧
      (∀ r, touchedRoot ops r → r ∈ st'.forest.roots) ∧
      (∀ r, removedRoot ops r → r ∉ st'.forest.roots) ∧
      (batchCost ops > 0 → trieWeight st'.trie > trieWeight st.trie) ∧
      (∀ r, r ∈ st'.forest.roots → forestNodes st'.forest (batchCost ops + 1) r > 0)) ∧
    (∀ s1 s2, (mergeForestM ops).run st = some ((), s1) → (mergeForestM ops).run st = some ((), s2) → s1 = s2) := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4Cand.ScheduleForestMergeM
