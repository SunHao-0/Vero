/-
  seL4 Haskell Spec Optimization: PSpace placeNewObject'
  Original: O(n log n) — foldr of n individual inserts into balanced map
  Optimized: O(n) — fromAscList + left-biased sorted merge

  placeNewObject' inserts n new object entries at ascending addresses.
  The original folds insertSorted n times. Since addresses are ascending,
  we can build a sorted list directly and merge it with the existing map.

  Source: SEL4/Model/PSpace.lhs:215-223
-/
import Mathlib
import Std

namespace seL4.PSpacePlaceObject

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

def Seq.map {α : Type} {β : Type} (f : α → β) : Seq α → Seq β
  | .nil => .nil
  | .cons x xs => .cons (f x) (Seq.map f xs)

def Seq.filter {α : Type} (p : α → Bool) : Seq α → Seq α
  | .nil => .nil
  | .cons x xs => if p x then .cons x (Seq.filter p xs) else Seq.filter p xs

def Seq.any {α : Type} (p : α → Bool) : Seq α → Bool
  | .nil => false
  | .cons x xs => p x || Seq.any p xs

def Seq.find? {α : Type} (p : α → Bool) : Seq α → Option α
  | .nil => none
  | .cons x xs => if p x then some x else Seq.find? p xs



variable {α : Type}

/-- Sorted association list (models Data.Map). -/
abbrev OrdMap (α : Type) := Seq (Nat × α)

def isSortedMap : OrdMap α → Prop
  | .nil => True
  | .cons _ .nil => True
  | .cons (k1, _) (.cons (k2, v2) rest) =>
    k1 < k2 ∧ isSortedMap (.cons (k2, v2) rest)

/-- Lookup a value by key. -/
def mapLookup (m : OrdMap α) (k : Nat) : Option α :=
  (m.find? (fun (k', _) => k' == k)).map Prod.snd

/-- Range sequence: 0, 1, ..., n-1. -/
def range : Nat → Seq Nat
  | 0 => .nil
  | n + 1 => Seq.cons 0 ((range n).map (· + 1))

instance {α : Type} : Membership α (Seq α) where
  mem s a := @Seq.mem α a s


-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

/-- Addresses are strictly ascending. -/
def addrsAscending (ptr objSize count : Nat) : Prop :=
  objSize > 0 ∧ ∀ i j, i < j → j < count → ptr + i * objSize < ptr + j * objSize

-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No axioms.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

/-- Optimized: build sorted sequence from ascending addresses, merge with
    existing map. O(n+m) total. -/
def placeOptimized (m : OrdMap α) (ptr objSize : Nat) (count : Nat) (val : α) : OrdMap α :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem placeObject_correct {α : Type} (m : OrdMap α)
    (ptr objSize count : Nat) (val : α)
    (h_sorted : isSortedMap m)
    (h_asc : addrsAscending ptr objSize count) :
    let result := placeOptimized m ptr objSize count val
    -- (1) New addresses have the correct value.
    (∀ i, i < count →
      mapLookup result (ptr + i * objSize) = some val) ∧
    -- (2) Non-address keys are preserved.
    (∀ k, (∀ i, i < count → k ≠ ptr + i * objSize) →
      mapLookup result k = mapLookup m k) ∧
    -- (3) Result is sorted.
    isSortedMap result ∧
    -- (4) Idempotence: placing the same block twice equals placing it once.
    placeOptimized result ptr objSize count val = result ∧
    -- (5) Empty count is identity.
    (count = 0 → result = m) ∧
    -- (6) Lookup characterization: every key resolves to either the
    --     freshly written `val` or the original map value.
    (∀ k,
      mapLookup result k =
        if (range count).any (fun i => k == ptr + i * objSize)
        then some val
        else mapLookup m k) ∧
    -- (7) Structural size bounds: merge never shrinks below original map
    --     and never grows by more than the inserted block size.
    (m.length ≤ result.length ∧ result.length ≤ m.length + count) ∧
    -- (8) Prefix monotonicity in count: writes for a smaller count are
    --     preserved by a larger count on overlapping indices.
    (∀ c', c' ≤ count →
      let r' := placeOptimized m ptr objSize c' val
      ∀ i, i < c' →
        mapLookup result (ptr + i * objSize) =
        mapLookup r' (ptr + i * objSize)) ∧
    -- (9) Commutativity on disjoint write blocks with equal object size.
    (∀ ptr2 count2 val2,
      (∀ i, i < count → ∀ j, j < count2 →
        ptr + i * objSize ≠ ptr2 + j * objSize) →
      placeOptimized (placeOptimized m ptr objSize count val) ptr2 objSize count2 val2 =
      placeOptimized (placeOptimized m ptr2 objSize count2 val2) ptr objSize count val) := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4.PSpacePlaceObject
