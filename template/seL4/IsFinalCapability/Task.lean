/-
  seL4 Optimization Task: isFinalCapability — local ⇔ global uniqueness
  Source: src/object/cnode.c:846-874

  Naive: walk the entire MDB checking how many caps share `sameObjectAs`.
  Optimized: inspect only `mdbPrev` and `mdbNext`, exploiting the
             invariant that the MDB is ordered so adjacent caps in the
             same `sameObjectAs` equivalence class are contiguous.

  Prove the local check is equivalent to the global uniqueness
  property under the MDB-ordering invariant. This is a `local ⇔ global`
  proof and the most challenging in this benchmark.
-/
import Mathlib
import Std

namespace seL4.IsFinalCapability

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

def Seq.get {α : Type} : (s : Seq α) → (i : Nat) → i < s.length → α
  | .cons x _, 0, _ => x
  | .cons _ xs, n + 1, h => Seq.get xs n (by simp [length] at h; omega)

def Seq.filter {α : Type} (p : α → Bool) : Seq α → Seq α
  | .nil => .nil
  | .cons x xs => if p x then .cons x (Seq.filter p xs) else Seq.filter p xs

def Seq.append {α : Type} : Seq α → Seq α → Seq α
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (Seq.append xs ys)

instance {α : Type} : Membership α (Seq α) where
  mem s a := @Seq.mem α a s

instance {α : Type} : Append (Seq α) := ⟨@Seq.append α⟩





abbrev CapId := Nat

/-- A simplified cap with an "object key" used by `sameObjectAs`. -/
structure Cap where
  capId  : CapId
  objKey : Nat
  deriving DecidableEq, Repr

/-- Two caps are `sameObjectAs` iff they share the same object key. -/
def sameObjectAs (c c' : Cap) : Prop := c.objKey = c'.objKey

/-- The MDB is a sequence of caps in `mdbPrev → mdbNext` traversal order. -/
abbrev MDB := Seq Cap

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

/-- MDB-ordering invariant: caps with the same `objKey` are contiguous. -/
def mdbOrdered (mdb : MDB) : Prop :=
  ∀ i j : Nat, ∀ hi : i < mdb.length, ∀ hj : j < mdb.length, i < j →
    (mdb.get i hi).objKey = (mdb.get j hj).objKey →
    ∀ k : Nat, ∀ hk : k < mdb.length, i ≤ k → k ≤ j →
      (mdb.get k hk).objKey = (mdb.get i hi).objKey

/-- A cap is "globally final" iff it is the only one in its `sameObjectAs`
    equivalence class within the MDB. -/
def isGloballyFinal (mdb : MDB) (c : Cap) : Prop :=
  c ∈ mdb ∧ ∀ c', c' ∈ mdb → sameObjectAs c c' → c' = c

-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===
-- No axioms.
-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

/-- Locality witness. -/
structure LocalCheck where
  result    : Bool
  inspected : Seq Cap

/-- Local final-capability check: inspect only `mdbPrev` and `mdbNext`
    of `c` in the MDB list. -/
def isFinalLocal (mdb : MDB) (c : Cap) : LocalCheck :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

theorem isFinalLocal_correct (mdb : MDB) (c : Cap)
    (h_ord : mdbOrdered mdb)
    (h_mem : c ∈ mdb)
    (h_unique : (mdb.filter (fun c' => c'.capId == c.capId)).length = 1) :
    let lc := isFinalLocal mdb c
    -- (1) Local check ⇔ global uniqueness.
    (lc.result = true ↔ isGloballyFinal mdb c) ∧
    -- (2) Singleton MDB: a cap in a singleton list is always final.
    (mdb = .cons c .nil → lc.result = true ∧ lc.inspected = .nil) ∧
    -- (3) Adjacency soundness.
    (lc.result = true →
      ∀ c', c' ∈ mdb → c' ≠ c → c'.objKey ≠ c.objKey) ∧
    -- (4) Adjacency completeness.
    ((∃ c', c' ∈ mdb ∧ c' ≠ c ∧ c'.objKey = c.objKey) →
      lc.result = false) ∧
    -- (5) Insertion stability.
    (∀ c' : Cap, c'.capId ≠ c.capId →
      (∀ d, d ∈ mdb → d.objKey ≠ c'.objKey) →
      ∀ pre suf, mdb = pre ++ suf →
      let mdb' := pre ++ .cons c' suf
      mdbOrdered mdb' →
      (isFinalLocal mdb' c).result = lc.result) ∧
    -- (6) Removal stability.
    (∀ pre c' suf, mdb = pre ++ .cons c' suf → c'.objKey ≠ c.objKey →
      let mdb' := pre ++ suf
      mdbOrdered mdb' → c ∈ mdb' →
      (isFinalLocal mdb' c).result = lc.result) ∧
    -- (7) LOCALITY: inspected ≤ 2 elements.
    lc.inspected.length ≤ 2 ∧
    -- (8) LOCALITY: every inspected cap is an immediate neighbour.
    (∀ d, d ∈ lc.inspected →
      ∃ i j : Nat, ∃ hi : i < mdb.length, ∃ hj : j < mdb.length,
        mdb.get i hi = c ∧ mdb.get j hj = d ∧
        (j + 1 = i ∨ i + 1 = j)) ∧
    -- (9) LOCALITY: changing non-neighbours cannot change the result.
    (∀ mdb₂ : MDB, mdb₂.length = mdb.length →
      mdbOrdered mdb₂ → c ∈ mdb₂ →
      (mdb₂.filter (fun c' => c'.capId == c.capId)).length = 1 →
      (∀ i : Nat, ∀ h₁ : i < mdb.length, ∀ h₂ : i < mdb₂.length,
        (∀ k : Nat, ∀ hk₁ : k < mdb.length, mdb.get k hk₁ = c →
          i = k ∨ i + 1 = k ∨ k + 1 = i) →
        mdb.get i h₁ = mdb₂.get i h₂) →
      (isFinalLocal mdb₂ c).result = lc.result) ∧
    -- (10) Tight finite bound form of locality window size.
    (lc.inspected.length = 0 ∨ lc.inspected.length = 1 ∨ lc.inspected.length = 2) := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4.IsFinalCapability
