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
  KM.modify (fun ks =>
    let mdb := ks.mdb
    let fuel := revokeM.mdbLen mdb
    let isDesc := fun cid => revokeM.descCheck targetId cid mdb fuel
    { mdb := revokeM.filterKeep mdb isDesc
      revLog := revokeM.filterRevLog mdb isDesc })
  where
    mdbLen : MDB → Nat
      | .nil => 0
      | .cons _ rest => mdbLen rest + 1
    findParent (mdb : MDB) (id : Nat) : Option Nat :=
      match mdb with
      | .nil => none
      | .cons node rest =>
        if node.capId == id then node.parentId
        else findParent rest id
    descCheck (target cid : Nat) (mdb : MDB) : Nat → Bool
      | 0 => false
      | fuel + 1 =>
        match findParent mdb cid with
        | none => false
        | some pid => (pid == target) || descCheck target pid mdb fuel
    filterKeep (mdb : MDB) (f : Nat → Bool) : MDB :=
      match mdb with
      | .nil => .nil
      | .cons node rest =>
        if f node.capId then filterKeep rest f
        else .cons node (filterKeep rest f)
    filterRevLog (mdb : MDB) (f : Nat → Bool) : Seq Nat :=
      match mdb with
      | .nil => .nil
      | .cons node rest =>
        if f node.capId then .cons node.capId (filterRevLog rest f)
        else filterRevLog rest f
-- === END: IMPLEMENTATION ===

-- ===== BEGIN AUX LEMMAS (helper gap) =====

-- Equational lemmas for revokeM helpers

private lemma mdbLen_nil : revokeM.mdbLen (Seq.nil : MDB) = 0 := rfl
private lemma mdbLen_cons (n : CapNode) (rest : MDB) :
    revokeM.mdbLen (Seq.cons n rest) = revokeM.mdbLen rest + 1 := rfl

private lemma findParent_nil (id : Nat) :
    revokeM.findParent (Seq.nil : MDB) id = none := rfl
private lemma findParent_cons (node : CapNode) (rest : MDB) (id : Nat) :
    revokeM.findParent (Seq.cons node rest) id =
    if node.capId == id then node.parentId else revokeM.findParent rest id := rfl

private lemma descCheck_zero (target cid : Nat) (mdb : MDB) :
    revokeM.descCheck target cid mdb 0 = false := rfl
private lemma descCheck_succ (target cid : Nat) (mdb : MDB) (fuel : Nat) :
    revokeM.descCheck target cid mdb (fuel + 1) =
    match revokeM.findParent mdb cid with
    | none => false
    | some pid => (pid == target) || revokeM.descCheck target pid mdb fuel := rfl

private lemma filterKeep_nil (f : Nat → Bool) :
    revokeM.filterKeep (Seq.nil : MDB) f = Seq.nil := rfl
private lemma filterKeep_cons (node : CapNode) (rest : MDB) (f : Nat → Bool) :
    revokeM.filterKeep (Seq.cons node rest) f =
    if f node.capId then revokeM.filterKeep rest f
    else Seq.cons node (revokeM.filterKeep rest f) := rfl

private lemma filterRevLog_nil (f : Nat → Bool) :
    revokeM.filterRevLog (Seq.nil : MDB) f = Seq.nil := rfl
private lemma filterRevLog_cons (node : CapNode) (rest : MDB) (f : Nat → Bool) :
    revokeM.filterRevLog (Seq.cons node rest) f =
    if f node.capId then Seq.cons node.capId (revokeM.filterRevLog rest f)
    else revokeM.filterRevLog rest f := rfl

-- Seq.length equational lemmas (Seq.length is irreducible but can be unfolded)
private lemma seqLen_nil {α : Type} : (Seq.nil : Seq α).length = 0 := by
  simp only [Seq.length]
private lemma seqLen_cons {α : Type} (x : α) (xs : Seq α) :
    (Seq.cons x xs).length = xs.length + 1 := by
  simp only [Seq.length]

-- findParent correctness
private lemma findParent_some_mem {mdb : MDB} {id pid : Nat}
    (h : revokeM.findParent mdb id = some pid) :
    ∃ node ∈ mdb, node.capId = id ∧ node.parentId = some pid := by
  induction mdb with
  | nil => simp [findParent_nil] at h
  | cons n rest ih =>
    rw [findParent_cons] at h
    split_ifs at h with hif
    · exact ⟨n, (Seq.mem_cons _ _ _).mpr (Or.inl rfl), beq_iff_eq.mp hif, h⟩
    · obtain ⟨node, hmem, hcap, hpar⟩ := ih h
      exact ⟨node, (Seq.mem_cons _ _ _).mpr (Or.inr hmem), hcap, hpar⟩

-- With uniqueIds, findParent returns the parent of the unique node with that capId
private lemma findParent_of_mem {mdb : MDB} {node : CapNode}
    (hmem : node ∈ mdb) (huniq : uniqueIds mdb) :
    revokeM.findParent mdb node.capId = node.parentId := by
  induction mdb with
  | nil => exact absurd hmem (Seq.mem_nil _ |>.mp)
  | cons n rest ih =>
    rw [Seq.mem_cons] at hmem
    rw [findParent_cons]
    unfold uniqueIds Seq.Pairwise at huniq
    cases hmem with
    | inl h =>
      subst h
      simp
    | inr h =>
      by_cases heq : n.capId == node.capId
      · -- n.capId = node.capId, but uniqueIds requires they differ since node ∈ rest
        have hne : n.capId ≠ node.capId := by
          have := huniq.1 node h
          exact this
        exact absurd (beq_iff_eq.mp heq) hne
      · simp [heq]
        exact ih h huniq.2

-- descCheck soundness: if descCheck says true, then IsDesc holds
private lemma descCheck_sound {target cid : Nat} {mdb : MDB} {fuel : Nat}
    (h : revokeM.descCheck target cid mdb fuel = true) :
    IsDesc mdb cid target := by
  induction fuel generalizing cid with
  | zero => simp [descCheck_zero] at h
  | succ n ih =>
    rw [descCheck_succ] at h
    match hfp : revokeM.findParent mdb cid with
    | none => simp [hfp] at h
    | some pid =>
      simp [hfp] at h
      obtain ⟨node, hmem, hcap, hpar⟩ := findParent_some_mem hfp
      rcases h with hpid | hrec
      · subst hpid
        exact IsDesc.child node cid pid hmem hcap hpar
      · have hcid_pid : IsDesc mdb cid pid := IsDesc.child node cid pid hmem hcap hpar
        have hpid_target : IsDesc mdb pid target := ih hrec
        exact IsDesc.trans cid pid target hcid_pid hpid_target

-- Monotonicity: more fuel still works
private lemma descCheck_mono_simple : ∀ (target cid : Nat) (mdb : MDB) (fuel : Nat),
    revokeM.descCheck target cid mdb fuel = true →
    revokeM.descCheck target cid mdb (fuel + 1) = true := by
  intro target cid mdb fuel h
  induction fuel generalizing cid with
  | zero => simp [descCheck_zero] at h
  | succ n ih =>
    rw [descCheck_succ] at h ⊢
    match hfp : revokeM.findParent mdb cid with
    | none => simp [hfp] at h
    | some pid =>
      simp [hfp] at h ⊢
      rcases h with hpid | hrec
      · simp [hpid]
      · right; exact ih pid hrec

private lemma descCheck_mono_le : ∀ (target cid : Nat) (mdb : MDB) (fuel fuel' : Nat),
    fuel ≤ fuel' →
    revokeM.descCheck target cid mdb fuel = true →
    revokeM.descCheck target cid mdb fuel' = true := by
  intro target cid mdb fuel fuel' hle h
  induction hle with
  | refl => exact h
  | step _ ih => exact descCheck_mono_simple target cid mdb _ ih

-- descCheck transitivity
private lemma descCheck_trans : ∀ (mid target cid : Nat) (mdb : MDB) (k1 k2 : Nat),
    revokeM.descCheck mid cid mdb k1 = true →
    revokeM.descCheck target mid mdb k2 = true →
    revokeM.descCheck target cid mdb (k1 + k2) = true := by
  intro mid target cid mdb k1 k2 h1 h2
  induction k1 generalizing cid with
  | zero => simp [descCheck_zero] at h1
  | succ n ih =>
    rw [descCheck_succ] at h1
    match hfp : revokeM.findParent mdb cid with
    | none => simp [hfp] at h1
    | some pid =>
      simp [hfp] at h1
      rcases h1 with hpid | hrec
      · -- pid = mid
        subst hpid
        -- descCheck target cid mdb (n+1 + k2)
        rw [show n + 1 + k2 = n + k2 + 1 from by ring]
        rw [descCheck_succ, hfp]
        simp
        -- need: (pid == target) || descCheck target pid mdb (n + k2) = true
        -- pid = mid, and descCheck target mid mdb k2 = true
        -- use mono to get descCheck target mid mdb (n + k2) = true
        exact Or.inr (descCheck_mono_le target pid mdb k2 (n + k2) (Nat.le_add_left _ _) h2)
      · -- descCheck mid pid mdb n = true
        have ihres := ih pid hrec
        rw [show n + k2 = n + k2 from rfl] at ihres
        rw [show n + 1 + k2 = n + k2 + 1 from by ring]
        rw [descCheck_succ, hfp]
        simp
        right
        exact ihres

-- IsDesc implies path via findParent exists (key completeness lemma)
private lemma IsDesc_to_descCheck : ∀ (mdb : MDB) (target cid : Nat),
    IsDesc mdb cid target →
    uniqueIds mdb →
    ∃ k, revokeM.descCheck target cid mdb k = true := by
  intro mdb target cid hd huniq
  induction hd with
  | child node cid aId hmem hcap hpar =>
    use 1
    rw [descCheck_succ]
    have hfp := findParent_of_mem (mdb := mdb) hmem huniq
    rw [hcap] at hfp
    rw [hpar] at hfp
    rw [hfp]
    simp
  | trans cid mid aId h1 h2 ih1 ih2 =>
    obtain ⟨k1, hk1⟩ := ih1
    obtain ⟨k2, hk2⟩ := ih2
    exact ⟨k1 + k2, descCheck_trans mid aId cid mdb k1 k2 hk1 hk2⟩

-- First, prove that if a chain exists (descCheck k = true), the capIds visited are in mdb
private lemma descCheck_visits_in_mdb : ∀ (target cid : Nat) (mdb : MDB) (fuel : Nat),
    revokeM.descCheck target cid mdb fuel = true →
    ∃ node ∈ mdb, node.capId = cid := by
  intro target cid mdb fuel h
  induction fuel generalizing cid with
  | zero => simp [descCheck_zero] at h
  | succ n ih =>
    rw [descCheck_succ] at h
    match hfp : revokeM.findParent mdb cid with
    | none => simp [hfp] at h
    | some pid =>
      obtain ⟨node, hmem, hcap, _⟩ := findParent_some_mem hfp
      exact ⟨node, hmem, hcap⟩

-- filterKeep membership
private lemma filterKeep_mem_iff {mdb : MDB} {f : Nat → Bool} {n : CapNode} :
    n ∈ revokeM.filterKeep mdb f ↔ n ∈ mdb ∧ f n.capId = false := by
  induction mdb with
  | nil =>
    simp [filterKeep_nil, Seq.mem_nil]
  | cons node rest ih =>
    rw [filterKeep_cons, Seq.mem_cons]
    cases hf : f node.capId with
    | true =>
      simp only [↓reduceIte, ih]
      constructor
      · rintro ⟨hmem, hfc⟩
        exact ⟨Or.inr hmem, hfc⟩
      · rintro ⟨hmem | hmem, hfc⟩
        · subst hmem; rw [hf] at hfc; exact absurd hfc (by decide)
        · exact ⟨hmem, hfc⟩
    | false =>
      simp only [Bool.false_eq_true, ite_false, Seq.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨hmem, hfc⟩)
        · exact ⟨Or.inl rfl, hf⟩
        · exact ⟨Or.inr hmem, hfc⟩
      · rintro ⟨hmem | hmem, hfc⟩
        · subst hmem; exact Or.inl rfl
        · exact Or.inr ⟨hmem, hfc⟩

-- filterKeep preserves Pairwise
private lemma filterKeep_pairwise {mdb : MDB} {f : Nat → Bool} {R : CapNode → CapNode → Prop}
    (h : mdb.Pairwise R) :
    (revokeM.filterKeep mdb f).Pairwise R := by
  induction mdb with
  | nil => rw [filterKeep_nil]; unfold Seq.Pairwise; trivial
  | cons node rest ih =>
    unfold Seq.Pairwise at h
    rw [filterKeep_cons]
    split_ifs with hf
    · exact ih h.2
    · unfold Seq.Pairwise
      constructor
      · intro y hy
        rw [filterKeep_mem_iff] at hy
        exact h.1 y hy.1
      · exact ih h.2

-- filterKeep preserves uniqueIds
private lemma filterKeep_uniqueIds {mdb : MDB} {f : Nat → Bool}
    (h : uniqueIds mdb) : uniqueIds (revokeM.filterKeep mdb f) :=
  filterKeep_pairwise h

-- IsDesc is monotone: if result ⊆ mdb, then IsDesc result implies IsDesc mdb
private lemma IsDesc_mono {result mdb : MDB} {cid aId : Nat}
    (hsub : ∀ n, n ∈ result → n ∈ mdb)
    (hd : IsDesc result cid aId) :
    IsDesc mdb cid aId := by
  induction hd with
  | child node cid' aId' hmem hcap hpar =>
    exact IsDesc.child node cid' aId' (hsub node hmem) hcap hpar
  | trans cid' mid aId' h1 h2 ih1 ih2 =>
    exact IsDesc.trans cid' mid aId' ih1 ih2

-- filterKeep preserves acyclicity
private lemma filterKeep_acyclic {mdb : MDB} {f : Nat → Bool}
    (h : acyclic mdb) : acyclic (revokeM.filterKeep mdb f) := by
  intro id hd
  apply h id
  apply IsDesc_mono _ hd
  intro n hmem
  rw [filterKeep_mem_iff] at hmem
  exact hmem.1

-- Helper: filterKeep identity when no node has capId = cid
private lemma filterKeep_none_id {mdb : MDB} {cid : Nat}
    (hno : ∀ n ∈ mdb, n.capId ≠ cid) :
    revokeM.filterKeep mdb (fun c => c == cid) = mdb := by
  induction mdb with
  | nil => simp [filterKeep_nil]
  | cons node rest ih =>
    rw [filterKeep_cons]
    have hnode : node.capId ≠ cid := hno node ((Seq.mem_cons _ _ _).mpr (Or.inl rfl))
    simp [hnode, ih (fun n hmem => hno n ((Seq.mem_cons _ _ _).mpr (Or.inr hmem)))]

-- Helper: findParent ignores the filtered-out id when querying nid ≠ cid
private lemma findParent_filterKeep_ne {mdb : MDB} {nid cid : Nat} (hne : nid ≠ cid) :
    revokeM.findParent (revokeM.filterKeep mdb (fun c => c == cid)) nid =
    revokeM.findParent mdb nid := by
  induction mdb with
  | nil => simp [filterKeep_nil, findParent_nil]
  | cons node rest ih =>
    rw [filterKeep_cons]
    by_cases hc : (node.capId == cid) = true
    · simp only [hc, ↓reduceIte, ih, findParent_cons]
      have hcid : node.capId = cid := beq_iff_eq.mp hc
      simp [hcid, Ne.symm hne]
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      rw [findParent_cons, findParent_cons]
      by_cases hn : (node.capId == nid) = true
      · simp [hn]
      · simp only [Bool.not_eq_true] at hn; simp [hn, ih]

-- Helper: findParent of filtered-out id is none
private lemma findParent_filterKeep_self {mdb : MDB} {cid : Nat} :
    revokeM.findParent (revokeM.filterKeep mdb (fun c => c == cid)) cid = none := by
  induction mdb with
  | nil => simp [filterKeep_nil, findParent_nil]
  | cons node rest ih =>
    rw [filterKeep_cons]
    by_cases hc : (node.capId == cid) = true
    · simp [hc, ih]
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte, findParent_cons]
      simp [ih, hc]

-- Helper: mdbLen decreases by 1 when removing the unique node with capId = cid
private lemma mdbLen_filterKeep_one {mdb : MDB} {cid : Nat}
    (hmem : ∃ node ∈ mdb, node.capId = cid) (huniq : uniqueIds mdb) :
    revokeM.mdbLen (revokeM.filterKeep mdb (fun c => c == cid)) + 1 = revokeM.mdbLen mdb := by
  induction mdb with
  | nil => obtain ⟨_, h, _⟩ := hmem; simp [Seq.mem_nil] at h
  | cons node rest ih =>
    rw [filterKeep_cons, mdbLen_cons]
    by_cases hc : (node.capId == cid) = true
    · simp only [hc, ↓reduceIte]
      have hcid : node.capId = cid := beq_iff_eq.mp hc
      have hno : ∀ n ∈ rest, n.capId ≠ cid := by
        intro n hn
        unfold uniqueIds Seq.Pairwise at huniq
        have hne := huniq.1 n hn
        intro h; exact hne (hcid ▸ h.symm)
      rw [filterKeep_none_id hno]
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte, mdbLen_cons]
      have hmem' : ∃ n ∈ rest, n.capId = cid := by
        obtain ⟨n, hn, hcap⟩ := hmem
        rw [Seq.mem_cons] at hn
        rcases hn with rfl | hn
        · exfalso; simp [hcap] at hc
        · exact ⟨n, hn, hcap⟩
      have huniq' : uniqueIds rest := by
        unfold uniqueIds Seq.Pairwise at huniq; exact huniq.2
      have := ih hmem' huniq'; omega

-- Helper: descCheck in filterKeep implies descCheck in original (for pid ≠ cid)
private lemma descCheck_filterKeep_to_mdb (cid : Nat) :
    ∀ (target pid : Nat) (mdb : MDB) (fuel : Nat),
    revokeM.descCheck target pid (revokeM.filterKeep mdb (fun c => c == cid)) fuel = true →
    pid ≠ cid →
    revokeM.descCheck target pid mdb fuel = true := by
  intro target pid mdb fuel h hne
  induction fuel generalizing pid with
  | zero => simp [descCheck_zero] at h
  | succ n ih =>
    rw [descCheck_succ] at h
    rw [findParent_filterKeep_ne hne] at h
    rw [descCheck_succ]
    match hfp : revokeM.findParent mdb pid with
    | none => simp [hfp] at h
    | some q =>
      simp only [hfp] at h ⊢
      cases hqt : (q == target) with
      | true => simp
      | false =>
        simp only [hqt, Bool.false_or] at h ⊢
        by_cases hqcid : q = cid
        · subst hqcid; exfalso
          cases n with
          | zero => simp [descCheck_zero] at h
          | succ k =>
            rw [descCheck_succ, findParent_filterKeep_self] at h; simp at h
        · exact ih q h hqcid

-- Helper: if pid is not a descendant of cid and pid ≠ cid,
-- descCheck in mdb implies descCheck in filterKeep mdb (== cid)
private lemma descCheck_without_non_ancestor (cid : Nat) :
    ∀ (target pid : Nat) (mdb : MDB) (fuel : Nat),
    revokeM.descCheck target pid mdb fuel = true →
    ¬ IsDesc mdb pid cid →
    pid ≠ cid →
    revokeM.descCheck target pid (revokeM.filterKeep mdb (fun c => c == cid)) fuel = true := by
  intro target pid mdb fuel h hnotDesc hne
  induction fuel generalizing pid with
  | zero => simp [descCheck_zero] at h
  | succ n ih =>
    rw [descCheck_succ] at h
    rw [descCheck_succ, findParent_filterKeep_ne hne]
    match hfp : revokeM.findParent mdb pid with
    | none => simp [hfp] at h
    | some q =>
      simp only [hfp] at h ⊢
      cases hqt : (q == target) with
      | true => simp
      | false =>
        simp only [hqt, Bool.false_or] at h ⊢
        have hpid_q : IsDesc mdb pid q := by
          obtain ⟨node, hmem, hcap, hpar⟩ := findParent_some_mem hfp
          exact IsDesc.child node pid q hmem hcap hpar
        have hqcid : q ≠ cid := fun heq => hnotDesc (heq ▸ hpid_q)
        have hnotDesc_q : ¬ IsDesc mdb q cid :=
          fun hdqc => hnotDesc (IsDesc.trans pid q cid hpid_q hdqc)
        exact ih q h hnotDesc_q hqcid

-- Lemma: if uniqueIds mdb and acyclic mdb and descCheck target cid mdb fuel = true,
-- then descCheck target cid mdb (mdbLen mdb) = true
private lemma descCheck_fuel_mdbLen : ∀ (target cid : Nat) (mdb : MDB) (fuel : Nat),
    revokeM.descCheck target cid mdb fuel = true →
    uniqueIds mdb →
    acyclic mdb →
    revokeM.descCheck target cid mdb (revokeM.mdbLen mdb) = true := by
  intro target cid mdb
  -- We proceed by strong induction on mdbLen mdb
  suffices h : ∀ n target cid (mdb : MDB) fuel,
      revokeM.mdbLen mdb ≤ n →
      revokeM.descCheck target cid mdb fuel = true →
      uniqueIds mdb →
      acyclic mdb →
      revokeM.descCheck target cid mdb (revokeM.mdbLen mdb) = true by
    intro fuel hdc huniq hacyc
    exact h (revokeM.mdbLen mdb) target cid mdb fuel (Nat.le_refl _) hdc huniq hacyc
  intro n
  induction n with
  | zero =>
    intro target cid mdb fuel hlen hdc _huniq _hacyc
    -- mdbLen mdb ≤ 0 means mdb = nil
    cases mdb with
    | nil =>
      match fuel with
      | 0 => simp [descCheck_zero] at hdc
      | m+1 => rw [descCheck_succ, findParent_nil] at hdc; simp at hdc
    | cons _ _ => simp [mdbLen_cons] at hlen
  | succ m ihm =>
    intro target cid mdb fuel hlen hdc huniq hacyc
    -- If fuel ≤ mdbLen mdb, we're done by mono
    by_cases hfuel : fuel ≤ revokeM.mdbLen mdb
    · exact descCheck_mono_le target cid mdb fuel _ hfuel hdc
    · push_neg at hfuel
      -- fuel > mdbLen mdb: extract first step of path
      obtain ⟨fuel', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
      rw [descCheck_succ] at hdc
      match hfp : revokeM.findParent mdb cid with
      | none => simp [hfp] at hdc
      | some pid =>
        simp only [hfp] at hdc
        obtain ⟨nodeC, hmemC, hcapC, _⟩ := findParent_some_mem hfp
        cases hpid : (pid == target) with
        | true =>
          -- pid = target: path has length 1
          simp only [hpid] at hdc
          have h1 : revokeM.descCheck target cid mdb 1 = true := by
            rw [descCheck_succ, hfp]; simp [hpid]
          have hlen1 : 1 ≤ revokeM.mdbLen mdb := by
            cases mdb with
            | nil => simp [Seq.mem_nil] at hmemC
            | cons _ _ => rw [mdbLen_cons]; omega
          exact descCheck_mono_le target cid mdb 1 _ hlen1 h1
        | false =>
          simp only [hpid, Bool.false_or] at hdc
          -- hdc : descCheck target pid mdb fuel' = true
          -- cid ≠ pid (else cycle)
          have hcid_pid : cid ≠ pid := by
            intro heq; subst heq
            obtain ⟨node2, hmem2, hcap2, hpar2⟩ := findParent_some_mem hfp
            exact hacyc cid (IsDesc.child node2 cid cid hmem2 hcap2 hpar2)
          -- ¬ IsDesc mdb pid cid (else cycle via trans)
          have hnotDesc_pid : ¬ IsDesc mdb pid cid := by
            intro h
            obtain ⟨node2, hmem2, hcap2, hpar2⟩ := findParent_some_mem hfp
            have hcid_pid' : IsDesc mdb cid pid := IsDesc.child node2 cid pid hmem2 hcap2 hpar2
            exact hacyc cid (IsDesc.trans cid pid cid hcid_pid' h)
          -- Let mdb' = filterKeep mdb (== cid)
          let mdb' := revokeM.filterKeep mdb (fun c => c == cid)
          have hdc' : revokeM.descCheck target pid mdb' fuel' = true :=
            descCheck_without_non_ancestor cid target pid mdb fuel' hdc hnotDesc_pid (Ne.symm hcid_pid)
          have hlen_mdb' : revokeM.mdbLen mdb' + 1 = revokeM.mdbLen mdb :=
            mdbLen_filterKeep_one ⟨nodeC, hmemC, hcapC⟩ huniq
          have hlen_m : revokeM.mdbLen mdb' ≤ m := by omega
          have huniq' : uniqueIds mdb' := filterKeep_uniqueIds huniq
          have hacyc' : acyclic mdb' := filterKeep_acyclic hacyc
          -- Apply IH to mdb'
          have hih : revokeM.descCheck target pid mdb' (revokeM.mdbLen mdb') = true :=
            ihm target pid mdb' fuel' hlen_m hdc' huniq' hacyc'
          -- Lift back to mdb
          have hdc_mdb : revokeM.descCheck target pid mdb (revokeM.mdbLen mdb') = true :=
            descCheck_filterKeep_to_mdb cid target pid mdb (revokeM.mdbLen mdb') hih (Ne.symm hcid_pid)
          -- Combine: cid → pid and pid → target
          have hcomb : revokeM.descCheck target cid mdb (revokeM.mdbLen mdb' + 1) = true := by
            rw [descCheck_succ, hfp]
            simp only [hpid, Bool.false_or]
            exact hdc_mdb
          rw [hlen_mdb'] at hcomb
          exact hcomb

-- Complete completeness: IsDesc → descCheck with mdbLen fuel
private lemma descCheck_complete : ∀ (mdb : MDB) (target cid : Nat),
    IsDesc mdb cid target →
    uniqueIds mdb →
    acyclic mdb →
    revokeM.descCheck target cid mdb (revokeM.mdbLen mdb) = true := by
  intro mdb target cid hd huniq hacyc
  obtain ⟨k, hk⟩ := IsDesc_to_descCheck mdb target cid hd huniq
  exact descCheck_fuel_mdbLen target cid mdb k hk huniq hacyc

-- filterRevLog membership
private lemma filterRevLog_mem_iff {mdb : MDB} {f : Nat → Bool} {id : Nat} :
    id ∈ revokeM.filterRevLog mdb f ↔ ∃ n ∈ mdb, n.capId = id ∧ f n.capId = true := by
  induction mdb with
  | nil =>
    simp [filterRevLog_nil, Seq.mem_nil]
  | cons node rest ih =>
    rw [filterRevLog_cons]
    cases hf : f node.capId with
    | true =>
      simp only [↓reduceIte, Seq.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨n, hmem, hcap, hfc⟩)
        · exact ⟨node, Or.inl rfl, rfl, hf⟩
        · exact ⟨n, Or.inr hmem, hcap, hfc⟩
      · rintro ⟨n, hmem | hmem, hcap, hfc⟩
        · subst hmem; left; exact hcap.symm
        · right; exact ⟨n, hmem, hcap, hfc⟩
    | false =>
      simp only [Bool.false_eq_true, ite_false, ih, Seq.mem_cons]
      constructor
      · rintro ⟨n, hmem, hcap, hfc⟩
        exact ⟨n, Or.inr hmem, hcap, hfc⟩
      · rintro ⟨n, hmem | hmem, hcap, hfc⟩
        · subst hmem; rw [hf] at hfc; exact absurd hfc (by decide)
        · exact ⟨n, hmem, hcap, hfc⟩

-- filterKeep is a subseq of mdb
private lemma filterKeep_subseq {mdb : MDB} {f : Nat → Bool} :
    (revokeM.filterKeep mdb f).Subseq mdb := by
  induction mdb with
  | nil => rw [filterKeep_nil]; exact Seq.Subseq.nil
  | cons node rest ih =>
    rw [filterKeep_cons]
    split_ifs with hf
    · exact Seq.Subseq.skip node ih
    · exact Seq.Subseq.cons node ih

-- Length partition: filterKeep + filterRevLog lengths = mdb length
private lemma filterKeep_filterRevLog_len {mdb : MDB} {f : Nat → Bool} :
    (revokeM.filterKeep mdb f).length + (revokeM.filterRevLog mdb f).length = mdb.length := by
  induction mdb with
  | nil =>
    simp only [filterKeep_nil, filterRevLog_nil, Seq.length]
  | cons node rest ih =>
    rw [filterKeep_cons, filterRevLog_cons, seqLen_cons]
    split_ifs with hf
    · rw [seqLen_cons]
      omega
    · rw [seqLen_cons]
      omega

-- filterKeep identity when predicate is everywhere false
private lemma filterKeep_eq_self {mdb : MDB} {f : Nat → Bool}
    (h : ∀ node ∈ mdb, f node.capId = false) :
    revokeM.filterKeep mdb f = mdb := by
  induction mdb with
  | nil => rw [filterKeep_nil]
  | cons node rest ih =>
    rw [filterKeep_cons]
    have hnode : f node.capId = false := h node ((Seq.mem_cons _ _ _).mpr (Or.inl rfl))
    simp [hnode]
    apply ih
    intro n hmem
    exact h n ((Seq.mem_cons _ _ _).mpr (Or.inr hmem))

-- filterRevLog empty when predicate is everywhere false
private lemma filterRevLog_eq_nil {mdb : MDB} {f : Nat → Bool}
    (h : ∀ node ∈ mdb, f node.capId = false) :
    revokeM.filterRevLog mdb f = Seq.nil := by
  induction mdb with
  | nil => rw [filterRevLog_nil]
  | cons node rest ih =>
    rw [filterRevLog_cons]
    have hnode : f node.capId = false := h node ((Seq.mem_cons _ _ _).mpr (Or.inl rfl))
    simp [hnode]
    apply ih
    intro n hmem
    exact h n ((Seq.mem_cons _ _ _).mpr (Or.inr hmem))

-- filterKeep composition
private lemma filterKeep_filterKeep {mdb : MDB} {f g : Nat → Bool} :
    revokeM.filterKeep (revokeM.filterKeep mdb f) g =
    revokeM.filterKeep mdb (fun cid => f cid || g cid) := by
  induction mdb with
  | nil => simp [filterKeep_nil]
  | cons node rest ih =>
    rw [filterKeep_cons]
    split_ifs with hf
    · rw [filterKeep_cons, if_pos (by simp [hf])]
      exact ih
    · rw [filterKeep_cons]
      have hf' : f node.capId = false := by cases h : f node.capId <;> simp_all
      conv_rhs => rw [filterKeep_cons]
      simp only [hf', Bool.false_or]
      split_ifs with hg
      · exact ih
      · exact congrArg (Seq.cons node) ih

-- IsDesc in filtered MDB implies IsDesc in original
private lemma IsDesc_filterKeep_imp_orig {mdb : MDB} {f : Nat → Bool} {cid aId : Nat}
    (h : IsDesc (revokeM.filterKeep mdb f) cid aId) :
    IsDesc mdb cid aId := by
  apply IsDesc_mono _ h
  intro n hmem
  rw [filterKeep_mem_iff] at hmem
  exact hmem.1

-- Key: IsDesc in orig implies IsDesc in filtered (when all descendants of aId are not filtered)
private lemma IsDesc_orig_imp_filterKeep
    {mdb : MDB} {f : Nat → Bool} {cid aId : Nat}
    (hd : IsDesc mdb cid aId)
    (huniq : uniqueIds mdb)
    (hf : ∀ mid, IsDesc mdb mid aId → f mid = false) :
    IsDesc (revokeM.filterKeep mdb f) cid aId := by
  revert hf
  induction hd with
  | child node cid' aId' hmem hcap hpar =>
    intro hf
    have hfcid : f cid' = false := hf cid' (IsDesc.child node cid' aId' hmem hcap hpar)
    apply IsDesc.child node cid' aId'
    · rw [filterKeep_mem_iff]
      exact ⟨hmem, hcap ▸ hfcid⟩
    · exact hcap
    · exact hpar
  | trans cid' mid aId' h1 h2 ih1 ih2 =>
    intro hf
    apply IsDesc.trans cid' mid aId'
    · apply ih1
      intro m hm
      exact hf m (IsDesc.trans m mid aId' hm h2)
    · exact ih2 hf

-- unfold what revokeM.run gives
private lemma revokeM_run (targetId : Nat) (ks : KernelState) :
    (revokeM targetId).run ks = some ((), {
      mdb := revokeM.filterKeep ks.mdb (fun cid => revokeM.descCheck targetId cid ks.mdb (revokeM.mdbLen ks.mdb))
      revLog := revokeM.filterRevLog ks.mdb (fun cid => revokeM.descCheck targetId cid ks.mdb (revokeM.mdbLen ks.mdb))
    }) := by
  simp only [revokeM, KM.modify_run]

-- descCheck false ↔ not IsDesc (given wellFormed)
private lemma descCheck_false_iff_not_IsDesc
    {mdb : MDB} {target cid : Nat}
    (huniq : uniqueIds mdb) (hacyc : acyclic mdb) :
    revokeM.descCheck target cid mdb (revokeM.mdbLen mdb) = false ↔ ¬ IsDesc mdb cid target := by
  constructor
  · intro hf hd
    have := descCheck_complete mdb target cid hd huniq hacyc
    rw [hf] at this
    exact Bool.noConfusion this
  · intro hnd
    cases h : revokeM.descCheck target cid mdb (revokeM.mdbLen mdb)
    · rfl
    · exact absurd (descCheck_sound h) hnd

-- Variant: IsDesc iff descCheck true
private lemma IsDesc_iff_descCheck
    {mdb : MDB} {target cid : Nat}
    (huniq : uniqueIds mdb) (hacyc : acyclic mdb) :
    IsDesc mdb cid target ↔
    revokeM.descCheck target cid mdb (revokeM.mdbLen mdb) = true := by
  constructor
  · intro hd; exact descCheck_complete mdb target cid hd huniq hacyc
  · intro h; exact descCheck_sound h

-- ===== END AUX LEMMAS =====

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
  obtain ⟨huniq, hacyc⟩ := h_wf
  have hr := revokeM_run targetId ks
  -- The filter function
  let f := fun cid => revokeM.descCheck targetId cid ks.mdb (revokeM.mdbLen ks.mdb)
  constructor
  · -- (not none)
    rw [hr]; simp
  · intro ks' hks'
    -- Extract the structure of ks'
    have hks'_eq : ks' = { mdb := revokeM.filterKeep ks.mdb f,
                            revLog := revokeM.filterRevLog ks.mdb f } :=
      (Prod.mk.inj (Option.some.inj (hks'.symm.trans hr))).2
    subst hks'_eq
    simp only []
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- (1) No descendants remain
    · intro n hn hIsDesc
      have hmem := filterKeep_mem_iff.mp hn
      have hcheck := (IsDesc_iff_descCheck huniq hacyc).mp hIsDesc
      -- hmem.2 : f n.capId = false, hcheck : f n.capId = true (same definition)
      simp only [f] at hmem; simp [hmem.2] at hcheck
    -- (2) Non-descendants preserved
    · intro n hmem hnotDesc
      rw [filterKeep_mem_iff]
      exact ⟨hmem, (descCheck_false_iff_not_IsDesc huniq hacyc).mpr hnotDesc⟩
    -- (3) Subset
    · intro n hn
      exact (filterKeep_mem_iff.mp hn).1
    -- (4) Exact characterization
    · intro n
      rw [filterKeep_mem_iff]
      constructor
      · rintro ⟨hmem, hf⟩
        exact ⟨hmem, (descCheck_false_iff_not_IsDesc huniq hacyc).mp hf⟩
      · rintro ⟨hmem, hnotDesc⟩
        exact ⟨hmem, (descCheck_false_iff_not_IsDesc huniq hacyc).mpr hnotDesc⟩
    -- (5) Well-formedness
    · exact ⟨filterKeep_uniqueIds huniq, filterKeep_acyclic hacyc⟩
    -- (6) Subsequence
    · exact filterKeep_subseq
    -- (7) Log exact characterization
    · intro id
      rw [filterRevLog_mem_iff]
      constructor
      · rintro ⟨n, hmem, hcap, hfc⟩
        exact ⟨n, hmem, hcap, hcap ▸ descCheck_sound hfc⟩
      · rintro ⟨n, hmem, hcap, hIsDesc⟩
        exact ⟨n, hmem, hcap, (IsDesc_iff_descCheck huniq hacyc).mp (hcap.symm ▸ hIsDesc)⟩
    -- (8) Length partition
    · exact filterKeep_filterRevLog_len
    -- (9) Idempotence
    · intro ks'' hks''
      let result := revokeM.filterKeep ks.mdb f
      have hr2 := revokeM_run targetId { mdb := result, revLog := revokeM.filterRevLog ks.mdb f }
      have hks''_eq : ks'' = {
        mdb := revokeM.filterKeep result
          (fun cid => revokeM.descCheck targetId cid result (revokeM.mdbLen result))
        revLog := revokeM.filterRevLog result
          (fun cid => revokeM.descCheck targetId cid result (revokeM.mdbLen result))
      } := (Prod.mk.inj (Option.some.inj (hks''.symm.trans hr2))).2
      subst hks''_eq
      simp only []
      have huniq_r : uniqueIds result := filterKeep_uniqueIds huniq
      have hacyc_r : acyclic result := filterKeep_acyclic hacyc
      have hno_desc : ∀ n ∈ result,
          revokeM.descCheck targetId n.capId result (revokeM.mdbLen result) = false := by
        intro n hn
        apply (descCheck_false_iff_not_IsDesc huniq_r hacyc_r).mpr
        intro hd_result
        have hd_mdb := IsDesc_filterKeep_imp_orig hd_result
        have hcheck := (IsDesc_iff_descCheck huniq hacyc).mp hd_mdb
        have hmem := filterKeep_mem_iff.mp hn
        simp only [f] at hmem
        rw [hmem.2] at hcheck
        exact Bool.noConfusion hcheck
      constructor
      · exact filterKeep_eq_self (fun n hn => hno_desc n hn)
      · exact filterRevLog_eq_nil (fun n hn => hno_desc n hn)
    -- (10) Determinism
    · intro ks₂ hmdb _ ks₂' hks₂'
      have hr2 := revokeM_run targetId ks₂
      have hks₂'_eq : ks₂' = {
        mdb := revokeM.filterKeep ks₂.mdb
          (fun cid => revokeM.descCheck targetId cid ks₂.mdb (revokeM.mdbLen ks₂.mdb))
        revLog := revokeM.filterRevLog ks₂.mdb
          (fun cid => revokeM.descCheck targetId cid ks₂.mdb (revokeM.mdbLen ks₂.mdb))
      } := (Prod.mk.inj (Option.some.inj (hks₂'.symm.trans hr2))).2
      subst hks₂'_eq
      simp only [hmdb]
      exact ⟨rfl, rfl⟩
    -- (11) Bind-consistency (commutativity)
    · intro tgt2 hdisj ks_ab ks_ba hab hba
      -- Unfold the bind
      rw [KM.bind_run, revokeM_run] at hab hba
      simp only at hab hba
      -- Extract ks_ab
      let f2 := fun cid => revokeM.descCheck tgt2 cid ks.mdb (revokeM.mdbLen ks.mdb)
      -- Let ks1 = state after revoking targetId (= result of running revokeM targetId on ks)
      -- Let ks2 = state after revoking tgt2 (= result of running revokeM tgt2 on ks)
      -- ks_ab.mdb = filterKeep ks1.mdb (descCheck tgt2 on ks1)
      -- ks_ba.mdb = filterKeep ks2.mdb (descCheck targetId on ks2)
      have hab_eq : ks_ab.mdb = revokeM.filterKeep (revokeM.filterKeep ks.mdb f)
          (fun cid => revokeM.descCheck tgt2 cid
            (revokeM.filterKeep ks.mdb f) (revokeM.mdbLen (revokeM.filterKeep ks.mdb f))) := by
        have hrs := revokeM_run tgt2
          { mdb := revokeM.filterKeep ks.mdb f,
            revLog := revokeM.filterRevLog ks.mdb f }
        have heq := (Prod.mk.inj (Option.some.inj (hab.symm.trans hrs))).2
        exact congr_arg KernelState.mdb heq
      have hba_eq : ks_ba.mdb = revokeM.filterKeep (revokeM.filterKeep ks.mdb f2)
          (fun cid => revokeM.descCheck targetId cid
            (revokeM.filterKeep ks.mdb f2) (revokeM.mdbLen (revokeM.filterKeep ks.mdb f2))) := by
        have hrs := revokeM_run targetId
          { mdb := revokeM.filterKeep ks.mdb f2,
            revLog := revokeM.filterRevLog ks.mdb f2 }
        have heq := (Prod.mk.inj (Option.some.inj (hba.symm.trans hrs))).2
        exact congr_arg KernelState.mdb heq
      rw [hab_eq, hba_eq]
      -- Both sides via filterKeep_filterKeep
      rw [filterKeep_filterKeep, filterKeep_filterKeep]
      -- Need: filterKeep mdb (fun c => f c || f2' c) = filterKeep mdb (fun c => f2 c || f1' c)
      -- where f2' c = descCheck tgt2 c (fk mdb f) ... and f1' c = descCheck tgt1 c (fk mdb f2) ...
      -- Show these equal f c and f2 c respectively
      congr 1
      funext c
      -- Show: f c || descCheck tgt2 c (fk mdb f) n' = f2 c || descCheck targetId c (fk mdb f2) n''
      -- Sublemma: descCheck tgt2 c (fk mdb f) n' = f2 c
      have hf_f2' : (fun cid => revokeM.descCheck tgt2 cid (revokeM.filterKeep ks.mdb f)
          (revokeM.mdbLen (revokeM.filterKeep ks.mdb f))) c = f2 c := by
        simp only [f2]
        -- IsDesc mdb c tgt2 ↔ IsDesc (filterKeep mdb f) c tgt2
        -- All desc of tgt2 are not desc of targetId (by hdisj), hence not filtered by f
        by_cases hd : IsDesc ks.mdb c tgt2
        · -- c is desc of tgt2 in mdb → also in filterKeep mdb f
          have hd_filt := IsDesc_orig_imp_filterKeep hd huniq
            (fun mid hmid => (descCheck_false_iff_not_IsDesc huniq hacyc).mpr
              (fun hd1 => hdisj mid ⟨hd1, hmid⟩))
          rw [(IsDesc_iff_descCheck (filterKeep_uniqueIds huniq) (filterKeep_acyclic hacyc)).mp hd_filt]
          exact ((IsDesc_iff_descCheck huniq hacyc).mp hd).symm
        · -- c is not desc of tgt2 in mdb → not in filterKeep mdb f either
          rw [(descCheck_false_iff_not_IsDesc (filterKeep_uniqueIds huniq)
            (filterKeep_acyclic hacyc)).mpr (fun h => hd (IsDesc_filterKeep_imp_orig h))]
          exact ((descCheck_false_iff_not_IsDesc huniq hacyc).mpr hd).symm
      -- Sublemma: descCheck targetId c (fk mdb f2) n'' = f c
      have hf2_f1' : (fun cid => revokeM.descCheck targetId cid (revokeM.filterKeep ks.mdb f2)
          (revokeM.mdbLen (revokeM.filterKeep ks.mdb f2))) c = f c := by
        simp only [f]
        by_cases hd : IsDesc ks.mdb c targetId
        · have hd_filt := IsDesc_orig_imp_filterKeep hd huniq
            (fun mid hmid => (descCheck_false_iff_not_IsDesc huniq hacyc).mpr
              (fun hd2 => hdisj mid ⟨hmid, hd2⟩))
          rw [(IsDesc_iff_descCheck (filterKeep_uniqueIds huniq) (filterKeep_acyclic hacyc)).mp hd_filt]
          exact ((IsDesc_iff_descCheck huniq hacyc).mp hd).symm
        · rw [(descCheck_false_iff_not_IsDesc (filterKeep_uniqueIds huniq)
            (filterKeep_acyclic hacyc)).mpr (fun h => hd (IsDesc_filterKeep_imp_orig h))]
          exact ((descCheck_false_iff_not_IsDesc huniq hacyc).mpr hd).symm
      simp only [hf_f2', hf2_f1']
      exact Bool.or_comm _ _
-- === END: PROOF ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

end seL4.CteRevoke

