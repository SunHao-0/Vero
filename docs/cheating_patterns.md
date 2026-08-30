# Cheating Patterns

The benchmark asks for a constructive implementation of an abstract
transformer, together with a proof that it is sound and optimal. A
submission that produces a green `check.sh` without a real
implementation is a cheat and scores zero on human review. This document
lists the patterns observed in prior runs, gives a minimal example of
each, and states which `check.sh` gate rejects it.

Each pattern does one of three things: it invokes `Classical.choose` on
the specification instead of computing, it enumerates the `2^64` values
of the concretization, or it defers the computation to a
`Classical.propDecidable` instance that has no extractable code.

## Patterns

### 1. Spec-mirroring conditional

The implementation transcribes the specification into a Classical
`if/then/else` and returns the answer the specification names. It
contains no algorithm.

```lean
def jmpEq (r1 r2 : RegState) : BranchResult :=
  if ∀ x y, inGamma r1 x → inGamma r2 y → x = y then BranchResult.always
  else if ∀ x y, inGamma r1 x → inGamma r2 y → x ≠ y then BranchResult.never
  else BranchResult.unknown
```

### 2. Classical.choose from the existence form

The implementation is `if h : <witness exists> then h.choose else default`,
and the proof unpacks `h.choose_spec`. It does not describe the answer;
it asks `Classical.choose` to produce one.

```lean
open Classical in
noncomputable def alu32Lsh (dst src : RegState) : RegState :=
  if h : ∃ r, validReg r ∧ sound r ∧ optimal r then h.choose else dst
```

### 3. Fintype enumeration over BitVec

The implementation builds a `Fintype (BitVec 64)` and folds over
`Finset.univ`, enumerating all `2^64` values. It is `noncomputable`
because that finset is not computable.

```lean
noncomputable instance : Fintype (BitVec 64) :=
  Fintype.ofEquiv (Fin (2^64)) ...

noncomputable def umin (reg : RegState) (h : (gammaImage reg).Nonempty) : BitVec 64 :=
  (gammaImage reg).min' h
```

### 4. Bit-by-bit Classical.propDecidable

For each bit position, decide a proposition over the concretization with
`Classical.propDecidable`, then assemble the result. The bit values come
from case analysis over the value set, not from the finite representation
of the abstract state.

```lean
open Classical in
private noncomputable def allBitOne (a b : Tnum) (i : Nat) : Bool :=
  decide (∀ x y, satisfiesTnum64 x a.value a.mask →
                 satisfiesTnum64 y b.value b.mask → (x * y).getLsbD i = true)
```

### 5. Code in the gaps between sections

Text between marked sections (for example between `END: AXIOMS` and
`BEGIN: SPEC`) is neither hashed nor, in older checkers, scanned.
Submissions placed forbidden helpers there, and a `noncomputable
section` opened in a gap silently made a following provided definition
noncomputable without changing the bytes inside that provided section.

### 6. noncomputable via section or open Classical in

Two ways to obtain Classical or noncomputable behavior without writing
the tokens `noncomputable` or `Classical.` inside a scanned region: open
a `noncomputable section` in a gap (pattern 5), or write `open Classical
in <decl>` before a declaration.

## Detection

`check.sh` runs five gates in order. The scan operates on everything
outside the `(provided)` sections, gaps included, after stripping
comments.

- Integrity. The provided sections are hashed and compared against
  `.provided_hash`. The hash covers every byte inside a `(provided)`
  marker. `gen.py` and `check.sh` extract the same bytes, so a tagged
  marker such as `(provided, foo)` does not diverge.

- Cheat scan, whole writable surface. Rejects proof holes (`sorry`,
  `sorryAx`, `admit`, `lcProof`), user `axiom`, metaprogramming axiom
  injection (`addDecl`, `.axiomDecl`), command and elaborator
  redefinition (`macro`, `elab`, `syntax`, `notation`, the `*ElabM`
  monads), native-evaluation escapes (`ofReduceBool`, `reduceBool`,
  `implemented_by`, `extern`), and nonconstructive or enumerating
  constructs (`Fintype`, `Finite`, `Finset.univ`, `Decidable*`,
  `Classical.*`, `open Classical`, `noncomputable`, `native_decide`,
  `Nat.find`, `Fin (2 ^ n)` with any spacing). This closes patterns 3,
  4, 5, 6 regardless of where the code sits.

- Cheat scan, IMPLEMENTATION only. The implementation must compute on the
  fields of the abstract state. It may not name a quantifier (`∀`, `∃`,
  or the Pi-type form `(x : T) → ...`), the concretization predicates
  (`inGamma`, `satisfiesTnum*`), `.choose` or `.choose_spec`, a
  `concrete*` operator, or `by`. This closes patterns 1 and 2.

- Verify. `lake lean Task.lean` succeeds and the kernel reports no
  `sorry`.

- Axioms. `#print axioms` on each theorem must list only `propext`,
  `Classical.choice`, `Quot.sound`, the two axioms introduced by
  `bv_decide` (`Lean.ofReduceBool`, `Lean.trustCompiler`), and the
  axioms declared in the task's own AXIOMS section. Any other axiom
  fails. The output is flattened before parsing, so a wrapped multi-line
  axiom list is read in full.
