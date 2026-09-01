# Task: Backward Demanded Bits for Mul

**Source**: LLVM DemandedBits analysis, llvm/lib/Analysis/DemandedBits.cpp (determineLiveOperandBits)

> **Scored by a human**, not just `./check.sh`. A cheat (spec-mirror,
> `Classical.choose`, brute force, `#exit`, etc.) scores **zero** even if
> the checker goes green. An honest partial attempt scores strictly
> more than any cheat. Don't waste tokens building one.

## What You Must Do

Implement the function in the IMPLEMENTATION section so that it computes the optimal backward demanded bits for the given operation.

The function receives demanded output bits, KnownBits of the input(s), and any flag parameters. It returns demanded bit masks for the input(s).

The result must satisfy:
- **Unknown-bits constraint**: demanded bits must be a subset of the unknown bits (bits where neither `zero` nor `one` is set in the KnownBits)
- **Soundness**: for every bit NOT marked as demanded, flipping that bit in any valid concrete input (where the flipped value is also valid and satisfies flag preconditions) must not change any demanded output bit
- **Optimality**: every bit marked as demanded IS truly demanded — there exist concrete inputs where flipping that bit changes a demanded output bit

This is the backward dual of the Galois connection: find the minimal set of input bits that can affect the demanded output bits. You may add helper lemmas in AUX.

**Design before coding.** Sketch your approach in `agent_note.md` before
writing IMPLEMENTATION. When the task asks for an *optimal* abstract
transformer, the most common failure is a sound but imprecise
implementation that then blocks the optimality proof. Work out which
components of the provided input the answer depends on, and whether the
tightest result must combine several of them. If you can construct an
input where a one-component implementation is imprecise, widen it now
rather than after a failed proof.

`Task.lean` is divided into labeled sections:

```
-- === BEGIN: SECTION_NAME (provided|editable) ===
...
-- === END: SECTION_NAME ===
```

**Provided sections** (DO NOT MODIFY):
- **DEFINITIONS**
- **PREDICATES**
- **SPEC**
- **SPEC_CORRECT**

**Editable sections** (your workspace):
- **IMPLEMENTATION**
- **AUX**
- **PROOF**

## Rules

1. Only edit the editable sections. Do not modify any `(provided)` section,
   and do not insert code in the gaps between provided sections — the
   checker scans everything outside `(provided)` blocks.
2. All `sorry` and `admit` must be removed. The code must remain a single file.
3. Do not modify `check.sh`, `.provided_hash`, `lakefile.lean`,
   `lean-toolchain`, or `lake-manifest.json`.
4. Add helpers/lemmas in AUX. No user-defined `axiom` anywhere outside
   the provided AXIOMS section.
5. **No hard complexity bound is imposed for this operator** --- an optimal transfer function here may genuinely need more than constant work. But **brute force scores ZERO**: we expect an insightful algorithm, and the human review rejects any implementation whose running time scales with the number of concrete values represented rather than with the bit-width. This includes enumerating the concretization, O(2^popcount(mask)) case explosion, and **tree recursion over the 64 bit positions** --- recursion that branches at each bit is 2^64 work even though it is 64 levels deep. 

   **Forbidden anywhere outside provided sections** (auto-checked, instant FAIL):
   - `sorry`, `admit`, `admitGoal`, `sorryAx`, `lcProof` — proof holes
   - `axiom` (direct or via `addDecl` / `.axiomDecl` metaprogramming)
   - `Decidable`, `DecidableEq`, `DecidablePred` — decidability instances
   - `Fintype`, `Finite`, `Finset.univ` — finite-type / universal-finset tricks
   - `Fin (2 ^ n)` — enumeration over large spaces (any whitespace)
   - `Classical.*` and `open Classical` — classical decidability escape
   - `noncomputable` (including `noncomputable section` in a gap)
   - `native_decide`, `Testable`, `plausible` — runtime / test decision
   - `ofReduceBool`, `reduceBool`, `implemented_by`, `extern` — manual
     native-evaluation escapes (the `bv_decide` tactic itself is fine;
     its `Lean.ofReduceBool`/`Lean.trustCompiler` axioms are accepted,
     as are the axioms provided in the task's AXIOMS section)
   - `Nat.find`, `Nat.findGreatest` — classical minimization
   - `#exit` — halts Lean before the theorem is elaborated

   **Forbidden in the IMPLEMENTATION block only** (the proof may still use
   these; the implementation may not):
   - `∀` / `∃` / `forall` / `exists` / `Forall` / `Exists` — no
     quantifiers, including the Pi-type syntax `(x : T) → …`, which is
     the Lean-equivalent of `∀ x : T, …` without the symbol.
   - `.choose`, `.choose_spec` — no `Classical.choose`-style witness
     extraction.
   - `by` — no tactic mode inside the implementation.

6. Provide any additional notes/comments to `agent_note.md`.

An **automated checker** enforces proof soundness, content integrity, and the
above rules. A **human expert** will check the algorithm complexity.
In addition, the human expert will also review every solution for
correctness, soundness, and any attempt to circumvent the verification.
Any form of cheating — including but not limited to introducing axioms
(directly or via metaprogramming), weakening specifications, abusing
`sorry`/`admit` variants, exploiting Lean internals, inserting `#exit`,
or hiding forbidden code in the gaps between provided sections — will be
detected and result in an automatic FAIL.

**Any violation causes a task FAIL.**

## Workflow

The checker has two modes. Use the fast one while you iterate:

1. **Write the implementation.** Replace the stub in the IMPLEMENTATION
   block with a concrete definition that operates on the fields of the
   provided input structures (see the SPEC and DEFINITIONS sections for
   the exact types and field names).

2. **Run the fast cheat check immediately**, *before* you write a single
   line of proof:
   ```
   ./check.sh --cheats-only
   ```
   This runs in under a second, needs no compilation, and catches every
   forbidden pattern listed above. If it FAILs, rewrite the implementation
   — do not proceed to the proof on code that will be rejected anyway.

3. **Compile the file** to make sure the implementation typechecks:
   ```
   ./check.sh --compile
   ```
   (sorry stubs in the PROOF section are fine at this stage).

4. **Write the proof.** Only now should you invest in proving the theorem.

5. **Before submitting**, run the full checker:
   ```
   ./check.sh
   ```
   It must print PASS on every line — integrity, stubs, cheats, verify,
   axioms — otherwise the submission fails. In particular, re-run the
   cheat check one last time: any helper you added during the proof may
   have accidentally tripped a forbidden pattern.

| Step | Command | What it checks |
|------|---------|----------------|
| Cheats | `./check.sh --cheats-only` | No forbidden patterns anywhere outside provided sections |
| Integrity | `./check.sh --check-integrity` | Provided sections unchanged (hash) |
| Compile | `./check.sh --compile` | `lake lean Task.lean` succeeds |
| Full    | `./check.sh` | All of the above + no sorry + only standard axioms |

## **NEVER** give up

These tasks are hard but solvable. Leaving the stub in place (`sorry`,
or returning an input unchanged) **counts as a failure**, as does
bailing out with "unable to complete in this run".

If you reach a wall:

- **Decompose the goal**. The theorem is typically a conjunction of
  clauses. Prove the components independently with `constructor` /
  `refine ⟨?_, ?_, ?_⟩` and attack each separately.
- **Use the AUX section.** Extract repetitive sub-lemmas there; do not
  inline the same reasoning several times.
- **Do not reset your file back to the original stubs** just because one
  strategy didn't work. Keep progress. Reset only if the file is
  genuinely broken.
- **Optimality resisting?** For a task with an optimality clause, if
  soundness closed quickly but optimality resists repeated rewrites, the
  bug is almost always the implementation, not the proof: a sound but
  imprecise implementation has no provable optimality. Enhance the
  implementation (use another input component, tighten the result), then
  retry.
- **Brute force ≠ bounded.** Bounded recursion depth does not imply
  bounded time: recursion that branches at every bit position runs in
  time exponential in the number of unknown bits even though it is only
  64 levels deep. That is brute force and an instant FAIL.

Keep iterating until either the full `./check.sh` passes.
