# Task: Unsigned Maximum

> **Scored by a human**, not just `./check.sh`. A cheat (spec-mirror,
> `Classical.choose`, brute force, `#exit`, etc.) scores **zero** even if
> the checker goes green. An honest partial attempt scores strictly
> more than any cheat. Don't waste tokens building one.

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
- **PROOF**
- **AUX**

## What You Must Do

Implement the function in the IMPLEMENTATION section so that it computes the optimal KnownBits for the given operation.

The function receives two KnownBits and must return a `KnownBits` for the unsigned maximum.

The result must satisfy:
- **Well-formedness**: `(result.zero &&& result.one) = 0`
- **Soundness**: for every concrete input(s) in the concretization (satisfying any flag preconditions), the concrete result is in the concretization of the output KnownBits
- **Optimality**: the result is the ⊑-least sound abstraction — for any other valid KnownBits `r'` that is also sound, `γ(result) ⊆ γ(r')`

This is the standard Galois connection optimality condition: `result = α(f(γ(a) × γ(b)))`. You may add helper lemmas in AUX.

## Rules

1. Only edit the editable sections. Do not modify any `(provided)` section,
   and do not insert code in the gaps between provided sections — the
   checker scans everything outside `(provided)` blocks.
2. All `sorry` and `admit` must be removed. The code must remain a single file.
3. Do not modify `check.sh`, `.provided_hash`, `lakefile.lean`,
   `lean-toolchain`, or `lake-manifest.json`.
4. Add helpers/lemmas in AUX. No user-defined `axiom` anywhere outside
   the provided AXIOMS section.
5. The **implementation must be O(1) complexity** (bounded loops up to 64 are OK).

   **Forbidden anywhere outside provided sections** (auto-checked, instant FAIL):
   - `sorry`, `admit`, `admitGoal`, `sorryAx`, `lcProof` — proof holes
   - `axiom` (direct or via `addDecl` / `.axiomDecl` metaprogramming)
   - `Decidable`, `DecidableEq`, `DecidablePred` — decidability instances
   - `Fintype`, `Finite`, `Finset.univ` — finite-type / universal-finset tricks
   - `Fin (2 ^ n)` — enumeration over large spaces (any whitespace)
   - `Classical.*` and `open Classical` — classical decidability escape
   - `noncomputable` (including `noncomputable section` in a gap)
   - `native_decide`, `Testable`, `plausible` — runtime / test decision
   - `Nat.find`, `Nat.findGreatest` — classical minimization
   - `#exit` — halts Lean before the theorem is elaborated

   **Forbidden in the IMPLEMENTATION block only** (the proof may still use
   these; the implementation may not):
   - `∀` / `∃` / `forall` / `exists` — no quantifiers; the implementation
     must compute on the components of the abstract state, not reason
     about γ.
   - `inGamma`, `satisfiesTnum32`, `satisfiesTnum64` — the implementation
     must not name the concretization relation.
   - `.choose`, `.choose_spec` — no `Classical.choose`-style witness
     extraction.
   - Any `concrete…` operator (`concreteAdd`, `concreteLsh32`, …) —
     the abstract transformer must never call the concrete operator.
   - `by` — no tactic mode inside the implementation.

5. Provide any additional notes/comments to `agent_note.md`.

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

## Workflow (follow this exact order)

The checker has two modes. Use the fast one aggressively while you iterate:

1. **Write the implementation.** Replace the stub in the IMPLEMENTATION
   block with a concrete definition that operates on the fields of the
   abstract state (`reg.umin_value`, `reg.var_off.value`, …). Do not
   reference γ, quantifiers, or the concrete operator.

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

## Do not give up early

These tasks are hard, but they are all solvable — previous runs have
produced full proofs for every one of them. Stubs like `sorry`, `dst`,
`reg`, or `(reg1, reg2)` **count as failures**. So does bailing out with
"unable to complete in this run". If you reach a wall:

- **Keep the best partial implementation you've found**, even if the
  optimality proof isn't closing. A sound-but-loose implementation with
  a partial proof is strictly better than a stub; it also gives you a
  concrete target to refine.
- **Decompose the goal**. The theorem is typically a conjunction
  (`validReg ∧ soundness ∧ optimality`). Prove the components
  independently — `constructor` / `refine ⟨?_, ?_, ?_⟩` — and attack
  each separately. Soundness is usually easy; optimality is the hard
  part.
- **Use the AUX section.** Extract repetitive sub-lemmas there; do not
  inline the same reasoning five times.
- **Do not reset your file back to the original two holes** just because
  one strategy didn't work. Keep progress. Reset only if the file is
  genuinely broken.
- **Do not try to "decide" the whole theorem**, do not `revert` and
  `decide`, do not try `native_decide` — they are forbidden and would
  not work anyway.
- **Do not edit `check.sh` or the provided sections** to "get unstuck".
  That is cheating and will be detected.

Keep iterating until either the full `./check.sh` passes.
