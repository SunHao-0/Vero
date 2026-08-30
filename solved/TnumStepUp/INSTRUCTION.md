# Task: Find smallest value above z satisfying a tnum

`Task.lean` is divided into labeled sections:

```
-- === BEGIN: SECTION_NAME (provided|editable) ===
...
-- === END: SECTION_NAME ===
```

**Provided sections** (DO NOT MODIFY):
- **DEFINITIONS**
- **SPEC**

**Editable sections** (your workspace):
- **IMPLEMENTATION**
- **PROOF**
- **AUX**

## What You Must Do

Implement the function in the IMPLEMENTATION section and prove correctness in the PROOF section.
The theorem in SPEC states that your implementation satisfies all postconditions.You may add helper lemmas in AUX.

## Rules

1. Only edit the editable sections. Do not modify any `(provided)` section.
2. All `sorry` must be removed, and the code must remain a single file.
3. Do not modify `check.sh`, `.provided_hash`, `lakefile.lean`,
   `lean-toolchain`, or `lake-manifest.json`.
4. Add helpers/lemmas in AUX, axioms are disallowed (except for the provided ones).
5. Importantly, **the algorithm must be of O(1) complexity**, e.g.,
    - quantify over a huge space (e.g., u32/u64) is not allowed;
    - bounded loops (e.g., 64 iterations) are allowed.
6. Provide any additional notes/comments to `agent_note.md`.

A **checker** will enforce the proof correctness and the content integrity.
A **human expert** will check the algorithm complexity.
**Any violation/cheating will lead to a task failure.**

You may run `./check.sh` to perform a simple check:

| Step | What it checks | Flag |
|------|---------------|------|
| Integrity | Provided sections unchanged (hash comparison) | `--check-integrity` |
| Verify | `lake lean Task.lean` compiles without errors | `--compile` |
| Stubs | No `sorry` remaining in the file | — |
