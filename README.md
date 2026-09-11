# Vero: Verified Code Generation Benchmark

Vero evaluates coding agents on verified code generation. A solver must
produce a working implementation together with a Lean 4 proof that it
satisfies a machine-checked specification. The benchmark has 103 tasks:
abstract interpretation operators from the eBPF verifier (52),
LLVM's KnownBits and DemandedBits (27), and seL4 kernel optimizations
(24).

| Area | Author | Tasks |
|------|--------|-------|
| eBPF | Hao Sun <hao.sun@inf.ethz.ch> | 52 eBPF tasks |
| LLVM | Cong Li <cong.li@inf.ethz.ch> | 27 KnownBits/DemandedBits tasks |
| seL4 | Zenan Li <zenan.li@inf.ethz.ch> | 24 seL4 optimization tasks |

**Leaderboard**: https://haosun.info/Vero/
## Features

- **Real-world.** Every task comes from _**a production system**_---the Linux
  kernel's eBPF verifier, LLVM, and seL4---not from a textbook exercise or
  a programming contest. For example, the eBPF tasks are value-tracking
  operators of the verifier (`kernel/bpf/verifier.c`).
- **New specification.** Each task encodes _**a new requirement**_ the upstream
  implementation does not yet meet, distilled from our upstream experience
  and documented community needs. For example, the eBPF tasks require
  abstract operators that are provably _sound and optimal_, a bar the
  verifier's current implementation does not reach, which makes the
  requirement real and _data contamination unlikely_.
- **Valuable to solve.** A correct solution is potentially an upstream
  _**contribution, not just a benchmark score**_. For example, the solution to
  the `tnum_step()` task is [merged into the Linux
  kernel](https://git.kernel.org/pub/scm/linux/kernel/git/bpf/bpf-next.git/commit/?id=833ef4a954e1),
  contributing a provably-correct operator.

#### Example: A Solution Merged into the Linux Kernel

`tnum_step()` returns the smallest member of a tnum strictly above `z`, a
subroutine of the verifier's range analysis. Claude Code solved it with a
branchless algorithm and a machine-checked proof.

<table>
<tr>
<th>Lean 4 solution </th>
<th><a href="https://git.kernel.org/pub/scm/linux/kernel/git/bpf/bpf-next.git/commit/?id=833ef4a954e1">Merged code</a></th>
</tr>
<tr>
<td valign="top">

```lean
def tnumStepUp (tval tmask z : ..) :=
  let d := z - tval
  let carry := d &&& ~~~tmask
  ...

-- r is the least tnum member above z
theorem tnumStepUp_correct
    (tval tmask z : BitVec 64)
    (h_tnum : tval &&& tmask = 0)
    (h_lo : tval ≤ z)
    (h_hi : z < (tval ||| tmask)) :
    let r := tnumStepUp tval tmask z
    satisfiesTnum64 r tval tmask ∧
    tval ≤ r ∧
    r ≤ (tval ||| tmask) ∧ z < r ∧
    ∀ w, satisfiesTnum64 w tval tmask
      → z < w → r ≤ w := by
  ...
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    intros <;> bv_decide
```

</td>
<td valign="top">

```c
u64 tnum_step(struct tnum t, u64 z)
{
  ...
  /*
   * Every member is t.value + s for
   * a submask s of t.mask, so r > z
   * reduces to s > d, d = z - t.value
   * -- increment d "within the mask":
   * fill every non-mask position with
   * 1 so the +1 ripples through the
   * gaps, then keep only mask bits;
   * carry_mask also fills below the
   * highest non-mask 1 in d.
   */
  d = z - t.value;
  carry = (1 << fls64(d & ~t.mask)) - 1;
  filled = d | carry | ~t.mask;
  inc = (filled + 1) & t.mask;
  return t.value | inc;
}
```

</td>
</tr>
</table>

Both excerpts are re-wrapped for width; the full artifact is
under `solved/TnumStepUp/`.

## Repository Structure

```
.
├── Dockerfile            # Lean 4 + agent CLIs + lean-lsp-mcp image
├── scripts/              # Runner, solvers, monitor, analysis, site generator
├── template/
│   ├── gen.py            # Instantiate the task templates
│   ├── *.lean            # Task.lean templates (eBPF/LLVM, expanded)
│   ├── seL4/, eBPF/      # Hand-maintained task sources
│   └── task_dir/         # Skeleton copied into each self-contained task dir
├── tasks/                # All tasks (make gen rebuilds all)
├── assets/runs/          # Per-run summaries shown on the website
└── solved/               # Published solutions
```

## Quick Start

All tasks are **self-contained**: each task directory holds the Lean 4
task file, the instruction, the checker, and the toolchain files. To use
your own pipeline, point your agent at a task directory; `./check.sh`
decides the result.

Alternatively, use the provided runner, which (1) builds the Docker
image, (2) mounts each task into a container, (3) runs the agent inside
it, and (4) collects the results. See `scripts/` and `make help`.

```bash
make build                       # docker build -t vero-lean4 with host UID/GID
make run TASKS=cnum_jmp64_eq     # run; override OUTPUT_DIR, SOLVER, PARALLEL, ...
make analyze                     # re-check and summarize ./results
```

## Task Details

### eBPF Tasks (52)

Abstract interpretation operations from the Linux kernel eBPF verifier,
over two abstract domains.

- Cnum (+ Tnum) domain (`eBPF_Cnum_*`): the current bpf-next register state, a
  64-bit tnum with a 64-bit and a 32-bit circular range. A cnum
  `{base, size}` is the wrapping arc from `base` covering `size + 1`
  values. All 64-bit tasks use this domain. See `docs/cnum.md`.
- Interval (+ Tnum) domain (`eBPF_Interval_*`): the previous register state, a
  tnum with four min/max range pairs (u64, s64, u32, s32). All 32-bit
  tasks use this domain. See `docs/interval.md`.

| Category | Count | Description |
|----------|-------|-------------|
| Cnum BranchTaken | 6 | Branch outcome (`always`, `never`, `unknown`) for a JMP64 comparison |
| Cnum RefineCond | 7 | Refine two states on the taken branch of a JMP64 condition |
| Cnum ALU | 8 | 64-bit transfer functions: add, sub, and, or, xor, lsh, rsh, arsh |
| Cnum Cast | 2 | Zero and sign extension (`coerce_reg_to_size`, `coerce_reg_to_size_sx`) |
| Cnum BoundsSync | 1 | Reduced form: synchronize tnum, cnum64, cnum32 (`reg_bounds_sync`) |
| Interval BranchTaken/RefineCond/ALU | 22 | The 32-bit (JMP32/ALU32) counterparts of the Cnum families |
| Tnum | 6 | Tnum operations: mul; udiv, sdiv, umod, smod by a non-zero constant; step |

The tnum_step task is solved and merged into the kernel.

### LLVM Tasks (27)

Optimal abstract transfer functions for LLVM's KnownBits domain. Flags
(nsw, nuw, exact, IntMinIsPoison) are boolean parameters, not separate
tasks. See `docs/llvm.md`.

| Category | Count | Description |
|----------|-------|-------------|
| KnownBits forward | 19 | udiv, sdiv, urem, srem, umax, umin, smax, smin, abs, abdu, abds, mul, mul_self, uadd.sat, usub.sat, sadd.sat, ssub.sat, mulhu, mulhs |
| DemandedBits backward | 8 | Minimal demanded input bits for add, sub, mul, udiv, sdiv, srem, urem, abs |

### seL4 Tasks (24)

Proofs that an optimized kernel routine is equivalent to its reference
specification. Each task provides the spec, the invariants, and a
correctness theorem, often a conjunction of a dozen or more algebraic
and frame clauses. The solver writes the optimized implementation and
the proof. The intended algorithm is described in each task header.

### Task Directory Layout

| File | Purpose | Editable |
|------|---------|----------|
| `Task.lean` | Source file with section markers | Editable sections only |
| `INSTRUCTION.md` | Task description and rules | No |
| `check.sh` | Verification and integrity check | No |
| `.provided_hash` | SHA256 of provided sections | No |

The task file is split into sections by `=== BEGIN: NAME (provided|editable) ===`
markers.

- Provided (locked): `DEFINITIONS`, `PREDICATES`, `AXIOMS`, `SPEC`, and
  the correctness theorem.
- Editable (solver workspace): `IMPLEMENTATION`, `AUX`, `PROOF`.

The full check (`check.sh`) runs five gates in order:

1. Integrity: hash the provided sections and compare against `.provided_hash`.
2. Stubs: no `sorry` or `sorryAx` remains.
3. Cheats: reject forbidden patterns (see `docs/cheating_patterns.md`).
4. Verify: `lake lean Task.lean` succeeds.
5. Axioms: `#print axioms` on each theorem lists only permitted axioms.

## Versioning and Task Liveness

A published solution under `solved/` is one web search away, so a run
either drops the solved tasks or takes away the web.

By default every task runs and the agents' web tools are *disabled*
(`VERO_DISABLE_WEB=1`, honored by both bundled solvers). `--run-unsolved`
(or `make run-unsolved`) runs only the tasks with no published solution
and leaves the web tools enabled.

## Running Benchmarks

Host requirements: Python >= 3.9 (the tooling is stdlib-only, see
`requirements.txt`), Docker, and git. For credentials, `cp .env.example
.env` and fill in your solver's token; the Makefile loads `.env`.

The `Makefile` wraps the common commands (see Quick Start) and checks
the solver's auth token; `make help` lists the targets. The equivalent
direct invocation is:

```bash
python3 scripts/run_bench.py \
  --output-dir ./results \
  --solver scripts/claude_code.sh \
  --build-images \
  --tasks cnum_jmp64_eq
```

Some options (see `--help` for the full list):

- `--tasks` / `--categories`: operator globs (`cnum_*`, `kb_udiv`) and
  area filter (`eBPF,LLVM,seL4`); ANDed when both are set.
- `--run-unsolved`: run only unsolved tasks, with agent web access.
- `--timeout` (hours, hard) and `--max-budget-usd` (soft): per-task budget.
- `--resume`: re-run only ERROR tasks (solver crash or infrastructure
  failure) from a clean task state; PASS, FAIL, and TIMEOUT are results
  and are not retried. Repeat `--run-unsolved` when resuming such a run.

For each task the runner fetches the Mathlib cache, runs the solver,
restores the protected files, and runs `check.sh`; the result is
committed to the output directory's git repository with a status prefix
(`PASS`, `FAIL`, `ERROR`, `TIMEOUT`) and summarized in `results.json`.

## Writing a Solver

A solver is any executable that receives two arguments and exits 0 when
it has finished (then `check.sh` decides PASS or FAIL; a non-zero exit
is recorded as ERROR):

```bash
#!/usr/bin/env bash
set -euo pipefail
TASK_DIR="$1"   # task directory, also the working directory
PROMPT="$2"     # guidance text from --prompt
cd "$TASK_DIR"
# Read INSTRUCTION.md, modify the editable sections of the task file, exit 0
```

Claude Code authenticates with `CLAUDE_CODE_OAUTH_TOKEN` (or an Anthropic
Console key in `ANTHROPIC_API_KEY`). `claude setup-token` prints a
long-lived OAuth token (`sk-ant-oat01-...`) from a Claude subscription:

```bash
export CLAUDE_CODE_OAUTH_TOKEN="sk-ant-oat01-..."
make run
```

Copilot authenticates with `COPILOT_GITHUB_TOKEN`: a fine-grained PAT
with the Copilot Requests permission, or a Copilot OAuth token (classic
`ghp_` PATs are rejected).

## Citation

```bibtex
@inproceedings{vero2027,
  title     = {From Specification to Kernel Commit: Verified Code Generation
               on Real-World Systems},
  author    = {Sun, Hao and Li, Zenan and Li, Cong and Su, Zhendong},
  booktitle = {Proceedings of ASPLOS '27},
  year      = {2027},
}
```

**Note.** Do not confuse this benchmark with the repository-level benchmark of
the same name in [arXiv:2608.13522](https://arxiv.org/abs/2608.13522); ours is
accepted to
[ASPLOS 2027](https://www.asplos-conference.org/asplos2027/cfp/).
