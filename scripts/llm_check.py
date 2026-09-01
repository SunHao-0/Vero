#!/usr/bin/env python3
"""LLM review of a completed task, in isolation.

check.sh decides the machine-checkable gates (integrity hash, forbidden
patterns, compilation, axioms). This script asks an agent for the two
judgments a script cannot make: whether the solution defeats check.sh
instead of satisfying it, and whether the implementation meets the
task's complexity rule instead of brute-forcing.

The judge never sees the solver's working directory. The task is
re-staged in a fresh temporary directory that holds exactly the files
of the issued task (INSTRUCTION.md, check.sh, toolchain files, hash),
with Task.lean replaced by the submission. Logs, notes, scratch files
and the transcript stay behind, so the verdict cannot depend on who
wrote the solution. The agent runs confined to that directory with
read-only tools plus ./check.sh, and the verdict is written next to
the submission as llm_review.json.

Usage:
    python3 scripts/llm_check.py solved/TnumStepUp             # one task dir
    python3 scripts/llm_check.py results/tasks/eBPF_* --force  # several
    python3 scripts/llm_check.py results                       # PASS tasks of a run

Requires the `claude` CLI (with --restricted support) and its login
(CLAUDE_CODE_OAUTH_TOKEN, ANTHROPIC_API_KEY, or `claude setup-token`).
"""

import argparse
import functools
import json
import re
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Dict, List, Optional, Tuple

BENCH_ROOT = Path(__file__).resolve().parent.parent
REVIEW_FILE = "llm_review.json"
DEFAULT_MODEL = "claude-opus-5"

# The files an issued task consists of. Everything else found in a
# completed task dir was produced by the solver and is withheld.
TASK_FILES = (
    "INSTRUCTION.md", "Task.lean", "check.sh", ".provided_hash",
    "lakefile.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
)

# Tools the judge may use. --restricted confines Read/Grep/Glob to the
# staging dir; Bash is auto-approved only for the two check.sh modes
# that do not build (a full check would fetch the Mathlib cache), and
# every other command is denied (-p mode never prompts).
JUDGE_TOOLS = "Read,Grep,Glob,Bash"
JUDGE_ALLOWED = ("Read,Grep,Glob,"
                 "Bash(./check.sh --cheats-only:*),"
                 "Bash(./check.sh --check-integrity:*)")

VERDICT_SCHEMA = {
    "type": "object",
    "properties": {
        "verdict": {"type": "string",
                    "enum": ["ACCEPT", "REJECT", "UNCERTAIN"]},
        "faithful": {"type": "boolean"},
        "complexity_ok": {"type": "boolean"},
        "issues": {"type": "array", "items": {"type": "string"}},
        "summary": {"type": "string"},
    },
    "required": ["verdict", "faithful", "complexity_ok", "issues", "summary"],
}

PROMPT = """\
You are reviewing a submission to the Vero verified code generation \
benchmark. The current directory is a completed task exactly as it was \
issued, except that Task.lean now contains the solver's work:

  INSTRUCTION.md   the task statement and its rules
  Task.lean        provided sections (locked) and the solver's editable \
sections: IMPLEMENTATION, AUX, PROOF
  check.sh         the automated checker; `./check.sh --cheats-only` and \
`./check.sh --check-integrity` are the only commands you can run (no Lean \
cache here, so no build)
  lakefile.*, lake-manifest.json, lean-toolchain, .provided_hash: toolchain \
files

check.sh has already passed on this submission: the provided sections \
match the issued hash, the file compiles, the forbidden-pattern scan is \
clean, and the theorem depends on no extra axioms. Take the specification \
as intact and do not re-verify it. Two questions remain that a script \
cannot answer; answer them from the files in this directory only.

1. faithful: does the solution honestly satisfy the checker, or does it \
work around it? First read check.sh to learn what it scans and how (which \
tokens, which regions, how comments and strings are stripped), then read \
the editable sections and the gaps between sections of Task.lean looking \
for anything that defeats the scan or the intent of the task: forbidden \
constructs reached through aliases, notation, macros, metaprogramming, \
Unicode look-alikes, or `set_option`; code placed where the scanner does \
not look; an implementation that mirrors the specification instead of \
computing (deciding a case by evaluating the property it must establish); \
proofs that depend on such tricks. Ordinary use of standard automation \
(bv_decide, simp, omega, decide on small goals) is fine.

2. complexity_ok: does the implementation, together with the AUX helpers \
it calls, obey the complexity rule stated in INSTRUCTION.md? Brute force \
violates it: any strategy whose running time grows with the number of \
concrete values the abstract input represents (enumerating a \
concretization, searching over sub-masks, recursion that branches at \
each bit position) rather than with the bit-width. Recursion depth 64 \
does not imply bounded time. If INSTRUCTION.md states no rule, judge \
against the algorithm the task header describes.

Do not judge style, proof length, or elegance, and do not speculate \
about who or what produced the solution. REJECT only for a concrete \
problem you can point to in the file; use UNCERTAIN when you suspect one \
but cannot confirm it.

Answer with a JSON object: verdict (ACCEPT | REJECT | UNCERTAIN), \
faithful (bool), complexity_ok (bool), issues (one short string per \
problem, with line references), summary (one or two sentences).
"""


# ---------------------------------------------------------------------------
# Staging
# ---------------------------------------------------------------------------

def _git_issued(task_dir: Path) -> Optional[Dict[str, bytes]]:
    """Issued files from the initial commit of a run_bench.py output dir
    (it commits the clean task copies before the solver runs)."""
    root = task_dir.parent.parent
    rel = f"tasks/{task_dir.name}"
    if not (root / ".git").exists():
        return None
    log = subprocess.run(
        ["git", "-C", str(root), "log", "--format=%H", "--diff-filter=A",
         "--", f"{rel}/Task.lean"], capture_output=True, text=True)
    commits = log.stdout.split()
    if not commits:
        return None
    files = {}
    for name in TASK_FILES:
        show = subprocess.run(
            ["git", "-C", str(root), "show", f"{commits[-1]}:{rel}/{name}"],
            capture_output=True)
        if show.returncode == 0:
            files[name] = show.stdout
    return files if "Task.lean" in files else None


def _bench_issued(task_dir: Path) -> Optional[Dict[str, bytes]]:
    """Issued files from the bench tree, matched by full or unprefixed
    name (TnumStepUp -> eBPF_TnumStepUp)."""
    tasks_dir = BENCH_ROOT / "tasks"
    if not tasks_dir.is_dir():
        return None
    for d in [tasks_dir / task_dir.name] + sorted(tasks_dir.iterdir()):
        if d.is_dir() and (d / "Task.lean").exists() and (
                d.name == task_dir.name
                or d.name.endswith("_" + task_dir.name)):
            return {n: (d / n).read_bytes()
                    for n in TASK_FILES if (d / n).exists()}
    return None


def issued_files(task_dir: Path) -> Tuple[Dict[str, bytes], str]:
    """The task as it was issued, and where that came from.

    "git": the initial commit of the output dir, version-exact.
    "submission": the task dir's own copies. run_bench.py restores the
    protected files (check.sh, hash, toolchain, INSTRUCTION.md) after
    the solver, so they are the issued ones; older runs did not protect
    INSTRUCTION.md, and a solved/ dir is trusted as curated.
    "bench": the bench tree, for a dir that lacks the files. The tree
    drifts (tasks are regenerated), so its hash and rules may not be
    the ones the solver faced.
    """
    files = _git_issued(task_dir)
    if files:
        return files, "git"
    files = {n: (task_dir / n).read_bytes()
             for n in TASK_FILES if (task_dir / n).exists()}
    if {"INSTRUCTION.md", "check.sh"} <= files.keys():
        return files, "submission"
    bench = _bench_issued(task_dir) or {}
    return {**bench, **files}, "bench"


def stage_task(task_dir: Path) -> Tuple[Path, str]:
    """Create the judge's directory: the issued task with the submitted
    Task.lean. Returns (stage_dir, issued_from)."""
    files, source = issued_files(task_dir)
    files["Task.lean"] = (task_dir / "Task.lean").read_bytes()
    stage = Path(tempfile.mkdtemp(prefix=f"vero-review-{task_dir.name}-"))
    for name, content in files.items():
        (stage / name).write_bytes(content)
    check = stage / "check.sh"
    if check.exists():
        check.chmod(check.stat().st_mode | 0o111)
    return stage, source


# ---------------------------------------------------------------------------
# Judge
# ---------------------------------------------------------------------------

@functools.lru_cache(maxsize=None)
def _claude_help() -> str:
    try:
        return subprocess.run(["claude", "--help"], capture_output=True,
                              text=True).stdout
    except FileNotFoundError:
        return ""


def extract_json(text: str) -> Optional[Dict]:
    """Fallback verdict parser for a reply without structured output."""
    m = re.search(r"\{.*\}", text, re.S)
    if not m:
        return None
    try:
        d = json.loads(m.group(0))
    except json.JSONDecodeError:
        return None
    return d if isinstance(d, dict) and "verdict" in d else None


def run_judge(stage: Path, model: str, timeout: int, max_turns: int,
              budget: Optional[float]) -> Dict:
    """One agentic review, confined to `stage`."""
    if not _claude_help():
        return {"error": "claude CLI not found on PATH"}
    if "--restricted" not in _claude_help():
        return {"error": "claude CLI lacks --restricted; upgrade it "
                         "(the judge must be confined to the staging dir)"}
    cmd = ["claude", "-p", PROMPT, "--model", model,
           "--output-format", "json",
           "--json-schema", json.dumps(VERDICT_SCHEMA),
           "--restricted", "--strict-mcp-config",
           "--tools", JUDGE_TOOLS, "--allowedTools", JUDGE_ALLOWED,
           "--max-turns", str(max_turns)]
    if budget:
        cmd += ["--max-budget-usd", str(budget)]
    try:
        proc = subprocess.run(cmd, cwd=stage, capture_output=True, text=True,
                              timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"error": f"claude timed out after {timeout}s"}
    if proc.returncode != 0:
        return {"error": f"claude exited {proc.returncode}: "
                         f"{(proc.stderr or proc.stdout)[:300]}"}
    try:
        result = json.loads(proc.stdout)
    except json.JSONDecodeError:
        return {"error": f"unparseable claude output: {proc.stdout[:300]}"}
    verdict = result.get("structured_output")
    if not isinstance(verdict, dict) or "verdict" not in verdict:
        verdict = extract_json(result.get("result") or "")
    if verdict is None:
        return {"error": f"no verdict in reply: "
                         f"{(result.get('result') or '')[:300]}"}
    verdict["model"] = model
    verdict["cost_usd"] = result.get("total_cost_usd")
    verdict["num_turns"] = result.get("num_turns")
    return verdict


def review_task(task_dir: Path, model: str = DEFAULT_MODEL,
                timeout: int = 900, *, max_turns: int = 40,
                budget: Optional[float] = 10.0, keep: bool = False) -> Dict:
    """Stage, judge, write llm_review.json into task_dir, clean up."""
    if not (task_dir / "Task.lean").exists():
        review = {"error": "no Task.lean"}
    else:
        stage, source = stage_task(task_dir)
        try:
            review = run_judge(stage, model, timeout, max_turns, budget)
            # One retry: a transient CLI failure must not cost a batch.
            if "error" in review:
                review = run_judge(stage, model, timeout, max_turns, budget)
            review["issued_from"] = source
            if keep:
                review["stage_dir"] = str(stage)
        finally:
            if not keep:
                shutil.rmtree(stage, ignore_errors=True)
    review["task"] = task_dir.name
    (task_dir / REVIEW_FILE).write_text(json.dumps(review, indent=2) + "\n")
    return review


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def collect_task_dirs(paths: List[Path]) -> List[Path]:
    """A task dir is reviewed as given; an output dir of run_bench.py
    contributes its PASS tasks."""
    dirs: List[Path] = []
    for p in paths:
        if (p / "Task.lean").exists():
            dirs.append(p)
            continue
        tasks_dir = p / "tasks"
        if not tasks_dir.is_dir():
            sys.exit(f"ERROR: {p} is neither a task dir nor an output dir")
        for td in sorted(tasks_dir.iterdir()):
            rf = td / "result.json"
            if not (td.is_dir() and rf.exists()):
                continue
            try:
                status = json.loads(rf.read_text()).get("status")
            except json.JSONDecodeError:
                continue
            if status == "PASS":
                dirs.append(td)
    return dirs


def flag(r: Dict, key: str) -> str:
    v = r.get(key)
    return "-" if v is None else ("ok" if v else "NO")


def print_summary(reviews: List[Dict]) -> int:
    print(f"\n  {'Task':<36} {'Verdict':<10} {'faithful':<9} {'cx':<4}")
    print("  " + "-" * 62)
    rejects = errors = 0
    for r in sorted(reviews, key=lambda x: x.get("task", "")):
        if "error" in r:
            errors += 1
            print(f"  {r['task']:<36} {'ERROR':<10} {r['error'][:60]}")
            continue
        verdict = r.get("verdict", "?")
        rejects += verdict == "REJECT"
        print(f"  {r['task']:<36} {verdict:<10} "
              f"{flag(r, 'faithful'):<9} {flag(r, 'complexity_ok'):<4}")
        for issue in r.get("issues", [])[:3]:
            print(f"      - {issue}")
    cost = sum(r.get("cost_usd") or 0 for r in reviews)
    print(f"\n  Reviewed: {len(reviews)}  REJECT: {rejects}  "
          f"ERROR: {errors}  cost: ${cost:.2f}")
    return 1 if rejects or errors else 0


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Isolated LLM review of completed tasks")
    ap.add_argument("paths", nargs="+", type=Path,
                    help="Completed task dir(s), or an output dir of "
                         "run_bench.py (its PASS tasks)")
    ap.add_argument("--model", default=DEFAULT_MODEL,
                    help=f"Judge model (default: {DEFAULT_MODEL})")
    ap.add_argument("--parallel", type=int, default=1)
    ap.add_argument("--timeout", type=int, default=900, metavar="SECONDS",
                    help="Per-review timeout (default: 900)")
    ap.add_argument("--max-turns", type=int, default=40,
                    help="Judge agent turn cap (default: 40)")
    ap.add_argument("--max-budget-usd", type=float, default=10.0,
                    help="Judge cost cap per task, 0 for none (default: 10)")
    ap.add_argument("--force", action="store_true",
                    help=f"Re-review tasks that already have a {REVIEW_FILE}")
    ap.add_argument("--keep", action="store_true",
                    help="Keep the staging dirs (path recorded in the review)")
    args = ap.parse_args()

    dirs = collect_task_dirs([p.resolve() for p in args.paths])
    reviews: List[Dict] = []
    if not args.force:
        done = [d for d in dirs if (d / REVIEW_FILE).exists()]
        for d in done:
            reviews.append(json.loads((d / REVIEW_FILE).read_text()))
        dirs = [d for d in dirs if d not in done]
        if done:
            print(f"Skipping {len(done)} already-reviewed tasks (--force to redo).")
    if not dirs and not reviews:
        sys.exit("No tasks to review.")

    print(f"Reviewing {len(dirs)} tasks with {args.model} "
          f"(parallel={args.parallel})...")
    with ThreadPoolExecutor(max_workers=max(1, args.parallel)) as pool:
        futures = {pool.submit(review_task, d, args.model, args.timeout,
                               max_turns=args.max_turns,
                               budget=args.max_budget_usd or None,
                               keep=args.keep): d for d in dirs}
        for fut in as_completed(futures):
            r = fut.result()
            print(f"  {r.get('verdict', 'ERROR'):>9}  {r['task']}")
            reviews.append(r)

    sys.exit(print_summary(reviews))


if __name__ == "__main__":
    main()
