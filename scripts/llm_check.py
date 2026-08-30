#!/usr/bin/env python3
"""LLM review of benchmark submissions.

check.sh decides the machine-checkable gates; this script asks an agent
for the human-level judgment: the provided spec is untouched, the proof
is faithful, and the implementation meets the task's complexity rule
rather than brute-forcing. The verdict is written next to each
submission (llm_review.json) and summarized on stdout.

Usage:
    python3 scripts/llm_check.py ./results                 # PASS tasks of a run
    python3 scripts/llm_check.py ./results --statuses PASS,FAIL
    python3 scripts/llm_check.py solved/TnumStepUp --force # one task dir

Requires the `claude` CLI and its auth token (CLAUDE_CODE_OAUTH_TOKEN or
ANTHROPIC_API_KEY) on the host.
"""

import argparse
import difflib
import json
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Dict, List, Optional

BENCH_ROOT = Path(__file__).resolve().parent.parent
REVIEW_FILE = "llm_review.json"
DEFAULT_MODEL = "claude-opus-5"

PROMPT = """You are an expert reviewer for the Vero verified code generation \
benchmark. A solver received a Lean 4 task file with locked (provided) sections \
and editable sections (IMPLEMENTATION, AUX, PROOF), plus the instruction below. \
The automated gates (integrity hash, forbidden-pattern scan, lake compilation, \
#print axioms) have already run; you make the judgment they cannot.

Judge three criteria:
1. spec_unmodified: the diff touches only editable sections. Any change to \
provided text, section markers, or the gaps between provided sections that \
weakens the task is a violation. Use the integrity-gate line below: when it \
is PASS, the provided sections are hash-verified against the issued task, \
and any provided-section difference in the diff is drift of the benchmark \
itself since the submission, not a solver edit.
2. proof_faithful: the proof honestly establishes the provided theorem: no \
spec mirroring, no decidability or enumeration escape, no metaprogramming or \
axiom trickery, no exploitation of Lean internals. Heavy use of standard \
automation (bv_decide, simp, omega, decide on small goals) is acceptable.
3. complexity_ok: the implementation obeys the complexity rule stated in the \
instruction. Brute force scores zero: any strategy whose running time scales \
with the number of concrete values represented (enumerating a concretization, \
2^popcount case explosion, tree recursion that branches at each bit position) \
rather than with the bit-width. Recursion depth 64 does not imply bounded \
time. If the instruction imposes no complexity rule, judge against the \
intended algorithm described in the task header.

Reply with ONLY a JSON object, no other text:
{"verdict": "ACCEPT" | "REJECT" | "UNCERTAIN",
 "spec_unmodified": true | false,
 "proof_faithful": true | false,
 "complexity_ok": true | false,
 "issues": ["short description of each problem found"],
 "summary": "one or two sentences"}

Integrity gate (hash of provided sections vs .provided_hash): {integrity}

=== INSTRUCTION.md ===
{instruction}

=== DIFF (pristine task vs submission; empty sections in the pristine file) ===
{diff}

=== SUBMITTED Task.lean ===
{submission}
"""


def pristine_text(task_dir: Path) -> Optional[str]:
    """The task file as the solver received it.

    An output dir is a git repo whose initial commit holds the clean task
    copies (run_bench.py commits them before the solver runs), so that
    blob is version-exact. Fall back to the bench tree, matched by full
    or unprefixed name (TnumStepUp -> eBPF_TnumStepUp); this can carry
    benchmark drift, which the integrity gate disambiguates.
    """
    root = task_dir.parent.parent
    rel = f"tasks/{task_dir.name}/Task.lean"
    if (root / ".git").exists():
        log = subprocess.run(
            ["git", "-C", str(root), "log", "--format=%H",
             "--diff-filter=A", "--", rel],
            capture_output=True, text=True)
        commits = log.stdout.split()
        if commits:
            show = subprocess.run(
                ["git", "-C", str(root), "show", f"{commits[-1]}:{rel}"],
                capture_output=True, text=True)
            if show.returncode == 0:
                return show.stdout
    tasks_dir = BENCH_ROOT / "tasks"
    for d in [tasks_dir / task_dir.name] + sorted(tasks_dir.iterdir()):
        if d.is_dir() and (d.name == task_dir.name
                           or d.name.endswith("_" + task_dir.name)):
            return (d / "Task.lean").read_text(errors="replace")
    return None


def integrity_gate(task_dir: Path) -> str:
    """Reuse check.sh as the canonical hash check: PASS, FAIL, or
    UNKNOWN (no check.sh or no .provided_hash)."""
    if not (task_dir / "check.sh").exists():
        return "UNKNOWN"
    proc = subprocess.run(["./check.sh", "--check-integrity"],
                          cwd=task_dir, capture_output=True, text=True)
    if "SKIP" in proc.stdout:
        return "UNKNOWN"
    return "PASS" if proc.returncode == 0 else "FAIL"


def build_prompt(task_dir: Path) -> str:
    submission = (task_dir / "Task.lean").read_text(errors="replace")
    instruction = (task_dir / "INSTRUCTION.md").read_text(errors="replace")
    pristine = pristine_text(task_dir)
    if pristine is not None:
        diff = "".join(difflib.unified_diff(
            pristine.splitlines(keepends=True),
            submission.splitlines(keepends=True),
            fromfile="pristine/Task.lean", tofile="submitted/Task.lean"))
        if not diff:
            diff = "(no changes: the submission is identical to the pristine task)"
    else:
        diff = "(pristine task file not found; judge from the submission alone)"
    return (PROMPT.replace("{instruction}", instruction)
                  .replace("{integrity}", integrity_gate(task_dir))
                  .replace("{diff}", diff)
                  .replace("{submission}", submission))


def extract_json(text: str) -> Optional[Dict]:
    """Parse the verdict object from the model's reply, tolerating code
    fences or prose around it."""
    m = re.search(r"\{.*\}", text, re.S)
    if not m:
        return None
    try:
        d = json.loads(m.group(0))
    except json.JSONDecodeError:
        return None
    return d if isinstance(d, dict) and "verdict" in d else None


def run_claude(prompt: str, model: str, timeout: int) -> Dict:
    """One review call. No tools are allowed and permissions are not
    skipped, so in -p mode any stray tool call is denied and the model
    must answer from the prompt alone."""
    cmd = ["claude", "-p", prompt, "--model", model,
           "--output-format", "json", "--max-turns", "4"]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"error": f"claude timed out after {timeout}s"}
    except FileNotFoundError:
        return {"error": "claude CLI not found on PATH"}
    if proc.returncode != 0:
        return {"error": f"claude exited {proc.returncode}: "
                         f"{(proc.stderr or proc.stdout)[:300]}"}
    try:
        result = json.loads(proc.stdout)
    except json.JSONDecodeError:
        return {"error": f"unparseable claude output: {proc.stdout[:300]}"}
    verdict = extract_json(result.get("result", "") or "")
    if verdict is None:
        return {"error": f"no JSON verdict in reply: "
                         f"{(result.get('result') or '')[:300]}"}
    verdict["model"] = model
    verdict["cost_usd"] = result.get("total_cost_usd")
    return verdict


def review_task(task_dir: Path, model: str, timeout: int) -> Dict:
    review = run_claude(build_prompt(task_dir), model, timeout)
    # One retry: a transient CLI failure must not cost a whole batch.
    if "error" in review:
        review = run_claude(build_prompt(task_dir), model, timeout)
    review["task"] = task_dir.name
    (task_dir / REVIEW_FILE).write_text(json.dumps(review, indent=2) + "\n")
    return review


def collect_task_dirs(paths: List[Path], statuses: List[str]) -> List[Path]:
    """Each path is an output dir (reviews its tasks with a matching
    result.json status) or a single task dir (reviewed unconditionally)."""
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
            if status in statuses:
                dirs.append(td)
    return dirs


def print_summary(reviews: List[Dict]) -> int:
    def flag(r, key):
        v = r.get(key)
        return "-" if v is None else ("ok" if v else "NO")

    print(f"\n  {'Task':<36} {'Verdict':<10} {'spec':<5} {'proof':<6} {'cx':<4}")
    print("  " + "-" * 66)
    rejects = errors = 0
    for r in sorted(reviews, key=lambda x: x.get("task", "")):
        if "error" in r:
            errors += 1
            print(f"  {r['task']:<36} {'ERROR':<10} {r['error'][:60]}")
            continue
        verdict = r.get("verdict", "?")
        rejects += verdict == "REJECT"
        print(f"  {r['task']:<36} {verdict:<10} "
              f"{flag(r, 'spec_unmodified'):<5} {flag(r, 'proof_faithful'):<6} "
              f"{flag(r, 'complexity_ok'):<4}")
        for issue in r.get("issues", [])[:3]:
            print(f"      - {issue}")
    cost = sum(r.get("cost_usd") or 0 for r in reviews)
    print(f"\n  Reviewed: {len(reviews)}  REJECT: {rejects}  "
          f"ERROR: {errors}  cost: ${cost:.2f}")
    return 1 if rejects or errors else 0


def main() -> None:
    ap = argparse.ArgumentParser(description="LLM review of submissions")
    ap.add_argument("paths", nargs="+", type=Path,
                    help="Output dir(s) from run_bench.py, or task dir(s)")
    ap.add_argument("--model", default=DEFAULT_MODEL,
                    help=f"Reviewer model (default: {DEFAULT_MODEL})")
    ap.add_argument("--statuses", default="PASS",
                    help="Statuses to review in an output dir (default: PASS)")
    ap.add_argument("--parallel", type=int, default=1)
    ap.add_argument("--timeout", type=int, default=600, metavar="SECONDS",
                    help="Per-review timeout (default: 600)")
    ap.add_argument("--force", action="store_true",
                    help=f"Re-review tasks that already have a {REVIEW_FILE}")
    args = ap.parse_args()

    statuses = [s.strip() for s in args.statuses.split(",")]
    dirs = collect_task_dirs([p.resolve() for p in args.paths], statuses)
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
        futures = {pool.submit(review_task, d, args.model, args.timeout): d
                   for d in dirs}
        for fut in as_completed(futures):
            r = fut.result()
            state = r.get("verdict", "ERROR")
            print(f"  {state:>9}  {r['task']}")
            reviews.append(r)

    sys.exit(print_summary(reviews))


if __name__ == "__main__":
    main()
