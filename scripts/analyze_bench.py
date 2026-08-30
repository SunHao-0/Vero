#!/usr/bin/env python3
"""
Analysis of Lean4 benchmark results.

Reads <output-dir>/tasks/<name>/result.json + logs/transcript.jsonl
produced by run_bench.py and prints a report: status summary, recovery
deltas after re-running check.sh, FAIL/TIMEOUT/ERROR breakdowns,
PASS-task activity stats, and a per-task table.

Usage:
    python analyze_bench.py --output-dir /path/to/bench_output
    python analyze_bench.py --output-dir /path/to/bench_output --skip-recheck
    python analyze_bench.py --output-dir /path/to/bench_output --parallel 8
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


BENCH_ROOT = Path(__file__).resolve().parent.parent


@dataclass
class Recheck:
    """Outcome of re-running check.sh against a task."""
    original_status: str
    new_status: str
    exit_code: Optional[int] = None
    failures: List[str] = field(default_factory=list)

    @property
    def changed(self) -> bool:
        return self.original_status != self.new_status


# ---------------------------------------------------------------------------
# Re-check logic
# ---------------------------------------------------------------------------

def run_check(task_dir: Path, timeout: int = 600) -> Tuple[int, str]:
    """Run check.sh in the task directory. Returns (exit_code, output)."""
    try:
        result = subprocess.run(
            ["./check.sh"],
            cwd=str(task_dir),
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        output = result.stdout + result.stderr
        return result.returncode, output
    except subprocess.TimeoutExpired:
        return -1, "TIMEOUT running check.sh"
    except Exception as e:
        return -2, str(e)


def _seed_lake_cache(lake_staging: Path, first_task_dir: Path) -> None:
    """Download the mathlib cache via `lake exec cache get` into lake_staging."""
    print(f"  No .lake cache found; running `lake exec cache get` in {first_task_dir.name}...")
    try:
        result = subprocess.run(
            ["lake", "exec", "cache", "get"],
            cwd=str(first_task_dir),
            capture_output=True,
            text=True,
            timeout=600,
        )
    except subprocess.TimeoutExpired:
        print("  WARNING: `lake exec cache get` timed out (600s)")
        return
    except Exception as e:
        print(f"  WARNING: `lake exec cache get` failed: {e}")
        return

    candidate = first_task_dir / ".lake"
    if result.returncode == 0 and candidate.exists() and not candidate.is_symlink():
        shutil.move(str(candidate), str(lake_staging))
        print(f"  Mathlib cache ready")
    else:
        print(f"  WARNING: Cache download failed (exit {result.returncode}): "
              f"{result.stderr[:200]}")


_ANSI = re.compile(r'\x1b\[[0-9;]*m')


def _extract_failures(output: str) -> List[str]:
    """Pick up FAIL/INCOMPLETE lines from check.sh output, ANSI-stripped."""
    return [
        stripped for line in output.splitlines()
        for stripped in [_ANSI.sub('', line)]
        if stripped.startswith(("FAIL", "INCOMPLETE"))
    ]


def _link_lake_cache(task_dir: Path, lake_staging: Path) -> bool:
    """Replace task_dir/.lake with a symlink to lake_staging. Return True if created."""
    task_lake = task_dir / ".lake"
    if task_lake.is_symlink():
        task_lake.unlink()
    elif task_lake.exists():
        shutil.rmtree(task_lake, ignore_errors=True)
    os.symlink(str(lake_staging), str(task_lake))
    return True


def _recheck_one_task(
    task_dir: Path,
    source_tasks_dir: Path,
    lake_staging: Optional[Path],
) -> Tuple[str, Recheck]:
    """Re-run check.sh against one task (with a fresh check.sh + shared .lake)."""
    name = task_dir.name
    original_status = json.loads((task_dir / "result.json").read_text())["status"]

    # Use the pristine check.sh from the source tree in case the solver tampered.
    src_check = source_tasks_dir / name / "check.sh"
    if src_check.exists():
        dst_check = task_dir / "check.sh"
        shutil.copy2(src_check, dst_check)
        dst_check.chmod(dst_check.stat().st_mode | 0o111)

    linked = bool(lake_staging and lake_staging.exists()) and _link_lake_cache(
        task_dir, lake_staging
    )
    try:
        exit_code, output = run_check(task_dir)
    finally:
        if linked and (task_dir / ".lake").is_symlink():
            (task_dir / ".lake").unlink()

    return name, Recheck(
        original_status=original_status,
        new_status="PASS" if exit_code == 0 else "FAIL",
        exit_code=exit_code,
        failures=_extract_failures(output),
    )


def _format_recheck_line(r: Recheck, name: str, i: int, total: int) -> Optional[str]:
    """Format a per-task progress line — or None if it's uninteresting."""
    if not (r.changed or r.new_status == "FAIL"):
        return None
    marker = "+" if r.new_status == "PASS" else "x"
    suffix = f" [{r.original_status} -> {r.new_status}]" if r.changed else ""
    if r.failures:
        suffix += f" ({r.failures[0]})"
    return f"  {marker} [{i:3}/{total}] {name}{suffix}"


def recheck_tasks(
    output_dir: Path,
    parallel: int = 1,
) -> Dict[str, Recheck]:
    """Re-run check.sh on PASS and FAIL tasks (TIMEOUT/ERROR are kept as-is).

    A shared .lake cache is seeded once and symlinked into each task
    directory during checking, so parallel workers don't thrash mathlib.
    """
    source_tasks_dir = BENCH_ROOT / "tasks"
    tasks_dir = output_dir / "tasks"
    results: Dict[str, Recheck] = {}

    all_task_dirs = [
        td for td in sorted(tasks_dir.iterdir())
        if td.is_dir() and (td / "result.json").exists()
    ]

    to_recheck: List[Path] = []
    for td in all_task_dirs:
        status = json.loads((td / "result.json").read_text())["status"]
        if status in ("PASS", "FAIL"):
            to_recheck.append(td)
        else:
            results[td.name] = Recheck(original_status=status, new_status=status)

    if not to_recheck:
        print("  No PASS/FAIL tasks found to recheck.")
        return results

    lake_staging = output_dir / ".lake_recheck_cache"
    shutil.rmtree(lake_staging, ignore_errors=True)
    for td in to_recheck:
        candidate = td / ".lake"
        if candidate.is_symlink():
            candidate.unlink()
        elif candidate.exists():
            shutil.rmtree(candidate, ignore_errors=True)
    _seed_lake_cache(lake_staging, to_recheck[0])

    print(f"  Rechecking {len(to_recheck)} PASS/FAIL tasks (parallel={parallel})...")

    # Single execution path: ThreadPoolExecutor handles parallel=1 fine.
    total = len(to_recheck)
    with ThreadPoolExecutor(max_workers=max(1, parallel)) as pool:
        futures = {
            pool.submit(_recheck_one_task, td, source_tasks_dir, lake_staging): td
            for td in to_recheck
        }
        for i, future in enumerate(as_completed(futures), 1):
            name, r = future.result()
            results[name] = r
            line = _format_recheck_line(r, name, i, total)
            if line is not None:
                print(line)
            elif i % 20 == 0 or i == total:
                print(f"  ... {i}/{total} checked")

    if lake_staging.exists():
        shutil.rmtree(lake_staging, ignore_errors=True)

    # Persist status changes so run_bench.py --resume sees the new truth.
    changed = 0
    for name, r in results.items():
        if not r.changed:
            continue
        result_file = tasks_dir / name / "result.json"
        if result_file.exists():
            data = json.loads(result_file.read_text())
            data["status"] = r.new_status
            result_file.write_text(json.dumps(data, indent=2) + "\n")
            changed += 1
    if changed:
        print(f"  Updated {changed} result.json files with new status.")

    return results


# ---------------------------------------------------------------------------
# Transcript parsing
# ---------------------------------------------------------------------------

TOOL_CATEGORIES = {
    "Read": "read",
    "Glob": "read",
    "Grep": "read",
    "ToolSearch": "read",
    "Edit": "edit",
    "Write": "edit",
    "Bash": "bash",
    "mcp__lean-lsp__lean_goal": "lean_debug",
    "mcp__lean-lsp__lean_diagnostic_messages": "lean_debug",
    "mcp__lean-lsp__lean_run_code": "lean_debug",
    "mcp__lean-lsp__lean_leanfinder": "lean_search",
    "mcp__lean-lsp__lean_leansearch": "lean_search",
    "mcp__lean-lsp__lean_loogle": "lean_search",
    "mcp__lean-lsp__lean_local_search": "lean_search",
    "mcp__lean-lsp__lean_multi_attempt": "lean_prove",
    "TodoWrite": "other",
    "NotebookEdit": "other",
}


def categorize_tool(name: str) -> str:
    return TOOL_CATEGORIES.get(name, "other")


def is_implementation_edit(tool_name: str, tool_input: dict) -> bool:
    """Heuristic: is this edit to the implementation section?"""
    if tool_name not in ("Edit", "Write"):
        return False
    content = str(tool_input.get("new_string", "") + tool_input.get("content", ""))
    path = str(tool_input.get("file_path", ""))
    if "Task.lean" not in path and "task.lean" not in path.lower():
        return False
    return "IMPLEMENTATION" in content.upper() or "BEGIN: IMPLEMENTATION" in content.upper()


def is_proof_edit(tool_name: str, tool_input: dict) -> bool:
    """Heuristic: is this edit to the proof section?"""
    if tool_name not in ("Edit", "Write"):
        return False
    path = str(tool_input.get("file_path", ""))
    if "Task.lean" not in path and "task.lean" not in path.lower():
        return False
    content = str(tool_input.get("new_string", "") + tool_input.get("content", ""))
    return "PROOF" in content.upper() or "BEGIN: PROOF" in content.upper()


def parse_transcript(transcript_path: Path) -> Dict[str, Any]:
    """Parse a transcript.jsonl file and extract all metrics."""
    stats = {
        "turns": 0,
        "cost_usd": 0.0,
        "total_input_tokens": 0,
        "total_output_tokens": 0,
        "total_cache_read_tokens": 0,
        "total_cache_creation_tokens": 0,
        "tool_calls": Counter(),
        "tool_categories": Counter(),
        "duration_ms": 0,
        "duration_api_ms": 0,
        "stop_reason": "",
        "is_rate_limited": False,
        "is_error": False,
        "result_text": "",
        "phase_counts": Counter(),
        "impl_edits": 0,
        "proof_edits": 0,
        "check_sh_runs": 0,
        "per_turn": [],
        "_assistant_msgs": 0,
    }

    if not transcript_path.exists():
        return stats

    lines = transcript_path.read_text(encoding="utf-8").splitlines()

    current_turn_tools = []
    current_turn_input = 0
    current_turn_output = 0

    for line in lines:
        if not line.strip():
            continue
        try:
            d = json.loads(line)
        except json.JSONDecodeError:
            continue

        t = d.get("type", "")

        if t == "rate_limit_event":
            stats["is_rate_limited"] = True

        elif t == "result":
            stats["cost_usd"] = d.get("total_cost_usd", 0.0) or 0.0
            stats["turns"] = d.get("num_turns", 0)
            stats["duration_ms"] = d.get("duration_ms", 0)
            stats["duration_api_ms"] = d.get("duration_api_ms", 0)
            stats["stop_reason"] = d.get("stop_reason", "")
            stats["is_error"] = d.get("is_error", False)
            stats["result_text"] = d.get("result", "") or ""

        elif t == "assistant":
            stats["_assistant_msgs"] += 1
            msg = d.get("message", {})
            usage = msg.get("usage", {})
            inp = usage.get("input_tokens", 0) + usage.get("cache_read_input_tokens", 0) + usage.get("cache_creation_input_tokens", 0)
            out = usage.get("output_tokens", 0)
            stats["total_input_tokens"] += inp
            stats["total_output_tokens"] += out
            stats["total_cache_read_tokens"] += usage.get("cache_read_input_tokens", 0)
            stats["total_cache_creation_tokens"] += usage.get("cache_creation_input_tokens", 0)

            current_turn_input += inp
            current_turn_output += out

            for content_item in msg.get("content", []):
                if content_item.get("type") == "tool_use":
                    tool_name = content_item.get("name", "unknown")
                    tool_input = content_item.get("input", {})
                    stats["tool_calls"][tool_name] += 1
                    cat = categorize_tool(tool_name)
                    stats["tool_categories"][cat] += 1
                    stats["phase_counts"][cat] += 1
                    current_turn_tools.append(tool_name)

                    if tool_name == "Bash":
                        cmd = str(tool_input.get("command", ""))
                        if "check.sh" in cmd:
                            stats["check_sh_runs"] += 1

                    if is_implementation_edit(tool_name, tool_input):
                        stats["impl_edits"] += 1

                    if is_proof_edit(tool_name, tool_input):
                        stats["proof_edits"] += 1

            content_types = [c.get("type") for c in msg.get("content", [])]
            if "tool_use" not in content_types:
                stats["per_turn"].append({
                    "tools": list(current_turn_tools),
                    "input_tokens": current_turn_input,
                    "output_tokens": current_turn_output,
                })
                current_turn_tools = []
                current_turn_input = 0
                current_turn_output = 0

    if stats["turns"] == 0 and stats["_assistant_msgs"] > 0:
        stats["turns"] = stats["_assistant_msgs"]

    return stats


# ---------------------------------------------------------------------------
# Per-task record
# ---------------------------------------------------------------------------

@dataclass
class TaskRecord:
    name: str
    original_status: str
    effective_status: str
    elapsed_s: float
    solver_exit: Optional[int]
    check_exit: Optional[int]
    meta: Dict[str, Any]
    transcript: Dict[str, Any]
    recheck: Optional[Recheck]
    timeout_cause: Optional[str]
    error_cause: Optional[str]


def _classify_timeout(ts: Dict[str, Any]) -> str:
    if ts["is_rate_limited"]:
        return "rate_limit"
    if ts["stop_reason"] == "":
        return "hard_timeout"
    return "hard_problem"


def _classify_error(ts: Dict[str, Any]) -> str:
    text = ts["result_text"].lower()
    if "rate" in text or "limit" in text:
        return "rate_limit"
    if ts["is_error"]:
        return "solver_error"
    return "unknown"


def _read_json(path: Path) -> Dict[str, Any]:
    try:
        return json.loads(path.read_text())
    except Exception:
        return {}


def _build_task_record(
    task_dir: Path, rechecks: Optional[Dict[str, Recheck]],
) -> Optional[TaskRecord]:
    result_file = task_dir / "result.json"
    if not (task_dir.is_dir() and result_file.exists()):
        return None

    result = json.loads(result_file.read_text())
    ts = parse_transcript(task_dir / "logs" / "transcript.jsonl")
    recheck = rechecks.get(task_dir.name) if rechecks else None

    return TaskRecord(
        name=task_dir.name,
        original_status=result["status"],
        effective_status=recheck.new_status if recheck else result["status"],
        elapsed_s=result["elapsed_s"],
        solver_exit=result["solver_exit"],
        check_exit=result["check_exit"],
        meta=_read_json(task_dir / "logs" / "meta.json"),
        transcript=ts,
        recheck=recheck,
        timeout_cause=_classify_timeout(ts) if result["status"] == "TIMEOUT" else None,
        error_cause=_classify_error(ts) if result["status"] == "ERROR" else None,
    )


# ---------------------------------------------------------------------------
# Formatting helpers
# ---------------------------------------------------------------------------

_STATUSES = ("PASS", "FAIL", "TIMEOUT", "ERROR")


def _stats_str(vals: List[float], fmt: str = ".1f") -> str:
    if not vals:
        return "N/A"
    s = sorted(vals)
    mean = sum(s) / len(s)
    p50 = s[len(s) // 2]
    p90 = s[int(len(s) * 0.9)]
    return (f"mean={mean:{fmt}}, p50={p50:{fmt}}, p90={p90:{fmt}}, "
            f"min={s[0]:{fmt}}, max={s[-1]:{fmt}}")


class Section:
    """Auto-numbered '## N. TITLE' emitter."""
    def __init__(self) -> None:
        self._n = 0

    def __call__(self, title: str) -> None:
        self._n += 1
        print(f"\n## {self._n}. {title}")


# ---------------------------------------------------------------------------
# Report sections
# ---------------------------------------------------------------------------

def _print_summary(tasks: List[TaskRecord], has_recheck: bool, section: Section) -> None:
    section("STATUS SUMMARY")
    orig = Counter(t.original_status for t in tasks)
    eff = Counter(t.effective_status for t in tasks)
    if has_recheck:
        print(f"\n  {'Status':<12} {'Original':>10} {'After recheck':>14}")
        print("  " + "-" * 38)
        for s in _STATUSES:
            delta = f"  (D {eff[s] - orig[s]:+d})" if eff[s] != orig[s] else ""
            print(f"  {s:<12} {orig[s]:>10} {eff[s]:>14}{delta}")
    else:
        print(f"\n  {'Status':<12} {'Count':>8}")
        print("  " + "-" * 22)
        for s in _STATUSES:
            print(f"  {s:<12} {orig[s]:>8}")
    print(f"  {'TOTAL':<12} {len(tasks):>10}")


def _print_status_changes(tasks: List[TaskRecord], section: Section) -> None:
    recovered = [t for t in tasks if t.original_status != "PASS" and t.effective_status == "PASS"]
    regressed = [t for t in tasks if t.original_status == "PASS" and t.effective_status != "PASS"]
    if not (recovered or regressed):
        return
    section("STATUS CHANGES")
    if recovered:
        print(f"\n  Recovered ({len(recovered)} tasks -> PASS):")
        for t in sorted(recovered, key=lambda x: x.name):
            print(f"    + {t.name:<20} {t.original_status:<8} -> PASS  "
                  f"(elapsed={t.elapsed_s:.0f}s)")
    if regressed:
        print(f"\n  Regressed ({len(regressed)} tasks, PASS -> non-PASS):")
        for t in sorted(regressed, key=lambda x: x.name):
            failures = "; ".join(t.recheck.failures[:2]) if t.recheck and t.recheck.failures else "unknown"
            print(f"    x {t.name:<20} PASS    -> {t.effective_status:<8}  ({failures})")


def _print_failures(tasks: List[TaskRecord], section: Section) -> None:
    fails = [t for t in tasks if t.effective_status == "FAIL"]
    section(f"FAIL ANALYSIS ({len(fails)} tasks)")
    for t in fails:
        if t.recheck:
            failures = "; ".join(t.recheck.failures) if t.recheck.failures else "none"
            label = (f"{t.original_status} -> {t.effective_status}"
                     if t.original_status != t.effective_status else t.effective_status)
            print(f"\n  {t.name}: {label}")
            print(f"    Failures: {failures}")
        else:
            print(f"\n  {t.name}: {t.original_status} (not rechecked)")


def _print_timeouts(tasks: List[TaskRecord], section: Section) -> None:
    timeouts = [t for t in tasks if t.original_status == "TIMEOUT"]
    section(f"TIMEOUT ANALYSIS ({len(timeouts)} tasks)")
    for t in timeouts:
        ts = t.transcript
        print(f"\n  {t.name}: elapsed={t.elapsed_s:.0f}s, turns={ts['turns']}, "
              f"cost=${ts['cost_usd']:.3f}, cause={t.timeout_cause}")
        if ts["result_text"]:
            print(f"    result: {ts['result_text'][:120]}")


def _print_errors(tasks: List[TaskRecord], section: Section) -> None:
    errors = [t for t in tasks if t.original_status == "ERROR"]
    section(f"ERROR ANALYSIS ({len(errors)} tasks)")
    for t in errors:
        ts = t.transcript
        print(f"\n  {t.name}: elapsed={t.elapsed_s:.0f}s, turns={ts['turns']}, "
              f"cause={t.error_cause}")
        if ts["result_text"]:
            print(f"    result: {ts['result_text'][:120]}")


def _print_pass_analysis(tasks: List[TaskRecord], section: Section) -> None:
    pass_tasks = [t for t in tasks if t.effective_status == "PASS"]
    section(f"PASS DETAILED ANALYSIS ({len(pass_tasks)} tasks)")

    elapsed = [t.elapsed_s for t in pass_tasks]
    turns = [t.transcript["turns"] for t in pass_tasks]
    costs = [t.transcript["cost_usd"] for t in pass_tasks if t.transcript["cost_usd"] > 0]
    inputs = [t.transcript["total_input_tokens"] for t in pass_tasks]
    outputs = [t.transcript["total_output_tokens"] for t in pass_tasks]

    print(f"\n  Time (seconds):    {_stats_str(elapsed, '.0f')}")
    print(f"  Turns:             {_stats_str(turns, '.0f')}")
    if costs:
        print(f"  Cost (USD):        {_stats_str(costs, '.3f')}")
        print(f"  Total cost (PASS): ${sum(costs):.2f}")
    print(f"  Input tokens:      {_stats_str(inputs, '.0f')}")
    print(f"  Output tokens:     {_stats_str(outputs, '.0f')}")

    _print_tool_breakdown(pass_tasks)
    _print_activity_breakdown(pass_tasks)
    _print_difficulty_buckets(pass_tasks)
    _print_hardest_pass(pass_tasks)
    _print_cache_efficiency(pass_tasks)


def _print_tool_breakdown(pass_tasks: List[TaskRecord]) -> None:
    all_tools: Counter = Counter()
    all_cats: Counter = Counter()
    for t in pass_tasks:
        all_tools.update(t.transcript["tool_calls"])
        all_cats.update(t.transcript["tool_categories"])
    n = max(len(pass_tasks), 1)

    print("\n  ### Tool Category Breakdown (across all PASS tasks)")
    total = sum(all_cats.values()) or 1
    for cat, count in sorted(all_cats.items(), key=lambda x: -x[1]):
        print(f"    {cat:<15} {count:>6} calls  ({100 * count / total:.1f}%)  "
              f"avg/task={count / n:.1f}")

    print("\n  ### Top Tools (across all PASS tasks)")
    for tool, count in all_tools.most_common(15):
        print(f"    {tool:<45} {count:>6}  avg/task={count / n:.1f}")


def _print_activity_breakdown(pass_tasks: List[TaskRecord]) -> None:
    rows = [
        ("impl edits",        [t.transcript["impl_edits"] for t in pass_tasks]),
        ("proof edits",       [t.transcript["proof_edits"] for t in pass_tasks]),
        ("check.sh runs",     [t.transcript["check_sh_runs"] for t in pass_tasks]),
        ("lean debug calls",  [t.transcript["tool_categories"].get("lean_debug", 0) for t in pass_tasks]),
        ("lean search calls", [t.transcript["tool_categories"].get("lean_search", 0) for t in pass_tasks]),
        ("lean prove calls",  [t.transcript["tool_categories"].get("lean_prove", 0) for t in pass_tasks]),
    ]
    print("\n  ### Activity Breakdown (avg per task, PASS only)")
    for label, vals in rows:
        print(f"    {label:<18} {_stats_str(vals, '.1f')}")


# (label, lower_bound_seconds, upper_bound_seconds)
_DIFFICULTY_BUCKETS: List[Tuple[str, float, float]] = [
    ("< 5min",   0,    300),
    ("5-15min",  300,  900),
    ("15-30min", 900,  1800),
    ("30-60min", 1800, 3600),
    ("> 60min",  3600, float("inf")),
]


def _print_difficulty_buckets(pass_tasks: List[TaskRecord]) -> None:
    print("\n  ### Difficulty Distribution (by elapsed time, PASS tasks)")
    for label, lo, hi in _DIFFICULTY_BUCKETS:
        count = sum(1 for t in pass_tasks if lo <= t.elapsed_s < hi)
        print(f"    {label:<12}: {count:>3} tasks")


def _print_hardest_pass(pass_tasks: List[TaskRecord]) -> None:
    print("\n  ### Hardest PASS tasks (by time)")
    for t in sorted(pass_tasks, key=lambda t: -t.elapsed_s)[:10]:
        ts = t.transcript
        print(f"    {t.name:<20} {t.elapsed_s:>6.0f}s  "
              f"turns={ts['turns']:>3}  cost=${ts['cost_usd']:.3f}  "
              f"check_runs={ts['check_sh_runs']}")


def _print_cache_efficiency(pass_tasks: List[TaskRecord]) -> None:
    cache_pcts = [
        100 * t.transcript["total_cache_read_tokens"] / t.transcript["total_input_tokens"]
        for t in pass_tasks if t.transcript["total_input_tokens"] > 0
    ]
    if not cache_pcts:
        return
    print("\n  ### Token/Cache efficiency (PASS tasks)")
    print(f"    Cache read %: {_stats_str(cache_pcts, '.1f')}")


def _print_full_table(tasks: List[TaskRecord], section: Section) -> None:
    section("FULL TASK TABLE")
    print(f"\n  {'Task':<20} {'Status':<10} {'Time(s)':>8} {'Turns':>6} "
          f"{'Cost($)':>8} {'InTok':>7} {'OutTok':>7} {'Tools':>6}")
    print("  " + "-" * 82)
    for t in tasks:
        ts = t.transcript
        status = (f"{t.original_status}->{t.effective_status}"
                  if t.original_status != t.effective_status else t.effective_status)
        print(f"  {t.name:<20} {status:<10} {t.elapsed_s:>8.0f} "
              f"{ts['turns']:>6} {ts['cost_usd']:>8.3f} "
              f"{ts['total_input_tokens']:>7} {ts['total_output_tokens']:>7} "
              f"{sum(ts['tool_calls'].values()):>6}")

    costs = [t.transcript["cost_usd"] for t in tasks if t.transcript["cost_usd"] > 0]
    total_hours = sum(t.elapsed_s for t in tasks) / 3600
    print(f"\n  Total wall time: {total_hours:.1f} hours")
    if costs and tasks:
        print(f"  Total cost: ${sum(costs):.2f}")
        print(f"  Avg cost per task: ${sum(costs) / len(tasks):.3f}")


# ---------------------------------------------------------------------------
# Main analysis
# ---------------------------------------------------------------------------

def analyze(output_dir: Path, rechecks: Optional[Dict[str, Recheck]] = None) -> None:
    tasks_dir = output_dir / "tasks"
    tasks = [
        rec for task_dir in sorted(tasks_dir.iterdir())
        for rec in [_build_task_record(task_dir, rechecks)] if rec is not None
    ]

    print("\n" + "=" * 70)
    print("LEAN4 BENCHMARK ANALYSIS REPORT")
    print("=" * 70)

    has_recheck = rechecks is not None
    section = Section()
    _print_summary(tasks, has_recheck, section)
    if has_recheck:
        _print_status_changes(tasks, section)
    _print_failures(tasks, section)
    _print_timeouts(tasks, section)
    _print_errors(tasks, section)
    _print_pass_analysis(tasks, section)
    _print_full_table(tasks, section)

    print("\n" + "=" * 70)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="Analyze Lean4 benchmark results")
    parser.add_argument(
        "--output-dir", required=True,
        help="Path to the benchmark output directory",
    )
    parser.add_argument(
        "--skip-recheck", action="store_true",
        help="Skip re-running check.sh (by default, PASS and FAIL tasks are rechecked)",
    )
    parser.add_argument(
        "--parallel", type=int, default=1,
        help="Number of parallel workers for rechecking (default: 1)",
    )
    args = parser.parse_args()

    output_dir = Path(args.output_dir).resolve()
    tasks_dir = output_dir / "tasks"
    if not tasks_dir.exists():
        print(f"ERROR: no tasks found at: {tasks_dir}", file=sys.stderr)
        sys.exit(1)

    rechecks: Optional[Dict[str, Recheck]] = None
    if not args.skip_recheck:
        print(f"\nRechecking PASS/FAIL tasks in {output_dir}...")
        rechecks = recheck_tasks(output_dir, parallel=args.parallel)

    analyze(output_dir, rechecks)


if __name__ == "__main__":
    main()
