#!/usr/bin/env python3
"""Summarize a benchmark run into the compact JSON the website reads.

A run directory holds one sub-directory per task with result.json and the
solver transcript. Those are large (hundreds of MB) and contain the agent's
tool inputs -- including the Lean code of solutions that are not published
yet. This script keeps only aggregate numbers: outcome, wall time, cost,
turns, token totals, per-category tool-call counts, and a bucketed activity
profile. No command, file path, prompt, or session id is ever written out,
so the result is safe to commit next to the public site.

Usage:
    python3 scripts/collect_runs.py <run-dir> --id opus5 \
        --model claude-opus-5 --label "Claude Opus 5"

<run-dir> is either an output directory produced by run_bench.py (tasks live
in <run-dir>/tasks/) or a directory of task directories such as solved/.
"""
import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path

BENCH_ROOT = Path(__file__).resolve().parent.parent
RUNS_DIR = BENCH_ROOT / "assets" / "runs"

# Buckets in the activity profile drawn on each problem page.
TRAJ_BUCKETS = 60

# Activity categories, in the order the site paints them. They follow the
# loop the solvers actually run: look around, edit Task.lean, compile, and
# submit to check.sh.
CATEGORIES = ["explore", "edit", "compile", "check"]

# Lean LSP tools that run the compiler or report what it said. The remaining
# ones (search, hover, outline) look something up, so they count as exploring.
COMPILE_TOOLS = {
    "lean_build", "lean_run_code", "lean_goal", "lean_term_goal",
    "lean_diagnostic_messages", "lean_multi_attempt", "lean_code_actions",
    "lean_completions", "lean_verify", "lean_minimal_hypotheses",
    "lean_profile_proof",
}

# A shell command counts as a compile when it drives lake/lean, as a check
# when it submits to check.sh, and as an edit when it writes a Lean file.
COMPILE_CMD = re.compile(r'(^|[\s;&|(])(lake|lean)\s', re.M)
CHECK_CMD = re.compile(r'check\.sh')
WRITE_CMD = re.compile(r'>\s*\S*\.lean\b|tee\s+\S*\.lean\b')


def classify(name: str, cmd: str) -> str:
    """Map one tool call to its activity category."""
    if name.startswith("mcp__lean-lsp__"):
        tool = name.rsplit("__", 1)[-1]
        return "compile" if tool in COMPILE_TOOLS else "explore"
    if name in ("Edit", "Write", "MultiEdit", "NotebookEdit"):
        return "edit"
    if name == "Bash":
        if CHECK_CMD.search(cmd):
            return "check"
        if COMPILE_CMD.search(cmd):
            return "compile"
        if WRITE_CMD.search(cmd):
            return "edit"
        return "explore"
    # Read, Grep, Glob, web and planning tools.
    return "explore"


def scan_transcript(path: Path):
    """Aggregate one transcript. Returns None if it cannot be read."""
    if not path.exists():
        return None
    calls = []                  # (ts, category)
    counts = dict.fromkeys(CATEGORIES, 0)
    seen = set()
    result = None
    first_ts = last_ts = None

    with path.open(errors="replace") as f:
        for line in f:
            try:
                evt = json.loads(line)
            except json.JSONDecodeError:
                continue
            ts = evt.get("ts")
            if ts:
                first_ts = ts if first_ts is None else first_ts
                last_ts = ts
            if evt.get("type") == "result":
                result = evt
                continue
            if evt.get("type") != "assistant":
                continue
            msg = evt.get("message") or {}
            for block in msg.get("content") or []:
                # The stream re-emits a message as it grows, so count each
                # tool call once.
                if block.get("type") != "tool_use" or block.get("id") in seen:
                    continue
                seen.add(block.get("id"))
                inp = block.get("input") or {}
                cmd = inp.get("command") or "" if isinstance(inp, dict) else ""
                cat = classify(block.get("name") or "", cmd)
                counts[cat] += 1
                calls.append((ts, cat))

    # Cost, turns and token totals come from the final result record only. A
    # run killed at the wall-clock cap never writes one, and the per-message
    # usage in the stream is a partial snapshot (it reports a few hundred
    # output tokens where the true total is six figures), so those runs
    # report no cost and no token count rather than a wrong one. The tool
    # calls and the activity profile stay exact either way.
    turns = tokens = None
    if result:
        turns = result.get("num_turns")
        usage = result.get("usage") or {}
        tokens = {
            "in": usage.get("input_tokens") or 0,
            "out": usage.get("output_tokens") or 0,
            "cache_read": usage.get("cache_read_input_tokens") or 0,
            "think": (usage.get("output_tokens_details") or {}).get(
                "thinking_tokens") or 0,
        }

    return {
        "cost_usd": (result or {}).get("total_cost_usd"),
        "turns": turns,
        "tools": counts,
        "tool_calls": sum(counts.values()),
        "tokens": tokens,
        "traj": bucketize(calls, first_ts, last_ts),
    }


def bucketize(calls, first_ts, last_ts):
    """Tool calls binned into TRAJ_BUCKETS columns.

    Columns are equal slices of wall clock when the transcript timestamps its
    events, and equal slices of the call sequence when it does not (older
    transcripts carry no ts), which the "by" field records.
    """
    if not calls:
        return None
    timed = first_ts and last_ts and last_ts > first_ts and all(
        ts for ts, _ in calls)
    # Wall clock leaves gaps where the agent was thinking or waiting on the
    # compiler, which is the point; a step profile has no such gaps, so it
    # gets one column per call up to the same budget.
    n = TRAJ_BUCKETS if timed else min(TRAJ_BUCKETS, len(calls))
    prof = {c: [0] * n for c in CATEGORIES}
    span = (last_ts - first_ts) if timed else len(calls)
    for i, (ts, cat) in enumerate(calls):
        pos = (ts - first_ts) / span if timed else i / len(calls)
        prof[cat][min(int(pos * n), n - 1)] += 1
    return {"n": n, "by": "time" if timed else "step",
            "span_s": round(span, 1) if timed else None, **prof}


def task_dirs(run_dir: Path):
    root = run_dir / "tasks" if (run_dir / "tasks").is_dir() else run_dir
    return sorted(d for d in root.iterdir() if d.is_dir())


def excluded(name: str, names) -> bool:
    """--exclude matches a full task name or its unprefixed form
    (TnumStepUp -> eBPF_TnumStepUp), as solved/ does."""
    return any(name == n or name.endswith("_" + n) for n in names)


def collect(run_dir: Path, drop=()):
    """Task records, plus the wall-clock span the run covers."""
    tasks, stamps = {}, []
    for d in task_dirs(run_dir):
        if excluded(d.name, drop):
            print(f"excluding {d.name}")
            continue
        result_file = d / "result.json"
        if not result_file.exists():
            continue            # never ran, or still running
        try:
            res = json.loads(result_file.read_text())
        except (json.JSONDecodeError, OSError):
            continue
        entry = {"status": res.get("status", "UNKNOWN"),
                 "elapsed_s": res.get("elapsed_s")}
        scan = scan_transcript(d / "logs" / "transcript.jsonl")
        if scan:
            entry.update(scan)
        meta_file = d / "logs" / "meta.json"
        if meta_file.exists():
            try:
                meta = json.loads(meta_file.read_text())
            except (json.JSONDecodeError, OSError):
                meta = {}
            stamps += [t for t in (meta.get("start_time"), meta.get("end_time"))
                       if t]
        tasks[d.name] = entry
    return tasks, (min(stamps), max(stamps)) if stamps else (None, None)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("run_dir", help="run output directory, or a directory of tasks")
    ap.add_argument("--id", required=True, help="short id; names runs/<id>.json")
    ap.add_argument("--model", required=True, help="model id, e.g. claude-opus-5")
    ap.add_argument("--label", required=True, help="display name, e.g. Claude Opus 5")
    ap.add_argument("--agent", default="Claude Code", help="solver harness")
    ap.add_argument("--limit-s", type=int, default=7200,
                    help="per-task wall-clock cap of the run (default 7200)")
    ap.add_argument("--date", help="run date (default: from the first meta.json)")
    ap.add_argument("--exclude", nargs="+", default=[], metavar="TASK",
                    help="task names to leave out of the summary, e.g. one "
                         "that was run by mistake")
    ap.add_argument("--out", default=str(RUNS_DIR))
    args = ap.parse_args()

    tasks, (started, ended) = collect(Path(args.run_dir).resolve(), args.exclude)
    if not tasks:
        raise SystemExit(f"no task results under {args.run_dir}")

    def as_date(stamp):
        try:
            return datetime.fromisoformat(stamp).astimezone(
                timezone.utc).date().isoformat()
        except (TypeError, ValueError):
            return None

    # A suite run spans days, sometimes machines; report both ends of it.
    date = args.date or as_date(started)
    date_end = as_date(ended) if not args.date else None

    run = {"id": args.id, "model": args.model, "label": args.label,
           "agent": args.agent, "date": date, "date_end": date_end,
           "limit_s": args.limit_s, "tasks": tasks}
    out_dir = Path(args.out)
    out_dir.mkdir(parents=True, exist_ok=True)
    out = out_dir / f"{args.id}.json"
    out.write_text(json.dumps(run, separators=(",", ":"), sort_keys=False) + "\n")

    passed = sum(1 for t in tasks.values() if t["status"] == "PASS")
    costed = [t["cost_usd"] for t in tasks.values() if t.get("cost_usd")]
    print(f"{out}: {len(tasks)} tasks, {passed} PASS, "
          f"${sum(costed):.2f} recorded over {len(costed)} runs")


if __name__ == "__main__":
    main()
