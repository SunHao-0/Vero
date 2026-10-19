#!/usr/bin/env python3
"""Summarize a benchmark run into the compact JSON the website reads.

A run directory holds one sub-directory per task with result.json and the
solver transcript. Those are large (hundreds of MB) and contain the agent's
tool inputs -- including the Lean code of solutions that are not published
yet. This script keeps only aggregate numbers: outcome, LLM-review verdict,
wall time, cost, turns, token totals, per-category tool-call counts, and a
bucketed activity profile. No command, file path, prompt, review text, or
session id is ever written out, so the result is safe to commit next to the
public site.

Both harnesses the runner ships are understood: Claude Code's stream-json
transcript (claude_code.sh) and Codex CLI's `exec --json` event stream
(codex_cli.sh). Every tool call of either goes through the same classifier,
so the activity numbers of different agents are comparable.

Usage:
    python3 scripts/collect_runs.py <run-dir> --id opus5 \
        --model claude-opus-5 --label "Claude Opus 5"

<run-dir> is either an output directory produced by run_bench.py (tasks live
in <run-dir>/tasks/) or a directory of task directories such as solved/.
"""
import argparse
import json
import os
import re
import shlex
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

# A shell command counts as a check when it submits to check.sh, as a
# compile when it drives lake/lean, and as an edit when it writes a Lean
# file; one command that does several counts once, in that order. Asking
# the toolchain where it lives (`lean --print-prefix`, `which lean`) is not
# a compile.
CHECK_CMD = re.compile(r'check\.sh')
COMPILE_CMD = re.compile(r'(^|[\s;&|(])(lake|lean)\s', re.M)
TOOLCHAIN_QUERY = re.compile(
    r'\b(lean|lake)\s+(--print-prefix|--version|-v|--help)\b'
    r'|\bwhich\s+(lean|lake)\b')
# Writes into a .lean file: a shell redirect or tee, an in-place sed/perl,
# or a Python script (Codex edits mostly through `python3 - <<'PY' ... PY`).
WRITE_CMD = re.compile(r'>\s*\S*\.lean\b|tee\s+\S*\.lean\b')
INPLACE_CMD = re.compile(r'\b(sed|perl)\s+(-\S+\s+)*-[A-Za-z0-9]*i\b[^\n;&|]*\.lean\b')
PYTHON = re.compile(r'\bpython3?\b')
PY_WRITE = re.compile(r'\.write(_text)?\(|open\([^)]*[\'"][wa]\+?[\'"]')
# A heredoc body is data (Lean code, a note, a script), not shell: it is cut
# out before matching, and only read when the shell hands it to Python.
HEREDOC = re.compile(r"<<-?[ \t]*(['\"]?)([A-Za-z_]\w*)\1(?P<rest>[^\n]*)\n"
                     r"(?P<body>.*?)^[ \t]*\2[ \t]*$", re.S | re.M)

# Codex runs every shell command as `/bin/bash -lc '<script>'`.
SHELLS = {"bash", "sh", "zsh"}

WEB_TOOLS = {"WebSearch", "WebFetch"}


def unwrap_shell(cmd: str) -> str:
    """The script inside a `bash -lc '...'` wrapper, or cmd unchanged."""
    try:
        argv = shlex.split(cmd)
    except ValueError:
        return cmd
    if (len(argv) == 3 and os.path.basename(argv[0]) in SHELLS
            and argv[1] in ("-c", "-lc")):
        return argv[2]
    return cmd


def split_heredocs(cmd: str):
    """The command with heredoc bodies cut out, and [(command line, body)]."""
    bodies = []

    def cut(m):
        line = cmd[cmd.rfind("\n", 0, m.start()) + 1:m.start()]
        bodies.append((line, m.group("body")))
        return f"<<{m.group(2)}{m.group('rest')}\n"
    return HEREDOC.sub(cut, cmd), bodies


def writes_lean(shell: str, bodies) -> bool:
    if WRITE_CMD.search(shell) or INPLACE_CMD.search(shell):
        return True
    if PYTHON.search(shell) and ".lean" in shell and PY_WRITE.search(shell):
        return True             # python3 -c "..."
    return any(PYTHON.search(line) and ".lean" in body and PY_WRITE.search(body)
               for line, body in bodies)


def classify(name: str, cmd: str) -> str:
    """Map one tool call to its activity category."""
    if name.startswith("mcp__lean-lsp__"):
        tool = name.rsplit("__", 1)[-1]
        return "compile" if tool in COMPILE_TOOLS else "explore"
    if name in ("Edit", "Write", "MultiEdit", "NotebookEdit"):
        return "edit"
    if name == "Bash":
        shell, bodies = split_heredocs(unwrap_shell(cmd))
        if CHECK_CMD.search(shell):
            return "check"
        if COMPILE_CMD.search(TOOLCHAIN_QUERY.sub(" ", shell)):
            return "compile"
        if writes_lean(shell, bodies):
            return "edit"
        return "explore"
    # Read, Grep, Glob, web and planning tools.
    return "explore"


def read_events(path: Path):
    events = []
    with path.open(errors="replace") as f:
        for line in f:
            try:
                evt = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(evt, dict):
                events.append(evt)
    return events


def scan_claude(events):
    """Tool calls, final record and agent version of a Claude Code run."""
    calls = []                  # (ts, tool name, shell command)
    seen = set()
    result = version = None
    for evt in events:
        if evt.get("type") == "system" and evt.get("subtype") == "init":
            version = version or evt.get("claude_code_version")
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
            calls.append((evt.get("ts"), block.get("name") or "", cmd))

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
        think = (usage.get("output_tokens_details") or {}).get(
            "thinking_tokens") or 0
        # modelUsage is the per-model total the cost is computed from; it
        # also counts calls to a second model (e.g. a Haiku helper), which
        # `usage` leaves out.
        per_model = (result.get("modelUsage") or {}).values()
        if per_model:
            tokens = {
                "in": sum((m.get("inputTokens") or 0)
                          + (m.get("cacheCreationInputTokens") or 0)
                          for m in per_model),
                "out": sum(m.get("outputTokens") or 0 for m in per_model),
                "cache_read": sum(m.get("cacheReadInputTokens") or 0
                                  for m in per_model),
                "think": think,
            }
        else:
            tokens = {
                "in": (usage.get("input_tokens") or 0)
                      + (usage.get("cache_creation_input_tokens") or 0),
                "out": usage.get("output_tokens") or 0,
                "cache_read": usage.get("cache_read_input_tokens") or 0,
                "think": think,
            }
    agent = f"Claude Code {version}" if version else "Claude Code"
    return calls, (result or {}).get("total_cost_usd"), turns, tokens, agent


# Codex items that are tool calls, by the Claude Code tool they correspond
# to; agent messages and reasoning are not calls.
CODEX_TOOLS = {"command_execution": "Bash", "file_change": "Edit",
               "web_search": "WebSearch", "todo_list": "TodoWrite"}


def scan_codex(events):
    """Tool calls and token totals of a Codex CLI run.

    Codex reports no cost and no per-request turn count (its one "turn" is
    the whole task), so both stay None. Its `turn.completed` record carries
    the token totals of the session; a run killed at the cap never writes
    it, and its tokens are unknown, as for Claude Code.
    """
    calls = []
    seen = set()
    completed = []
    for evt in events:
        typ = evt.get("type")
        if typ == "turn.completed":
            completed.append(evt.get("usage") or {})
            continue
        if typ not in ("item.started", "item.completed"):
            continue
        item = evt.get("item") or {}
        kind = item.get("type")
        if item.get("id") in seen:
            continue
        if kind == "mcp_tool_call":
            name = f"mcp__{item.get('server')}__{item.get('tool')}"
        elif kind in CODEX_TOOLS:
            name = CODEX_TOOLS[kind]
        else:
            continue
        seen.add(item.get("id"))
        calls.append((evt.get("ts"), name, item.get("command") or ""))

    tokens = None
    # One exec is one turn; more than one would make the totals ambiguous.
    if len(completed) == 1:
        u = completed[0]
        cached = u.get("cached_input_tokens") or 0
        tokens = {
            # input_tokens includes the cached part; output_tokens
            # includes reasoning, as Claude's output includes thinking.
            "in": (u.get("input_tokens") or 0) - cached,
            "out": u.get("output_tokens") or 0,
            "cache_read": cached,
            "think": u.get("reasoning_output_tokens") or 0,
        }
    return calls, None, None, tokens, None


def scan_transcript(path: Path, meta: dict):
    """Aggregate one transcript. Returns None if it cannot be read."""
    if not path.exists():
        return None
    events = read_events(path)
    if any(e.get("type") == "thread.started" for e in events[:5]):
        calls, cost, turns, tokens, agent = scan_codex(events)
        version = (meta.get("cli_version") or "").replace("codex-cli", "").strip()
        agent = f"Codex CLI {version}" if version else "Codex CLI"
    else:
        calls, cost, turns, tokens, agent = scan_claude(events)

    counts = dict.fromkeys(CATEGORIES, 0)
    binned = []
    for ts, name, cmd in calls:
        cat = classify(name, cmd)
        counts[cat] += 1
        binned.append((ts, cat))
    stamps = [e["ts"] for e in events if e.get("ts")]
    first_ts, last_ts = (stamps[0], stamps[-1]) if stamps else (None, None)

    scan = {
        "cost_usd": cost,
        "turns": turns,
        "tools": counts,
        "tool_calls": sum(counts.values()),
        "tokens": tokens,
        "traj": bucketize(binned, first_ts, last_ts),
    }
    # Web lookups are recorded even in a run that disabled the web, so the
    # site can say when an agent reached it anyway.
    web = sum(1 for _, name, _ in calls if name in WEB_TOOLS)
    if web:
        scan["web_calls"] = web
    return scan, agent


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


def read_review(task_dir: Path):
    """The LLM review verdict (scripts/llm_check.py) of a submission, and
    which of its two judgments failed. The review text is left behind: it
    describes the solution, which is not published yet."""
    try:
        review = json.loads((task_dir / "llm_review.json").read_text())
    except (OSError, json.JSONDecodeError):
        return None
    if not review.get("verdict"):
        return None
    flags = [k for k, key in (("faithful", "faithful"),
                              ("complexity", "complexity_ok"))
             if review.get(key) is False]
    return {"verdict": review["verdict"], "flags": flags,
            "judge": review.get("model")}


def task_dirs(run_dir: Path):
    root = run_dir / "tasks" if (run_dir / "tasks").is_dir() else run_dir
    return sorted(d for d in root.iterdir() if d.is_dir())


def excluded(name: str, names) -> bool:
    """--exclude matches a full task name or its unprefixed form
    (TnumStepUp -> eBPF_TnumStepUp), as solved/ does."""
    return any(name == n or name.endswith("_" + n) for n in names)


def web_access(meta: dict):
    """Whether the agent could reach the web. Older metas only list the
    allowed tools."""
    if "web_access" in meta:
        return bool(meta["web_access"])
    tools = meta.get("allowed_tools")
    return None if tools is None else "WebFetch" in tools


def collect(run_dir: Path, drop=()):
    """Task records, plus what the run as a whole reports: its wall-clock
    span, the agents and judges seen, and whether the web was reachable."""
    tasks, stamps = {}, []
    agents, judges, web = set(), set(), set()
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
        meta = {}
        meta_file = d / "logs" / "meta.json"
        if meta_file.exists():
            try:
                meta = json.loads(meta_file.read_text())
            except (json.JSONDecodeError, OSError):
                meta = {}
            stamps += [t for t in (meta.get("start_time"), meta.get("end_time"))
                       if t]
            web.add(web_access(meta))
        entry = {"status": res.get("status", "UNKNOWN"),
                 "elapsed_s": res.get("elapsed_s")}
        # Only a submission that passed check.sh is reviewed.
        review = read_review(d) if entry["status"] == "PASS" else None
        if review:
            entry["review"] = review["verdict"]
            if review["flags"]:
                entry["review_flags"] = review["flags"]
            judges.add(review["judge"])
        scanned = scan_transcript(d / "logs" / "transcript.jsonl", meta)
        if scanned:
            scan, agent = scanned
            entry.update(scan)
            if agent:
                agents.add(agent)
        tasks[d.name] = entry

    def as_date(stamp):
        try:
            return datetime.fromisoformat(stamp).astimezone(timezone.utc)
        except (TypeError, ValueError):
            return None

    times = sorted(t for t in map(as_date, stamps) if t)
    web.discard(None)
    return tasks, {
        "span": (times[0], times[-1]) if times else (None, None),
        "agents": sorted(agents),
        "judges": sorted(j for j in judges if j),
        "web": web.pop() if len(web) == 1 else ("mixed" if web else None),
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("run_dir", help="run output directory, or a directory of tasks")
    ap.add_argument("--id", required=True, help="short id; names runs/<id>.json")
    ap.add_argument("--model", required=True, help="model id, e.g. claude-opus-5")
    ap.add_argument("--label", required=True, help="display name, e.g. Claude Opus 5")
    ap.add_argument("--agent", help="solver harness (default: detected from "
                                    "the transcripts, with its version)")
    ap.add_argument("--limit-s", type=int, default=7200,
                    help="per-task wall-clock cap of the run (default 7200)")
    ap.add_argument("--parallel", type=int,
                    help="tasks the run executed at once (run_bench.py "
                         "--parallel); wall-clock times depend on it")
    ap.add_argument("--date", help="run date (default: from the first meta.json)")
    ap.add_argument("--exclude", nargs="+", default=[], metavar="TASK",
                    help="task names to leave out of the summary, e.g. one "
                         "that was run by mistake")
    ap.add_argument("--out", default=str(RUNS_DIR))
    args = ap.parse_args()

    tasks, info = collect(Path(args.run_dir).resolve(), args.exclude)
    if not tasks:
        raise SystemExit(f"no task results under {args.run_dir}")

    # A suite run spans days, sometimes machines; report both ends of it.
    started, ended = info["span"]
    date = args.date or (started.date().isoformat() if started else None)
    date_end = ended.date().isoformat() if ended and not args.date else None

    reviewed = [t for t in tasks.values() if t.get("review")]
    passed = [t for t in tasks.values() if t["status"] == "PASS"]
    if reviewed and len(reviewed) != len(passed):
        print(f"WARNING: {len(passed) - len(reviewed)} PASS tasks have no "
              f"LLM review; run scripts/llm_check.py on {args.run_dir}")

    run = {"id": args.id, "model": args.model, "label": args.label,
           "agent": args.agent or ", ".join(info["agents"]) or None,
           "date": date, "date_end": date_end,
           "limit_s": args.limit_s, "web_access": info["web"]}
    if args.parallel:
        run["parallel"] = args.parallel
    if reviewed:
        run["review"] = {"judge": ", ".join(info["judges"]) or None,
                         "reviewed": len(reviewed)}
    run["tasks"] = tasks
    out_dir = Path(args.out)
    out_dir.mkdir(parents=True, exist_ok=True)
    out = out_dir / f"{args.id}.json"
    out.write_text(json.dumps(run, separators=(",", ":"), sort_keys=False) + "\n")

    rejected = sum(1 for t in reviewed if t["review"] == "REJECT")
    costed = [t["cost_usd"] for t in tasks.values() if t.get("cost_usd")]
    statuses = {}
    for t in tasks.values():
        statuses[t["status"]] = statuses.get(t["status"], 0) + 1
    print(f"{out}: {len(tasks)} tasks, "
          + ", ".join(f"{n} {s}" for s, n in sorted(statuses.items()))
          + f"; {len(reviewed)} reviewed, {rejected} REJECT; "
          f"${sum(costed):.2f} recorded over {len(costed)} runs; "
          f"agent {run['agent']}, web access {run['web_access']}")


if __name__ == "__main__":
    main()
