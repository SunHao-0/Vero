#!/usr/bin/env python3
"""Live monitor for Vero solver transcripts (Claude Code and GitHub Copilot).

Usage:
    # Watch a running solver (follows the file like tail -f):
    ./scripts/monitor.py <task_dir>/logs/transcript.jsonl

    # Analyze a completed transcript (prints summary and exits):
    ./scripts/monitor.py --summary <task_dir>/logs/transcript.jsonl

    # Watch all running tasks under an output directory:
    ./scripts/monitor.py --watch-dir <output_dir>

The transcript format is auto-detected per file:

  * Claude Code (scripts/claude_code.sh) — stream-json events typed
    ``system`` / ``assistant`` / ``user`` / ``result``, each carrying a ``ts``
    float injected by the wrapper.
  * GitHub Copilot (scripts/copilot.sh) — ``--output-format json`` events with
    dotted types (``session.*`` / ``assistant.*`` / ``tool.*`` / ``result``) and
    ISO-8601 ``timestamp`` fields.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path
from typing import Optional

DIM = "\033[2m"
BOLD = "\033[1m"
RED = "\033[0;31m"
GREEN = "\033[0;32m"
YELLOW = "\033[0;33m"
CYAN = "\033[0;36m"
NC = "\033[0m"


def fmt_duration(seconds: float) -> str:
    if seconds < 1:
        return f"{seconds * 1000:.0f}ms"
    if seconds < 60:
        return f"{seconds:.1f}s"
    m, s = divmod(int(seconds), 60)
    return f"{m}m{s:02d}s"


def _line_tag(m) -> str:
    """Dim ``[elapsed]`` prefix for a live line, or ``[name elapsed]`` when the
    monitor carries a task name (watch-dir mode multiplexes many tasks)."""
    el = m._elapsed_str()
    inner = f"{m.name} {el}" if m.name else el
    return f"{DIM}[{inner}]{NC}"


def _iso_to_epoch(s: Optional[str]) -> Optional[float]:
    """Parse a Copilot ISO-8601 timestamp (e.g. ``2026-07-05T19:42:45.308Z``)
    into a Unix epoch float. Returns None if absent or unparseable."""
    if not s:
        return None
    try:
        return datetime.fromisoformat(s.replace("Z", "+00:00")).timestamp()
    except (ValueError, TypeError):
        return None


def short_cmd(cmd: str, max_len: int = 80) -> str:
    """Strip a common bash wrapper and truncate for display."""
    for prefix in ("/bin/bash -lc ", "/usr/bin/bash -lc "):
        if cmd.startswith(prefix):
            cmd = cmd[len(prefix):]
            break
    cmd = cmd.strip("'\"")
    if len(cmd) > max_len:
        cmd = cmd[: max_len - 3] + "..."
    return cmd


class SolverMonitor:
    """Track running totals across a Claude Code transcript.

    Time accounting: tool_use events carry an ``id`` that is echoed back
    as ``tool_use_id`` in the subsequent user tool_result. The gap between
    the two timestamps is the tool's execution time.
    """

    def __init__(self) -> None:
        self.start_ts: Optional[float] = None
        self.last_ts: Optional[float] = None
        self.name = ""  # task label, set when multiplexing (watch-dir mode)
        self.turn_count = 0
        self.cmd_count = 0
        self.agent_message_count = 0
        self.check_sh_count = 0
        self.lake_build_count = 0
        self.total_input_tokens = 0
        self.total_output_tokens = 0
        self.total_cached_tokens = 0
        # tool_use_id -> ts for pairing with tool_result.
        self._pending_tools: dict[str, float] = {}
        # 10 slowest (duration, command) pairs, newest ties last.
        self.slowest: list[tuple[float, str]] = []
        self.total_tool_time = 0.0

    def _update_start(self, ts: float) -> None:
        if self.start_ts is None:
            self.start_ts = ts
        self.last_ts = ts

    def _elapsed_str(self) -> str:
        if self.start_ts is None or self.last_ts is None:
            return "0s"
        return fmt_duration(self.last_ts - self.start_ts)

    def _track_command(self, cmd: str) -> None:
        if "check.sh" in cmd:
            self.check_sh_count += 1
        if "lake lean" in cmd or "lake build" in cmd:
            self.lake_build_count += 1

    def _record_tool_duration(self, dur: float, label: str) -> None:
        self.total_tool_time += dur
        self.slowest.append((dur, label))
        self.slowest.sort(key=lambda x: x[0], reverse=True)
        del self.slowest[10:]

    # -- event dispatch -------------------------------------------------

    def process_event(self, ev: dict, *, live: bool = True) -> None:
        ts = ev.get("ts")
        if ts:
            self._update_start(ts)

        handler = _HANDLERS.get(ev.get("type", ""))
        if handler is not None:
            handler(self, ev, live)

    def _on_assistant(self, ev: dict, live: bool) -> None:
        msg = ev.get("message", {})
        usage = msg.get("usage") or {}
        self.total_input_tokens += usage.get("input_tokens", 0)
        self.total_cached_tokens += usage.get("cache_read_input_tokens", 0)
        self.total_output_tokens += usage.get("output_tokens", 0)

        ts = ev.get("ts")
        for item in msg.get("content", []):
            itype = item.get("type", "")
            if itype == "tool_use":
                self._on_tool_use(item, ts, live)
            elif itype == "text":
                self._on_text(item, live)

    def _on_tool_use(self, item: dict, ts: Optional[float], live: bool) -> None:
        name = item.get("name", "")
        inp = item.get("input", {})
        self.cmd_count += 1
        tool_id = item.get("id")
        if tool_id and ts:
            self._pending_tools[tool_id] = ts

        detail = ""
        if name == "Bash":
            cmd = inp.get("command", "")
            detail = short_cmd(cmd)
            self._track_command(cmd)
        elif name in ("Read", "Edit", "Write"):
            detail = inp.get("file_path", "")
        elif name.startswith("mcp__lean-lsp__"):
            detail = name.removeprefix("mcp__lean-lsp__")

        if live:
            suffix = f" {detail}" if detail else ""
            print(f"  {_line_tag(self)} "
                  f"{CYAN}{name}{NC}{suffix}", flush=True)

    def _on_text(self, item: dict, live: bool) -> None:
        self.agent_message_count += 1
        if not live:
            return
        text = item.get("text", "")
        if len(text) > 256:
            text = text[:253] + "..."
        print(f"  {_line_tag(self)} "
              f"{BOLD}agent:{NC} {text}", flush=True)

    def _on_user(self, ev: dict, live: bool) -> None:
        ts = ev.get("ts")
        if not ts:
            return
        msg = ev.get("message", {})
        for item in msg.get("content", []) or []:
            if item.get("type") != "tool_result":
                continue
            start = self._pending_tools.pop(item.get("tool_use_id", ""), None)
            if start is not None:
                self._record_tool_duration(ts - start, _describe_tool_result(item))

    def _on_result(self, ev: dict, live: bool) -> None:
        self.turn_count = ev.get("num_turns", self.turn_count)
        cost = ev.get("total_cost_usd")
        if live and cost is not None:
            print(f"\n  {GREEN}Result:{NC} cost=${cost:.2f}, "
                  f"turns={self.turn_count}", flush=True)

    # -- summary --------------------------------------------------------

    def print_summary(self) -> None:
        wall = (self.last_ts - self.start_ts
                if self.start_ts and self.last_ts else 0)
        print(f"\n{'=' * 60}")
        label = f"Claude Code ({self.name})" if self.name else "Claude Code"
        print(f"  {BOLD}{label}{NC}    {BOLD}Wall time:{NC} {fmt_duration(wall)}")
        print(f"{'=' * 60}")

        print(f"\n  {BOLD}Stats:{NC}")
        print(f"    Steps (msg/cmd):     "
              f"{self.agent_message_count} / {self.cmd_count}")
        print(f"    check.sh runs:       {self.check_sh_count}")
        print(f"    lake build/lean:     {self.lake_build_count}")
        if self.turn_count:
            print(f"    Turns:               {self.turn_count}")
        print(f"    Tokens (in/cache/out): "
              f"{self.total_input_tokens:,} / "
              f"{self.total_cached_tokens:,} / "
              f"{self.total_output_tokens:,}")

        if wall > 0 and self.total_tool_time > 0:
            tool_pct = self.total_tool_time / wall * 100
            model_pct = max(0.0, 100 - tool_pct)
            print(f"\n  {BOLD}Time breakdown:{NC}")
            print(f"    Tools:  {fmt_duration(self.total_tool_time):>8s}  "
                  f"{CYAN}{'#' * int(tool_pct / 2)}{NC} {tool_pct:.0f}%")
            print(f"    Model:  {fmt_duration(wall - self.total_tool_time):>8s}  "
                  f"{YELLOW}{'#' * int(model_pct / 2)}{NC} {model_pct:.0f}%")

        if self.slowest:
            print(f"\n  {BOLD}Slowest tool calls:{NC}")
            for dur, label in self.slowest:
                if dur < 0.1:
                    continue
                print(f"    {YELLOW}{fmt_duration(dur):>8s}{NC}  {label}")
        print()


def _describe_tool_result(item: dict) -> str:
    """Short label for a tool_result event (falls back to the tool_use_id)."""
    tid = item.get("tool_use_id", "?")
    content = item.get("content")
    if isinstance(content, list) and content:
        first = content[0]
        if isinstance(first, dict):
            snippet = first.get("text", "")[:60].replace("\n", " ")
            if snippet:
                return f"{tid}: {snippet}"
    return tid


_HANDLERS = {
    "system":    lambda m, ev, live: None,  # session metadata; nothing to track
    "assistant": SolverMonitor._on_assistant,
    "user":      SolverMonitor._on_user,
    "result":    SolverMonitor._on_result,
}


class CopilotMonitor:
    """Track running totals across a GitHub Copilot ``--output-format json``
    transcript (scripts/copilot.sh).

    Copilot streams dotted-type events with ISO-8601 timestamps. Tool timing
    pairs ``tool.execution_start`` with ``tool.execution_complete`` by
    ``toolCallId``. Per-message output tokens come from ``assistant.message``;
    aggregate usage (premium requests, API/session duration, code changes) and
    the exit code arrive in the final ``result`` event.
    """

    def __init__(self) -> None:
        self.start_ts: Optional[float] = None
        self.last_ts: Optional[float] = None
        self.name = ""  # task label, set when multiplexing (watch-dir mode)
        self.turn_count = 0
        self.cmd_count = 0
        self.agent_message_count = 0
        self.check_sh_count = 0
        self.lake_build_count = 0
        self.total_output_tokens = 0
        # Aggregate usage from the terminal result event.
        self.premium_requests: Optional[int] = None
        self.api_duration_ms: Optional[float] = None
        self.session_duration_ms: Optional[float] = None
        self.exit_code: Optional[int] = None
        self.lines_added = 0
        self.lines_removed = 0
        self.files_modified = 0
        # toolCallId -> start ts, for pairing with tool.execution_complete.
        self._pending_tools: dict[str, float] = {}
        self.slowest: list[tuple[float, str]] = []
        self.total_tool_time = 0.0

    # -- shared timing helpers (mirrors SolverMonitor) ------------------

    def _update_start(self, ts: float) -> None:
        if self.start_ts is None:
            self.start_ts = ts
        self.last_ts = ts

    def _elapsed_str(self) -> str:
        if self.start_ts is None or self.last_ts is None:
            return "0s"
        return fmt_duration(self.last_ts - self.start_ts)

    def _track_command(self, cmd: str) -> None:
        if "check.sh" in cmd:
            self.check_sh_count += 1
        if "lake lean" in cmd or "lake build" in cmd:
            self.lake_build_count += 1

    def _record_tool_duration(self, dur: float, label: str) -> None:
        self.total_tool_time += dur
        self.slowest.append((dur, label))
        self.slowest.sort(key=lambda x: x[0], reverse=True)
        del self.slowest[10:]

    # -- event dispatch -------------------------------------------------

    def process_event(self, ev: dict, *, live: bool = True) -> None:
        ts = _iso_to_epoch(ev.get("timestamp"))
        if ts is not None:
            self._update_start(ts)

        etype = ev.get("type", "")
        data = ev.get("data") or {}
        if etype == "assistant.turn_start":
            self.turn_count += 1
        elif etype == "assistant.message":
            self._on_message(data, live)
        elif etype == "tool.execution_start":
            self._on_tool_start(data, ts, live)
        elif etype == "tool.execution_complete":
            self._on_tool_complete(data, ts)
        elif etype == "result":
            self._on_result(ev, live)

    def _on_message(self, data: dict, live: bool) -> None:
        self.total_output_tokens += data.get("outputTokens", 0) or 0
        text = (data.get("content") or "").strip()
        if not text:
            return
        self.agent_message_count += 1
        if live:
            disp = text if len(text) <= 256 else text[:253] + "..."
            print(f"  {_line_tag(self)} "
                  f"{BOLD}agent:{NC} {disp}", flush=True)

    def _on_tool_start(self, data: dict, ts: Optional[float], live: bool) -> None:
        self.cmd_count += 1
        cid = data.get("toolCallId")
        if cid and ts is not None:
            self._pending_tools[cid] = ts
        name = data.get("toolName", "")
        args = data.get("arguments") or {}
        if name == "bash":
            self._track_command(args.get("command", ""))
        if live:
            detail = _copilot_tool_detail(name, args)
            suffix = f" {detail}" if detail else ""
            print(f"  {_line_tag(self)} "
                  f"{CYAN}{name}{NC}{suffix}", flush=True)

    def _on_tool_complete(self, data: dict, ts: Optional[float]) -> None:
        start = self._pending_tools.pop(data.get("toolCallId", ""), None)
        if start is not None and ts is not None:
            self._record_tool_duration(ts - start, _copilot_result_label(data))

    def _on_result(self, ev: dict, live: bool) -> None:
        usage = ev.get("usage") or {}
        self.premium_requests = usage.get("premiumRequests")
        self.api_duration_ms = usage.get("totalApiDurationMs")
        self.session_duration_ms = usage.get("sessionDurationMs")
        self.exit_code = ev.get("exitCode")
        changes = usage.get("codeChanges") or {}
        self.lines_added = changes.get("linesAdded", 0) or 0
        self.lines_removed = changes.get("linesRemoved", 0) or 0
        modified = changes.get("filesModified") or []
        self.files_modified = len(modified) if isinstance(modified, list) else 0
        if live:
            bits = []
            if self.exit_code is not None:
                bits.append(f"exit={self.exit_code}")
            if self.premium_requests is not None:
                bits.append(f"premium_requests={self.premium_requests}")
            if self.api_duration_ms:
                bits.append(f"api={fmt_duration(self.api_duration_ms / 1000)}")
            if bits:
                print(f"\n  {GREEN}Result:{NC} {', '.join(bits)}", flush=True)

    # -- summary --------------------------------------------------------

    def print_summary(self) -> None:
        wall = (self.last_ts - self.start_ts
                if self.start_ts and self.last_ts else 0)
        print(f"\n{'=' * 60}")
        label = f"GitHub Copilot ({self.name})" if self.name else "GitHub Copilot"
        print(f"  {BOLD}{label}{NC}    {BOLD}Wall time:{NC} {fmt_duration(wall)}")
        print(f"{'=' * 60}")

        print(f"\n  {BOLD}Stats:{NC}")
        print(f"    Steps (msg/cmd):     "
              f"{self.agent_message_count} / {self.cmd_count}")
        print(f"    check.sh runs:       {self.check_sh_count}")
        print(f"    lake build/lean:     {self.lake_build_count}")
        if self.turn_count:
            print(f"    Turns:               {self.turn_count}")
        print(f"    Output tokens:       {self.total_output_tokens:,}")

        usage_bits = []
        if self.premium_requests is not None:
            usage_bits.append(f"premium_requests={self.premium_requests}")
        if self.api_duration_ms:
            usage_bits.append(f"api={fmt_duration(self.api_duration_ms / 1000)}")
        if self.session_duration_ms:
            usage_bits.append(f"session={fmt_duration(self.session_duration_ms / 1000)}")
        if usage_bits:
            print(f"    Usage:               {', '.join(usage_bits)}")
        if self.files_modified or self.lines_added or self.lines_removed:
            print(f"    Code changes:        "
                  f"+{self.lines_added}/-{self.lines_removed} "
                  f"in {self.files_modified} file(s)")
        if self.exit_code is not None:
            print(f"    Exit code:           {self.exit_code}")

        if wall > 0 and self.total_tool_time > 0:
            tool_pct = self.total_tool_time / wall * 100
            model_pct = max(0.0, 100 - tool_pct)
            print(f"\n  {BOLD}Time breakdown:{NC}")
            print(f"    Tools:  {fmt_duration(self.total_tool_time):>8s}  "
                  f"{CYAN}{'#' * int(tool_pct / 2)}{NC} {tool_pct:.0f}%")
            print(f"    Model:  {fmt_duration(wall - self.total_tool_time):>8s}  "
                  f"{YELLOW}{'#' * int(model_pct / 2)}{NC} {model_pct:.0f}%")

        if self.slowest:
            print(f"\n  {BOLD}Slowest tool calls:{NC}")
            for dur, label in self.slowest:
                if dur < 0.1:
                    continue
                print(f"    {YELLOW}{fmt_duration(dur):>8s}{NC}  {label}")
        print()


def _copilot_tool_detail(name: str, args: dict) -> str:
    """Short display detail for a Copilot tool.execution_start event."""
    if name == "bash":
        return short_cmd(args.get("command", ""))
    for key in ("path", "file_path", "filePath", "filename", "pattern", "query"):
        val = args.get(key)
        if val:
            return str(val)
    for key, val in args.items():
        if isinstance(val, (str, int, float)) and str(val):
            return f"{key}={str(val)[:60]}"
    return ""


def _copilot_result_label(data: dict) -> str:
    """Short label for a tool.execution_complete event (for the slowest list)."""
    cid = (data.get("toolCallId") or "?")[:12]
    result = data.get("result")
    content = result.get("content") if isinstance(result, dict) else None
    if isinstance(content, str) and content.strip():
        snippet = content[:60].replace("\n", " ")
        return f"{cid}: {snippet}"
    return f"{cid} ({'ok' if data.get('success') else 'fail'})"


# ---------------------------------------------------------------------------
# Format detection
# ---------------------------------------------------------------------------

def _detect_format(path: Path) -> str:
    """Return 'copilot' or 'claude' by peeking at the transcript's event types.

    Copilot events use dotted types (session.*, assistant.*, tool.*); Claude
    stream-json uses flat types (system/assistant/user/result). Defaults to
    'claude' when the file is empty or ambiguous.
    """
    try:
        with open(path) as f:
            for _ in range(50):
                line = f.readline()
                if not line:
                    break
                line = line.strip()
                if not line:
                    continue
                try:
                    ev = json.loads(line)
                except json.JSONDecodeError:
                    continue
                etype = ev.get("type", "")
                if "." in etype:
                    return "copilot"
                if etype in ("system", "assistant", "user", "rate_limit_event"):
                    return "claude"
                if etype == "result":
                    return "copilot" if "sessionId" in ev else "claude"
    except OSError:
        pass
    return "claude"


def make_monitor(fmt: str):
    """Instantiate the monitor matching a detected transcript format."""
    return CopilotMonitor() if fmt == "copilot" else SolverMonitor()


# ---------------------------------------------------------------------------
# File drivers
# ---------------------------------------------------------------------------

def _iter_events(lines) -> "iter":
    for line in lines:
        line = line.strip()
        if not line:
            continue
        try:
            yield json.loads(line)
        except json.JSONDecodeError:
            continue


def _task_name(path: Path) -> str:
    """Task dir name from a .../<task>/logs/transcript.jsonl path."""
    return path.parent.parent.name


def follow_file(path: Path, monitor) -> None:
    """Tail -f style: follow the transcript until the user interrupts."""
    print(f"{BOLD}[monitor]{NC} watching {CYAN}{_task_name(path)}{NC} ({path})\n",
          flush=True)
    with open(path) as f:
        while True:
            line = f.readline()
            if not line:
                time.sleep(0.1)
                continue
            for ev in _iter_events([line]):
                monitor.process_event(ev, live=True)


def analyze_file(path: Path):
    """Parse a completed transcript and return the populated monitor."""
    monitor = make_monitor(_detect_format(path))
    with open(path) as f:
        for ev in _iter_events(f):
            monitor.process_event(ev, live=False)
    return monitor


def watch_dir(output_dir: Path) -> None:
    """Follow every transcript.jsonl under output_dir, one monitor per task.

    tail(1) prints a ``==> path <==`` banner whenever the file producing output
    changes; we track the active file from those banners and route each line to
    that task's own monitor. The elapsed clock is therefore per task, not
    run-wide (a single shared monitor would count from the first task's first
    event across the whole run). ``-q`` is deliberately omitted so the banners
    are emitted; a lone transcript gets no banner, hence the fallback below.
    """
    transcripts = sorted(output_dir.rglob("logs/transcript.jsonl"))
    if not transcripts:
        print(f"{RED}No transcript.jsonl files found under {output_dir}{NC}")
        sys.exit(1)

    # A run uses one solver, so all transcripts share a format; pick the first
    # that resolves to Copilot, else default to Claude.
    fmt = "claude"
    for t in transcripts:
        if _detect_format(t) == "copilot":
            fmt = "copilot"
            break

    print(f"{BOLD}[monitor]{NC} watching {len(transcripts)} tasks "
          f"under {output_dir} ({fmt})\n")

    cmd = ["tail", "-n", "+1", "-f", "--", *map(str, transcripts)]
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, text=True)

    monitors: dict = {}
    current = str(transcripts[0])  # fallback when tail emits no banner

    def monitor_for(key: str):
        m = monitors.get(key)
        if m is None:
            m = make_monitor(fmt)
            m.name = _task_name(Path(key))
            monitors[key] = m
        return m

    try:
        assert proc.stdout is not None
        for raw in proc.stdout:
            line = raw.strip()
            if not line:
                continue
            if line.startswith("==> ") and line.endswith(" <=="):
                current = line[4:-4]
                continue
            try:
                ev = json.loads(line)
            except json.JSONDecodeError:
                continue
            monitor_for(current).process_event(ev, live=True)
    except KeyboardInterrupt:
        proc.terminate()
        print()
        for m in monitors.values():
            m.print_summary()


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _resolve_transcript(path: Path) -> Path:
    """Let the user pass a task dir instead of the .jsonl file directly."""
    if path.is_file():
        return path
    if path.is_dir():
        direct = path / "logs" / "transcript.jsonl"
        if direct.exists():
            return direct
        candidates = list(path.rglob("logs/transcript.jsonl"))
        if len(candidates) == 1:
            return candidates[0]
        if len(candidates) > 1:
            print("Multiple transcripts found. Use --watch-dir to monitor all.")
            sys.exit(1)
    print(f"{RED}No transcript.jsonl found under {path}{NC}")
    sys.exit(1)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Live monitor for Vero solver transcripts "
                    "(Claude Code and GitHub Copilot; format auto-detected)")
    parser.add_argument("path", type=Path,
                        help="Path to transcript.jsonl file or task directory")
    parser.add_argument("--summary", action="store_true",
                        help="Print summary of completed transcript and exit")
    parser.add_argument("--watch-dir", action="store_true",
                        help="Watch all transcript.jsonl files under the given directory")
    args = parser.parse_args()

    if args.watch_dir:
        watch_dir(args.path)
        return

    path = _resolve_transcript(args.path)
    if args.summary:
        analyze_file(path).print_summary()
        return

    monitor = make_monitor(_detect_format(path))
    try:
        follow_file(path, monitor)
    except KeyboardInterrupt:
        print()
        monitor.print_summary()


if __name__ == "__main__":
    main()
