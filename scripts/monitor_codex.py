#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import time
from collections import Counter
from pathlib import Path

from monitor import BOLD, CYAN, DIM, GREEN, NC, RED, SolverMonitor, fmt_duration, short_cmd


def compact(value, limit=180):
    text = " ".join(str(value).split())
    return text if len(text) <= limit else text[:limit - 3] + "..."


class CodexMonitor(SolverMonitor):
    def __init__(self, name=""):
        super().__init__()
        self.name = name
        self.state = "waiting"
        self.thread_id = None
        self.last_activity = "waiting for events"
        self.last_error = ""
        self.usage_reported = False
        self.seen_items = set()
        self.completed_items = set()
        self.tool_counts = Counter()

    def emit(self, text):
        print(f"  {DIM}[{self._elapsed_str()} {self.name}]{NC} {text}", flush=True)

    def process_event(self, ev, *, live=True):
        ts = ev.get("ts")
        if isinstance(ts, (int, float)):
            self._update_start(ts)
        kind = ev.get("type", "")
        if kind == "thread.started":
            self.thread_id = ev.get("thread_id")
            self.seen_items.clear()
            self.completed_items.clear()
            self._pending_tools.clear()
            self.state = "starting"
            self.last_activity = "session started"
            if live:
                self.emit(f"{BOLD}session started{NC}")
        elif kind == "turn.started":
            self.state = "running"
            self.last_activity = "waiting for agent"
            if live:
                self.emit(f"{BOLD}turn started{NC}")
        elif kind == "turn.completed":
            self.turn_count += 1
            usage = ev.get("usage") or {}
            self.usage_reported = bool(usage) or self.usage_reported
            self.total_input_tokens += usage.get("input_tokens", 0) or 0
            self.total_cached_tokens += usage.get("cached_input_tokens", 0) or 0
            self.total_output_tokens += usage.get("output_tokens", 0) or 0
            self.state = "agent finished"
            self.last_activity = "turn completed"
            if live:
                self.emit(f"{GREEN}turn completed{NC} | tokens in/cache/out: "
                          f"{self.total_input_tokens:,}/{self.total_cached_tokens:,}/"
                          f"{self.total_output_tokens:,}")
        elif kind in ("error", "turn.failed"):
            error = ev.get("error") or ev.get("message") or "unknown error"
            self.last_error = compact(error.get("message", error) if isinstance(error, dict) else error)
            if kind == "turn.failed":
                self.state = "failed"
            self.last_activity = self.last_error
            if live:
                self.emit(f"{RED}{kind}: {self.last_error}{NC}")
        elif kind in ("item.started", "item.updated", "item.completed"):
            item = ev.get("item")
            if isinstance(item, dict):
                self.process_item(item, kind, ts, live)

    def process_item(self, item, event_kind, ts, live):
        kind = item.get("type", "unknown")
        item_id = item.get("id")
        done = event_kind == "item.completed"
        if item_id is not None and item_id in self.completed_items:
            return
        if kind in ("agent_message", "reasoning", "error"):
            if not done:
                return
            text = compact(item.get("text") or item.get("message") or "", 300)
            if kind == "agent_message":
                self.agent_message_count += 1
            if kind == "error":
                self.last_error = text
            self.last_activity = f"{kind}: {text}"
            if live and text:
                color = RED if kind == "error" else BOLD
                self.emit(f"{color}{kind}:{NC} {text}")
        elif kind == "todo_list":
            todos = item.get("items") or []
            completed = sum(bool(todo.get("completed")) for todo in todos)
            self.last_activity = f"plan: {completed}/{len(todos)} complete"
            if live:
                self.emit(self.last_activity)
        else:
            label = self.item_label(item)
            fresh = item_id is None or item_id not in self.seen_items
            if fresh:
                self.cmd_count += 1
                self.tool_counts[kind] += 1
                if kind == "command_execution":
                    self._track_command(item.get("command") or "")
                if item_id is not None:
                    self.seen_items.add(item_id)
                    if isinstance(ts, (int, float)) and not done:
                        self._pending_tools[item_id] = (ts, label)
                if live and not done:
                    self.emit(f"{CYAN}start{NC} {label}")
            self.last_activity = label
            if done:
                pending = self._pending_tools.pop(item_id, None)
                duration = ""
                if pending is not None and isinstance(ts, (int, float)):
                    elapsed = max(0, ts - pending[0])
                    self._record_tool_duration(elapsed, label)
                    duration = f" ({fmt_duration(elapsed)})"
                result = item.get("result") or {}
                failed = (item.get("status") == "failed" or bool(item.get("error"))
                          or item.get("exit_code") not in (None, 0)
                          or isinstance(result, dict) and result.get("isError", False))
                status = "failed" if failed else "done"
                suffix = f" exit={item['exit_code']}" if item.get("exit_code") is not None else ""
                if live:
                    color = RED if failed else GREEN
                    self.emit(f"{color}{status}{NC} {label}{suffix}{duration}")
        if done and item_id is not None:
            self.completed_items.add(item_id)

    @staticmethod
    def item_label(item):
        kind = item.get("type", "unknown")
        if kind == "command_execution":
            return "shell " + short_cmd(item.get("command") or "", 140)
        if kind == "mcp_tool_call":
            label = f"MCP {item.get('server', '')}.{item.get('tool', '')}"
            args = item.get("arguments") or {}
            if isinstance(args, dict):
                detail = next((args[key] for key in ("file_path", "file", "path", "query") if args.get(key)), "")
                if detail:
                    label += " " + compact(detail, 80)
            return label
        if kind == "file_change":
            changes = item.get("changes") or []
            return "edit " + compact(", ".join(str(change.get("path", "")) for change in changes))
        if kind == "web_search":
            return "search " + compact(item.get("query") or "")
        return compact(kind)

    def print_progress(self):
        now = time.time()
        end = now if self.state in ("waiting", "starting", "running") else self.last_ts
        elapsed = fmt_duration(max(0, end - self.start_ts)) if end is not None and self.start_ts is not None else "?"
        idle = fmt_duration(max(0, now - self.last_ts)) if self.last_ts is not None else "?"
        pending = [f"{label} ({fmt_duration(max(0, now - start))})"
                   for start, label in self._pending_tools.values()]
        activity = "active: " + "; ".join(pending[:2]) if pending else "last: " + self.last_activity
        if len(pending) > 2:
            activity += f"; +{len(pending) - 2} more"
        print(f"  {DIM}[{self.name}]{NC} {self.state} | elapsed={elapsed} idle={idle} "
              f"tools={self.cmd_count} | {activity}", flush=True)

    def print_summary(self):
        wall = (max(0, self.last_ts - self.start_ts)
                if self.start_ts is not None and self.last_ts is not None else 0)
        print(f"\n{BOLD}Codex ({self.name}){NC} | {self.state} | event span={fmt_duration(wall)}")
        print(f"  Messages: {self.agent_message_count}  Tools: {self.cmd_count}  "
              f"Completed turns: {self.turn_count}")
        print(f"  check.sh runs: {self.check_sh_count}  lake build/lean: {self.lake_build_count}")
        if self.tool_counts:
            print("  " + ", ".join(f"{kind}={count}" for kind, count in sorted(self.tool_counts.items())))
        if self.usage_reported:
            print(f"  Tokens (in/cache/out): {self.total_input_tokens:,} / "
                  f"{self.total_cached_tokens:,} / {self.total_output_tokens:,}")
        else:
            print("  Tokens: not reported; Codex reports usage when a turn completes")
        if self.last_error:
            print(f"  Last error: {self.last_error}")
        print(f"  Last activity: {self.last_activity}")
        if self._pending_tools:
            print("  Pending: " + "; ".join(label for _, label in self._pending_tools.values()))
        if self.slowest:
            print("  Slowest tool calls:")
            for duration, label in self.slowest:
                if duration >= 0.1:
                    print(f"    {fmt_duration(duration):>8}  {label}")


class Transcript:
    def __init__(self, path):
        self.path = path
        self.monitor = CodexMonitor(path.parent.parent.name)
        self.offset = 0
        self.buffer = b""
        self.identity = None
        self.result_status = None

    def read(self, *, live=True, finish=False):
        try:
            stat = self.path.stat()
        except FileNotFoundError:
            return
        identity = (stat.st_dev, stat.st_ino)
        if self.identity is not None and (identity != self.identity or stat.st_size < self.offset):
            self.monitor = CodexMonitor(self.monitor.name)
            self.offset = 0
            self.buffer = b""
            self.result_status = None
            if live:
                self.monitor.emit("transcript restarted")
        self.identity = identity
        with self.path.open("rb") as stream:
            stream.seek(self.offset)
            while chunk := stream.read(1024 * 1024):
                self.offset = stream.tell()
                lines = (self.buffer + chunk).split(b"\n")
                self.buffer = lines.pop()
                for line in lines:
                    self.process_line(line, live)
        if finish and self.buffer:
            self.process_line(self.buffer, live)
            self.buffer = b""
        result_file = self.path.parent.parent / "result.json"
        try:
            status = json.loads(result_file.read_text()).get("status")
            if self.monitor.start_ts is not None and result_file.stat().st_mtime < self.monitor.start_ts:
                status = None
        except (OSError, ValueError, AttributeError):
            status = None
        if status is None:
            self.result_status = None
        if status and status != self.result_status:
            self.result_status = status
            self.monitor.state = status
            if live:
                self.monitor.emit(f"{BOLD}benchmark result: {status}{NC}")

    def process_line(self, line, live):
        try:
            event = json.loads(line)
        except (ValueError, UnicodeError):
            return
        if isinstance(event, dict):
            self.monitor.process_event(event, live=live)


def transcript_path(path):
    if path.is_file():
        return path
    direct = path / "logs/transcript.jsonl"
    if direct.is_file():
        return direct
    candidates = list(path.rglob("logs/transcript.jsonl"))
    if len(candidates) == 1:
        return candidates[0]
    if len(candidates) > 1:
        raise ValueError("Multiple transcripts found; use --watch-dir")
    raise ValueError(f"No transcript.jsonl found under {path}")


def watch(path, directory, heartbeat):
    readers = {}
    last_scan = last_heartbeat = 0.0
    root = path / "tasks" if (path / "tasks").is_dir() else path
    print(f"{BOLD}[monitor]{NC} Codex: {path} (Ctrl+C to stop)", flush=True)
    try:
        while True:
            now = time.monotonic()
            if now - last_scan >= 1 or not readers:
                paths = sorted(root.rglob("logs/transcript.jsonl")) if directory else [path]
                for transcript in paths:
                    if transcript not in readers:
                        reader = readers[transcript] = Transcript(transcript)
                        reader.read(live=False)
                        reader.monitor.print_progress()
                last_scan = now
            for reader in readers.values():
                reader.read()
            if heartbeat > 0 and now - last_heartbeat >= heartbeat:
                if last_heartbeat:
                    active = [r for r in readers.values() if not r.result_status]
                    for reader in active:
                        reader.monitor.print_progress()
                    if directory:
                        results = Counter(r.result_status for r in readers.values() if r.result_status)
                        counts = ", ".join(f"{status}={count}" for status, count in sorted(results.items()))
                        print(f"  {DIM}[monitor]{NC} tracked={len(readers)} pending={len(active)}"
                              + (f" | {counts}" if counts else ""), flush=True)
                last_heartbeat = now
            time.sleep(0.2)
    except KeyboardInterrupt:
        for reader in readers.values():
            reader.monitor.print_summary()


def main():
    parser = argparse.ArgumentParser(description="Live progress for Codex solver transcripts")
    parser.add_argument("path", type=Path)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--summary", action="store_true", help="Print a transcript summary and exit")
    mode.add_argument("--watch-dir", action="store_true", help="Follow current and newly created task transcripts")
    parser.add_argument("--heartbeat", type=float, default=15,
                        help="Seconds between progress updates; 0 disables them (default: 15)")
    args = parser.parse_args()
    if args.heartbeat < 0:
        parser.error("--heartbeat must be non-negative")
    if args.watch_dir:
        if not args.path.is_dir():
            parser.error(f"Not a directory: {args.path}")
        watch(args.path, True, args.heartbeat)
        return
    try:
        path = transcript_path(args.path)
    except ValueError as error:
        parser.error(str(error))
    if args.summary:
        reader = Transcript(path)
        reader.read(live=False, finish=True)
        reader.monitor.print_summary()
    else:
        watch(path, False, args.heartbeat)


if __name__ == "__main__":
    main()
