#!/usr/bin/env python3
"""
Vero benchmark runner.

Runs a solver against verification tasks under tasks/<category>_<Name>/
(e.g. eBPF_Cnum_Alu64Add, LLVM_KBUdiv, seL4_AllocRegion), in parallel,
optionally inside Docker containers, tracking progress via git commits.

Task liveness: a published solution (under solved/) is one web search
away, so a run either drops the solved tasks or takes away the web. By
default every task runs and the agents' web tools are disabled
(VERO_DISABLE_WEB=1); --run-unsolved runs only the unsolved tasks and
leaves the web tools enabled.
"""

import argparse
import contextlib
import fnmatch
import functools
import json
import os
import shlex
import shutil
import subprocess
import sys
import threading
import time
import uuid
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterator, List, Optional, Tuple


BENCH_NAME = "vero"
DOCKER_IMAGE = f"{BENCH_NAME}-lean4"
TEMPLATE_SCRIPT = "template/gen.py"
DOCKERFILE = "Dockerfile"
SOLVED_DIR = "solved"

# Mathlib is prebuilt into the image here (Dockerfile warm step). Linking a
# task's packages to it avoids a per-task clone/download and works offline.
WARM_PACKAGES = "/home/solver/vero-warm/.lake/packages"

DEFAULT_PROMPT = (
    "Read INSTRUCTION.md in this directory and solve the task, "
    "following its Workflow. Every submission is human-reviewed: "
    "a cheat scores ZERO even if `./check.sh` passes, so do not waste "
    "tokens building one. "
)

# Files that must not be modified by the solver — saved before, restored after.
# The toolchain and Lake config files are included because swapping them out
# would silently change what `lake lean Task.lean` evaluates.
PROTECTED_FILES = [
    ".provided_hash",
    "check.sh",
    "lakefile.lean",
    "lakefile.toml",
    "lean-toolchain",
    "lake-manifest.json",
    "INSTRUCTION.md",
]


@dataclass(frozen=True)
class Task:
    name: str           # e.g. "eBPF_Cnum_Alu64Add" (prefixed directory name)
    src_dir: Path       # source task dir in the bench repo
    run_dir: Path       # task dir inside --output-dir


@dataclass
class TaskResult:
    task: str
    status: str         # PASS, FAIL, ERROR, TIMEOUT
    solver_exit: Optional[int] = None
    check_exit: Optional[int] = None
    elapsed_s: float = 0.0
    error: str = ""

    def to_dict(self) -> Dict:
        return {
            "task": self.task,
            "status": self.status,
            "solver_exit": self.solver_exit,
            "check_exit": self.check_exit,
            "elapsed_s": round(self.elapsed_s, 1),
        }

    @classmethod
    def from_dict(cls, data: Dict) -> "TaskResult":
        return cls(
            task=data.get("task", ""),
            status=data.get("status", "UNKNOWN"),
            solver_exit=data.get("solver_exit"),
            check_exit=data.get("check_exit"),
            elapsed_s=data.get("elapsed_s", 0.0),
        )


@dataclass(frozen=True)
class RunCtx:
    solver_script: Path
    prompt: str
    timeout: int
    check_timeout: int
    abort_after: int
    no_docker: bool
    docker_extra_args: str
    docker_network: str
    output_dir: Path
    git_lock: threading.Lock
    fail_counter: "_FailCounter"
    rate_limit_tracker: "_RateLimitTracker"


class _FailCounter:
    """Thread-safe counter tracking consecutive solver errors. Used to
    decide whether to abort the remaining queue after repeated solver
    failures without killing the run on a single transient hiccup."""

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._count = 0

    def record_error(self) -> int:
        with self._lock:
            self._count += 1
            return self._count

    def record_success(self) -> None:
        with self._lock:
            self._count = 0

    def reset(self) -> None:
        with self._lock:
            self._count = 0


class _RateLimitTracker:
    """Thread-safe tracker for Claude Code usage-limit rejections.

    Parallel solvers all hit the same five-hour window, so we keep the
    max ``resetsAt`` (Unix seconds) seen across workers and let the
    main loop pause until the window reopens, then re-enter resume
    mode to rerun the aborted tasks.
    """

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._reset_at: Optional[int] = None

    def record(self, resets_at: int) -> None:
        with self._lock:
            if self._reset_at is None or resets_at > self._reset_at:
                self._reset_at = resets_at

    def was_hit(self) -> bool:
        with self._lock:
            return self._reset_at is not None

    def reset_time(self) -> Optional[int]:
        with self._lock:
            return self._reset_at

    def clear(self) -> None:
        with self._lock:
            self._reset_at = None


@dataclass
class ProcResult:
    exit_code: Optional[int]
    timed_out: bool
    stdout: str = ""
    stderr: str = ""


# ---------------------------------------------------------------------------
# Task discovery
# ---------------------------------------------------------------------------

@functools.lru_cache(maxsize=None)
def _load_gen_module(bench_root: Path):
    """Dynamically import template/gen.py (cached per bench_root)."""
    gen_py = bench_root / TEMPLATE_SCRIPT
    if not gen_py.exists():
        raise FileNotFoundError(f"Template generator not found: {gen_py}")
    import importlib.util
    spec = importlib.util.spec_from_file_location("task_templates", str(gen_py))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _resolve_dir_name(mod, operator: str) -> str:
    """Map an operator to its prefixed directory name via the gen module.

    e.g. "interval_alu32_add" -> "eBPF_Interval_Alu32Add", "kb_udiv" -> "LLVM_KBUdiv",
    "TnumStepUp" -> "eBPF_TnumStepUp". Falls through to the bare name
    if the operator isn't known.
    """
    for attr in vars(mod).values():
        if isinstance(attr, dict) and operator in attr:
            subs = attr[operator]
            if isinstance(subs, dict) and "LEAN_TASK_NAME" in subs:
                name = subs["LEAN_TASK_NAME"]
                return f"{mod._category_for(name)}_{name}"
    if operator in getattr(mod, "DIRECT_TASKS", ()):
        return f"{mod._category_for(operator)}_{operator}"
    return operator


def build_task_list(
    bench_root: Path,
    output_dir: Path,
    task_filter: Optional[List[str]],
    category_filter: Optional[List[str]] = None,
) -> List[Task]:
    """Build list of tasks to run.

    task_filter: fnmatch globs against operator names (e.g. 'cnum_alu64_*').
    category_filter: prefix names, case-insensitive (e.g. ['eBPF', 'LLVM']).
    Both filters are ANDed when present.
    """
    mod = _load_gen_module(bench_root)
    cat_set = {c.lower() for c in category_filter} if category_filter else None
    tasks: List[Task] = []
    for op in mod.list_available_operators():
        if task_filter and not any(fnmatch.fnmatch(op, pat) for pat in task_filter):
            continue
        name = _resolve_dir_name(mod, op)
        if cat_set is not None and name.split("_", 1)[0].lower() not in cat_set:
            continue
        tasks.append(Task(
            name=name,
            src_dir=bench_root / "tasks" / name,
            run_dir=output_dir / "tasks" / name,
        ))
    return tasks


# ---------------------------------------------------------------------------
# Task liveness (solved tasks)
# ---------------------------------------------------------------------------

def _solved_task_names(bench_root: Path) -> set:
    """Names of tasks with a published solution under solved/.

    A solved/ entry matches its task either by full directory name
    (LLVM_KBUmax) or by unprefixed name (TnumStepUp -> eBPF_TnumStepUp),
    the same convention build_site.py uses.
    """
    solved_dir = bench_root / SOLVED_DIR
    if not solved_dir.exists():
        return set()
    return {d.name for d in solved_dir.iterdir() if d.is_dir()}


def _is_solved(task_name: str, solved_names: set) -> bool:
    return task_name in solved_names or any(
        task_name.endswith("_" + n) for n in solved_names
    )


def filter_solved_tasks(
    tasks: List[Task], bench_root: Path, run_unsolved: bool, *,
    quiet: bool = False,
) -> List[Task]:
    """Drop solved tasks when --run-unsolved is set: that mode gives the
    agent web access, and a published solution is one search away."""
    solved = _solved_task_names(bench_root)
    if not run_unsolved or not solved:
        return tasks
    kept = [t for t in tasks if not _is_solved(t.name, solved)]
    n_skipped = len(tasks) - len(kept)
    if n_skipped and not quiet:
        names = ", ".join(t.name for t in tasks if _is_solved(t.name, solved))
        print(f"Skipping {n_skipped} solved tasks ({names}); "
              f"drop --run-unsolved to run them with web access disabled.")
    return kept


# ---------------------------------------------------------------------------
# Setup phases
# ---------------------------------------------------------------------------

def regenerate_tasks(bench_root: Path) -> None:
    """Run template/gen.py --all tasks/ to regenerate tasks."""
    gen_py = bench_root / TEMPLATE_SCRIPT
    if not gen_py.exists():
        print(f"WARNING: {gen_py} not found, skipping regeneration")
        return
    print("Regenerating lean4 tasks...")
    subprocess.run(
        [sys.executable, str(gen_py), "tasks", "--all"],
        cwd=str(bench_root),
        check=True,
    )


def setup_output_dir(
    bench_root: Path,
    output_dir: Path,
    tasks: List[Task],
) -> None:
    """Copy task directories into output dir."""
    output_dir.mkdir(parents=True, exist_ok=True)

    for task in tasks:
        if not task.src_dir.exists():
            print(f"WARNING: source dir not found: {task.src_dir}")
            continue
        if task.run_dir.exists():
            shutil.rmtree(task.run_dir)
        shutil.copytree(
            task.src_dir,
            task.run_dir,
            symlinks=False,
            ignore=shutil.ignore_patterns('.lake'),
        )


def _lean4_setup_lake(task: Task, ctx: "RunCtx") -> bool:
    """Make Mathlib available in the task's .lake dir.

    In Docker mode, link the task's `.lake/packages` to the Mathlib prebuilt
    into the image (Dockerfile warm step), so setup needs no per-task clone,
    no download, and no network. If the warm copy is missing (older image),
    fall back to `lake exe cache get`. In no-docker mode, always use
    `cache get`, which resolves and fetches over the network.

    A persistent failure is reported loudly, not as a buried WARNING, because
    the task will then fail to compile for a reason unrelated to the solver.
    """
    if ctx.no_docker:
        cmd, cwd = ["lake", "exe", "cache", "get"], task.run_dir
    else:
        setup = (
            f'if [ -d "{WARM_PACKAGES}" ]; then '
            f'mkdir -p .lake && rm -rf .lake/packages '
            f'&& ln -s "{WARM_PACKAGES}" .lake/packages; '
            f'else lake exe cache get; fi'
        )
        cmd = (_docker_run_base(task, ctx.docker_extra_args,
                                network=ctx.docker_network)
               + [DOCKER_IMAGE, "bash", "-c", setup])
        cwd = None
    result = _run(cmd, cwd=cwd, timeout=600)
    if result.timed_out:
        return False
    if result.exit_code != 0:
        # One retry for a transient hiccup on the network fallback path.
        result = _run(cmd, cwd=cwd, timeout=600)
    if result.exit_code != 0 and not result.timed_out:
        print(f"  ERROR: Mathlib setup failed for {task.name} — this task WILL "
              f"fail to compile (an environment problem, not a solver problem). "
              f"In Docker mode this links the image's prebuilt Mathlib; rebuild "
              f"the image (`make build`) if it is missing. Without Docker, "
              f"`lake exe cache get` needs network access.\n"
              f"         {result.stderr[:200]}", flush=True)
        return False
    return True


def _lean4_cleanup_lake(task_dir: Path) -> None:
    """Delete the task's .lake dir to free disk space."""
    lake_dir = task_dir / ".lake"
    if lake_dir.exists():
        shutil.rmtree(lake_dir, ignore_errors=True)


def git_init_output(output_dir: Path) -> None:
    """Initialize git repo in output dir with initial commit."""
    gitignore = output_dir / ".gitignore"
    gitignore.write_text(
        "# Lean4 build cache (symlinked from external)\n"
        ".lake/\n"
        "\n"
        "# Python\n"
        "__pycache__/\n"
        "*.py[cod]\n"
        "\n"
        "# Editor\n"
        ".vscode/\n"
        ".idea/\n"
        "*.swp\n"
        "*~\n"
    )
    subprocess.run(["git", "init"], cwd=str(output_dir), check=True,
                   capture_output=True)
    subprocess.run(["git", "add", "-A"], cwd=str(output_dir), check=True,
                   capture_output=True)
    subprocess.run(
        ["git", "commit", "-m", "Initial: clean task copies"],
        cwd=str(output_dir), check=True, capture_output=True,
    )
    print(f"Git repo initialized in {output_dir}")


# ---------------------------------------------------------------------------
# Docker
# ---------------------------------------------------------------------------

def build_docker_image(bench_root: Path) -> None:
    """Build the Lean4 Docker image.

    Passes the current user's UID/GID as build args so the in-container
    solver user matches the host user. This avoids chmod 777 hacks and
    ensures bind-mounted files have correct ownership.
    """
    dockerfile = bench_root / DOCKERFILE
    if not dockerfile.exists():
        print(f"WARNING: {dockerfile} not found, skipping build")
        return
    uid, gid = os.getuid(), os.getgid()
    print(f"Building {DOCKER_IMAGE} from {dockerfile} (UID={uid}, GID={gid})...")
    subprocess.run(
        [
            "docker", "build",
            "-f", str(dockerfile),
            "--build-arg", f"SOLVER_UID={uid}",
            "--build-arg", f"SOLVER_GID={gid}",
            "-t", DOCKER_IMAGE, str(bench_root),
        ],
        check=True,
    )
    print(f"Built {DOCKER_IMAGE}")


# ---------------------------------------------------------------------------
# Task execution
# ---------------------------------------------------------------------------


def _docker_user_args() -> List[str]:
    """Return docker run args to match the host user UID/GID.

    Runs the container process as the host user so mounted volume files
    have correct ownership. Build-time tools (elan, opam, rustup) are
    world-readable and work regardless of the runtime UID.
    """
    uid, gid = os.getuid(), os.getgid()
    return ["--user", f"{uid}:{gid}"]


DOCKER_TASK_DIR = "/task"
DOCKER_SOLVER_PATH = "/solver"

# Auth + solver-config env vars forwarded into Docker containers.
_AUTH_ENV_VARS = [
    # Set unless --run-unsolved; the solver scripts drop their web tools.
    "VERO_DISABLE_WEB",
    # Claude Code
    "CLAUDE_CODE_OAUTH_TOKEN",
    "ANTHROPIC_API_KEY",
    "CLAUDE_MAX_BUDGET_USD",
    "CLAUDE_MODEL",
    # Gemini CLI
    "GEMINI_API_KEY",
    "GOOGLE_API_KEY",
    # Codex CLI
    "CODEX_API_KEY",
    "OPENAI_API_KEY",
    # Codex custom provider (codex_cli.sh generates config.toml from these)
    "CODEX_BASE_URL",
    "CODEX_PROVIDER_NAME",
    "CODEX_MODEL",
    # Gemini model override
    "GEMINI_MODEL",
    # GitHub Copilot CLI (copilot.sh). Token precedence: COPILOT_GITHUB_TOKEN >
    # GH_TOKEN > GITHUB_TOKEN. Classic ghp_ PATs are not supported by Copilot.
    "COPILOT_GITHUB_TOKEN",
    "GH_TOKEN",
    "GITHUB_TOKEN",
    "COPILOT_MODEL",
    "COPILOT_CONTEXT",
    "COPILOT_EFFORT",
    "COPILOT_MAX_BUDGET_USD",
    "COPILOT_MAX_AI_CREDITS",
]


def _docker_run_base(
    task: Task,
    docker_extra_args: str,
    container_name: Optional[str] = None,
    solver_script: Optional[Path] = None,
    network: str = "",
) -> List[str]:
    """Build the base docker run command with proper volume mounts.

    Container mount points (well-known, fixed paths):
        /task            — task working directory (read-write)
        /solver          — solver script (read-only, when provided)

    Auth is passed via environment variables (CLAUDE_CODE_OAUTH_TOKEN,
    ANTHROPIC_API_KEY, GEMINI_API_KEY, CODEX_API_KEY, etc.), not via
    config-dir mounts.
    """
    task_dir = task.run_dir
    cmd = [
        "docker", "run", "--rm",
        *(["--network", network] if network else []),
        *_docker_user_args(),
        "-e", "HOME=/home/solver",
        "-v", f"{task_dir}:{DOCKER_TASK_DIR}",
        "-w", DOCKER_TASK_DIR,
    ]
    # Forward auth env vars if set on the host.
    for var in _AUTH_ENV_VARS:
        val = os.environ.get(var)
        if val:
            cmd.extend(["-e", f"{var}={val}"])
    if container_name:
        cmd.extend(["--name", container_name])
    if solver_script:
        cmd.extend(["-v", f"{solver_script}:{DOCKER_SOLVER_PATH}:ro"])
    if docker_extra_args:
        cmd.extend(shlex.split(docker_extra_args))
    return cmd


@contextlib.contextmanager
def _protected_files(task_dir: Path) -> Iterator[None]:
    """Snapshot PROTECTED_FILES, restore them on exit.

    The solver might rewrite or delete check.sh / .provided_hash; we
    always want a clean copy for the verification step, even if the
    solver crashes.
    """
    saved = {
        name: (task_dir / name).read_bytes()
        for name in PROTECTED_FILES if (task_dir / name).exists()
    }
    try:
        yield
    finally:
        for name, content in saved.items():
            path = task_dir / name
            path.write_bytes(content)
            if name == "check.sh":
                path.chmod(path.stat().st_mode | 0o111)


def _detect_rate_limit_reset(task_dir: Path) -> Optional[int]:
    """Return the Claude Code rate-limit reset timestamp, or None.

    Scans the solver transcript for a ``rate_limit_event`` with
    ``status == "rejected"`` and returns the latest ``resetsAt`` Unix
    timestamp seen. ``allowed`` / ``allowed_warning`` events are
    advisory and are ignored.
    """
    transcript = task_dir / "logs" / "transcript.jsonl"
    if not transcript.exists():
        return None
    latest: Optional[int] = None
    try:
        with open(transcript) as f:
            for line in f:
                if '"rate_limit_event"' not in line or '"rejected"' not in line:
                    continue
                try:
                    evt = json.loads(line)
                except json.JSONDecodeError:
                    continue
                info = evt.get("rate_limit_info") or {}
                if info.get("status") != "rejected":
                    continue
                resets_at = info.get("resetsAt")
                if isinstance(resets_at, (int, float)):
                    r = int(resets_at)
                    if latest is None or r > latest:
                        latest = r
    except OSError:
        return None
    return latest


def _run(
    cmd: List[str],
    *,
    cwd: Optional[Path] = None,
    timeout: int,
    container_kill: Optional[str] = None,
) -> ProcResult:
    """Run a subprocess, capture output, kill the container on timeout."""
    try:
        r = subprocess.run(
            cmd,
            cwd=str(cwd) if cwd else None,
            timeout=timeout,
            capture_output=True,
            text=True,
        )
        return ProcResult(r.returncode, False, r.stdout, r.stderr)
    except subprocess.TimeoutExpired:
        if container_kill:
            subprocess.run(
                ["docker", "kill", container_kill],
                capture_output=True, timeout=30,
            )
        return ProcResult(None, True)


def _append_log(
    path: Path, section: Optional[str], result: ProcResult, *, append: bool,
) -> None:
    """Write a ProcResult to the solver log.

    ``section=None`` emits ``=== STDOUT === / === STDERR ===`` (the
    solver run); ``section="CHECK"`` prefixes both headers with CHECK.
    """
    prefix = f"{section} " if section else ""
    mode = "a" if append else "w"
    with open(path, mode) as f:
        if append:
            f.write("\n")
        f.write(f"=== {prefix}STDOUT ===\n{result.stdout}\n"
                f"=== {prefix}STDERR ===\n{result.stderr}\n")


def _solver_invocation(
    task: Task, ctx: RunCtx,
) -> Tuple[List[str], Optional[Path], Optional[str]]:
    """Build the solver command. Returns (cmd, cwd, docker-container-name)."""
    if ctx.no_docker:
        return (
            [str(ctx.solver_script), str(task.run_dir), ctx.prompt],
            task.run_dir,
            None,
        )
    container = f"{BENCH_NAME}-solver-{task.name}-{uuid.uuid4().hex[:8]}"
    base = _docker_run_base(
        task, ctx.docker_extra_args,
        container_name=container,
        solver_script=ctx.solver_script,
        network=ctx.docker_network,
    )
    return (
        base + [DOCKER_IMAGE, DOCKER_SOLVER_PATH, DOCKER_TASK_DIR, ctx.prompt],
        None,
        container,
    )


def _check_invocation(
    task: Task, ctx: RunCtx,
) -> Tuple[List[str], Optional[Path], Optional[str]]:
    """Build the check.sh command. Returns (cmd, cwd, docker-container-name)."""
    if ctx.no_docker:
        return ["./check.sh"], task.run_dir, None
    container = f"{BENCH_NAME}-check-{task.name}-{uuid.uuid4().hex[:8]}"
    base = _docker_run_base(task, ctx.docker_extra_args, container_name=container,
                            network=ctx.docker_network)
    return base + [DOCKER_IMAGE, "./check.sh"], None, container


def _finalize(
    task: Task, ctx: RunCtx, *,
    status: str,
    solver_exit: Optional[int],
    check_exit: Optional[int],
    start: float,
    error: str = "",
) -> TaskResult:
    """Write result.json, git-commit, clean up the lake cache, return the TaskResult."""
    result = TaskResult(
        task=task.name, status=status,
        solver_exit=solver_exit, check_exit=check_exit,
        elapsed_s=time.time() - start, error=error,
    )
    (task.run_dir / "result.json").write_text(
        json.dumps(result.to_dict(), indent=2) + "\n"
    )
    _git_commit_task(task, status, ctx.git_lock, ctx.output_dir)
    _lean4_cleanup_lake(task.run_dir)
    return result


def run_task(
    task: Task, ctx: RunCtx, abort_event: threading.Event,
) -> TaskResult:
    """Run solver + check.sh for a single task.

    If ``abort_event`` is set when the task starts, skip it and return a
    synthetic ERROR with no subprocess invocation — this stops the bench
    from burning through remaining tasks after a solver failure.
    """
    if abort_event.is_set():
        return TaskResult(
            task=task.name, status="ERROR",
            error="skipped: aborted after earlier solver error",
        )

    start = time.time()
    log = task.run_dir / "solver.log"
    _lean4_setup_lake(task, ctx)

    solver_cmd, solver_cwd, solver_container = _solver_invocation(task, ctx)
    with _protected_files(task.run_dir):
        solver = _run(
            solver_cmd, cwd=solver_cwd, timeout=ctx.timeout,
            container_kill=solver_container,
        )
    _append_log(log, None, solver, append=False)

    if solver.timed_out:
        return _finalize(
            task, ctx, status="TIMEOUT",
            solver_exit=solver.exit_code, check_exit=None, start=start,
        )

    if solver.exit_code != 0:
        # Claude Code hit the five-hour usage limit: the solver exits
        # non-zero but the failure is recoverable by waiting for the
        # window to reset. Abort remaining work without counting this
        # toward --abort-after, and let the main loop handle the wait.
        reset_at = _detect_rate_limit_reset(task.run_dir)
        if reset_at is not None:
            ctx.rate_limit_tracker.record(reset_at)
            if not abort_event.is_set():
                abort_event.set()
                print(f"  [rate-limit] {task.name}: usage limit hit, "
                      f"resets at {reset_at}; skipping remaining tasks",
                      flush=True)
            return _finalize(
                task, ctx, status="ERROR",
                solver_exit=solver.exit_code, check_exit=None, start=start,
                error=f"Solver blocked by usage limit (resets_at={reset_at})",
            )
        # Only abort the remaining queue after repeated solver errors.
        # A single transient failure (network blip, CLI auth refresh) must
        # not nuke an overnight run; systemic failures still bail fast.
        n = ctx.fail_counter.record_error()
        if n >= ctx.abort_after and not abort_event.is_set():
            abort_event.set()
            print(f"  [abort] {n} solver errors in a row "
                  f"(threshold: {ctx.abort_after}); skipping remaining tasks",
                  flush=True)
        return _finalize(
            task, ctx, status="ERROR",
            solver_exit=solver.exit_code, check_exit=None, start=start,
            error=f"Solver exited with code {solver.exit_code}",
        )
    ctx.fail_counter.record_success()

    check_cmd, check_cwd, check_container = _check_invocation(task, ctx)
    check = _run(
        check_cmd, cwd=check_cwd, timeout=ctx.check_timeout,
        container_kill=check_container,
    )
    _append_log(log, "CHECK", check, append=True)
    check_exit = -1 if check.timed_out else check.exit_code

    status = "PASS" if check_exit == 0 else "FAIL"
    return _finalize(
        task, ctx, status=status,
        solver_exit=solver.exit_code, check_exit=check_exit, start=start,
    )


def _git_commit_task(
    task: Task, status: str,
    git_lock: threading.Lock, output_dir: Path,
) -> None:
    rel_path = f"tasks/{task.name}"
    with git_lock:
        try:
            subprocess.run(
                ["git", "add", f"{rel_path}/"],
                cwd=str(output_dir), check=True, capture_output=True,
            )
            subprocess.run(
                ["git", "commit", "-m", f"{status}({task.name}): auto"],
                cwd=str(output_dir), check=True, capture_output=True,
            )
        except subprocess.CalledProcessError:
            pass  # Nothing to commit (e.g. solver didn't change anything)


# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------

def _collect_all_results(output_dir: Path) -> List[TaskResult]:
    """Read result.json from every task directory in the output dir."""
    tasks_dir = output_dir / "tasks"
    if not tasks_dir.exists():
        return []
    results: List[TaskResult] = []
    for task_dir in sorted(tasks_dir.iterdir()):
        result_file = task_dir / "result.json"
        if not (task_dir.is_dir() and result_file.exists()):
            continue
        try:
            data = json.loads(result_file.read_text())
        except (json.JSONDecodeError, OSError):
            continue
        data.setdefault("task", task_dir.name)
        results.append(TaskResult.from_dict(data))
    return results


_STATUS_ORDER = ("PASS", "FAIL", "ERROR", "TIMEOUT")


def _print_results_table(results: List[TaskResult], title: str) -> None:
    """Print a formatted results table with a status-count footer."""
    from collections import Counter
    print()
    print(title)
    print("=" * 70)
    print(f"  {'Task':<36} {'Status':<10} {'Time':>8}")
    print("-" * 70)
    for r in sorted(results, key=lambda x: x.task):
        print(f"  {r.task:<36} {r.status:<10} {r.elapsed_s:>7.0f}s")
    print("=" * 70)

    counts = Counter(r.status for r in results)
    parts = [f"Total: {len(results)}"] + [
        f"{s}: {counts[s]}" for s in _STATUS_ORDER if counts.get(s)
    ]
    print("  " + "  ".join(parts))
    print()


def print_summary(
    results: List[TaskResult], output_dir: Path, is_resume: bool = False,
) -> None:
    """Print results table(s) and write aggregate results.json.

    In resume mode, prints both the current-run table and the full
    cross-run table (aggregated from disk).
    """
    if is_resume:
        _print_results_table(results, "CURRENT RUN RESULTS")

    disk = _collect_all_results(output_dir)
    final = disk or results
    if disk or not is_resume:
        title = "FULL BENCHMARK RESULTS" if is_resume else "BENCHMARK RESULTS"
        _print_results_table(final, title)

    results_file = output_dir / "results.json"
    results_file.write_text(
        json.dumps([r.to_dict() for r in final], indent=2) + "\n"
    )
    print(f"Results written to {results_file}")


# ---------------------------------------------------------------------------
# Dry run
# ---------------------------------------------------------------------------

def dry_run(tasks: List[Task], solver_script: Path, no_docker: bool) -> None:
    """Print what would be executed without running anything."""
    print(f"\nDRY RUN — {len(tasks)} tasks, solver: {solver_script}\n")
    mode = "direct" if no_docker else f"docker:{DOCKER_IMAGE}"
    for t in sorted(tasks, key=lambda x: x.name):
        print(f"  [{mode}] {t.name}")
        print(f"    src: {t.src_dir}")
        print(f"    run: {t.run_dir}")
    print()


# ---------------------------------------------------------------------------
# Resume mode helpers
# ---------------------------------------------------------------------------

def _find_resumable_tasks(
    tasks: List[Task], bench_root: Path,
) -> List[Task]:
    """Filter tasks to those with ERROR status from a previous run.

    Reads each task's result.json in the output dir.  Tasks with PASS,
    FAIL, or TIMEOUT are skipped — those are legitimate benchmark
    results; re-running them would give the solver extra attempts.
    Only ERROR (solver crashed / infrastructure failure) is resumable.
    For each ERROR task, restores all source files from the source
    directory so the solver gets a clean starting point.
    """
    resumable: List[Task] = []
    for task in tasks:
        result_file = task.run_dir / "result.json"
        if not result_file.exists():
            # No result yet — treat as new, include it
            resumable.append(task)
            continue
        try:
            data = json.loads(result_file.read_text())
        except (json.JSONDecodeError, OSError):
            resumable.append(task)
            continue
        status = data.get("status", "")
        if status == "ERROR":
            # Restore all source files so the solver gets a clean slate
            _restore_task_source_files(task, bench_root)
            resumable.append(task)
        else:
            print(f"  Skipping {task.name} (previous status: {status})")
    return resumable


def _restore_task_source_files(task: Task, bench_root: Path) -> None:
    """Restore all source files from the source task directory.

    Copies every file from the source directory into the run directory,
    giving the solver a completely clean starting point (Task.lean,
    INSTRUCTION.md, check.sh, .provided_hash, lakefile.lean, etc.).
    Only .lake/ and run-time artifacts (logs/, result.json, solver.log)
    are left untouched.
    """
    src_dir = bench_root / "tasks" / task.name
    if not src_dir.exists():
        print(f"  WARNING: source dir {src_dir} not found, cannot restore files")
        return

    for src_file in src_dir.iterdir():
        if src_file.name.startswith('.lake'):
            continue
        if src_file.is_file():
            dst_file = task.run_dir / src_file.name
            shutil.copy2(str(src_file), str(dst_file))
            # Ensure scripts remain executable
            if src_file.name.endswith('.sh'):
                dst_file.chmod(dst_file.stat().st_mode | 0o111)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Vero benchmark runner",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--output-dir", required=True,
        help="Execution directory (will be created if needed)",
    )
    parser.add_argument(
        "--solver", required=True,
        help="Path to solver script. Invoked as: <script> <task_dir> <prompt>",
    )
    parser.add_argument(
        "--prompt", default=DEFAULT_PROMPT,
        help="Prompt text passed to the solver via {prompt} placeholder.",
    )
    parser.add_argument(
        "--tasks", default=None,
        help="Comma-separated task/operator globs to run (default: all). "
             "e.g. 'cnum_alu64_*,kb_udiv'. ANDed with --categories if both set.",
    )
    parser.add_argument(
        "--categories", default=None,
        help="Comma-separated category filter: eBPF, LLVM, seL4 "
             "(case-insensitive). e.g. 'eBPF,LLVM' runs all tasks "
             "except seL4. ANDed with --tasks if both set.",
    )
    parser.add_argument(
        "--run-unsolved", action="store_true",
        help="Run only the tasks with no published solution (under "
             "solved/), with the agents' web tools enabled. By default "
             "every task runs and the web tools are disabled "
             "(VERO_DISABLE_WEB=1), which keeps the solved tasks in the "
             "suite without a published solution being one search away.",
    )
    parser.add_argument(
        "--parallel", type=int, default=1,
        help="Number of parallel workers (default: 1)",
    )
    parser.add_argument(
        "--timeout", type=float, default=3.0, metavar="HOURS",
        help="Per-task solver timeout in hours (default: 3.0)",
    )
    parser.add_argument(
        "--check-timeout", type=int, default=600, metavar="SECONDS",
        help="Per-task check.sh timeout in seconds (default: 600). Full "
             "check runs `lake lean` twice; larger proofs need more.",
    )
    parser.add_argument(
        "--max-budget-usd", type=float, default=None, metavar="USD",
        help="Per-task $ cap forwarded to the solver (CLAUDE_MAX_BUDGET_USD "
             "for claude_code.sh, COPILOT_MAX_BUDGET_USD for copilot.sh). "
             "copilot.sh defaults to $30 when this is unset; claude_code.sh "
             "is unlimited by default.",
    )
    parser.add_argument(
        "--abort-after", type=int, default=3,
        help="Abort the remaining queue after this many consecutive solver "
             "errors (default: 3). Protects against single transient "
             "solver hiccups killing a long run.",
    )
    parser.add_argument(
        "--no-docker", action="store_true",
        help="Run solver and check.sh directly on host (no containers)",
    )
    parser.add_argument(
        "--docker-extra-args", default="",
        help='Extra args for docker run (e.g. "-e MY_VAR=value")',
    )
    parser.add_argument(
        "--docker-network", default="host", metavar="NET",
        help="Docker network for container runs (default: host). host lets the "
             "solver reach model APIs on machines where the default bridge has "
             "no outbound DNS. Pass an empty string to use the docker default.",
    )
    parser.add_argument(
        "--build-images", action="store_true",
        help="Build Docker images before running",
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="Show what would run without executing",
    )
    parser.add_argument(
        "--force", action="store_true",
        help="Overwrite existing output directory without prompting",
    )
    parser.add_argument(
        "--resume", action="store_true",
        help="Resume a previous run: re-run only ERROR tasks (solver crashes), skipping PASS/FAIL/TIMEOUT. "
             "Reuses the existing output dir.",
    )
    parser.add_argument(
        "--no-rate-limit-wait", action="store_true",
        help="Do not wait and retry after the Claude Code usage limit is "
             "hit. By default, the runner parses the solver transcript for "
             "the reset timestamp, sleeps until it passes, and re-enters "
             "resume mode to rerun the aborted tasks.",
    )
    parser.add_argument(
        "--rate-limit-max-retries", type=int, default=5,
        help="Maximum number of rate-limit wait/resume cycles before "
             "giving up (default: 5). Guards against an infinite loop "
             "if the limit keeps firing without progress.",
    )
    parser.add_argument(
        "--rate-limit-buffer-s", type=int, default=300,
        help="Extra seconds to wait past resetsAt before retrying "
             "(default: 300). Avoids racing the server's clock.",
    )
    args = parser.parse_args()

    bench_root = Path(__file__).resolve().parent.parent  # scripts/ -> repo root
    output_dir = Path(args.output_dir).resolve()
    task_filter = [t.strip() for t in args.tasks.split(",")] if args.tasks else None
    category_filter = (
        [c.strip() for c in args.categories.split(",")] if args.categories else None
    )
    # Validate categories up front — typos would otherwise silently match nothing.
    if category_filter:
        valid = {"ebpf", "llvm", "sel4"}
        bad = [c for c in category_filter if c.lower() not in valid]
        if bad:
            parser.error(
                f"unknown --categories entries: {bad}. Valid: eBPF, LLVM, seL4."
            )
    solver_script = Path(args.solver).resolve()

    if not solver_script.is_file():
        parser.error(f"Solver script not found: {solver_script}")
    if not os.access(solver_script, os.X_OK):
        parser.error(f"Solver script is not executable: {solver_script}")

    # The solver scripts read this and drop their web tools; Docker mode
    # forwards it via _AUTH_ENV_VARS.
    if not args.run_unsolved:
        os.environ["VERO_DISABLE_WEB"] = "1"
        print("All tasks included; agent web access disabled.")
    else:
        print("Unsolved tasks only; agent web access enabled.")

    if args.resume:
        if args.force:
            parser.error("--resume and --force are mutually exclusive")
        if not (output_dir / ".git").exists():
            print(f"ERROR: Cannot resume — output dir has no previous run: {output_dir}")
            sys.exit(1)

        print("Resume mode: scanning previous results...")
        # Discover all tasks (need the full list to find which errored)
        tasks = build_task_list(bench_root, output_dir, task_filter, category_filter)
        tasks = filter_solved_tasks(tasks, bench_root, args.run_unsolved)
        tasks = _find_resumable_tasks(tasks, bench_root)
        if not tasks:
            print("No ERROR tasks to resume. Exiting.")
            return
        print(f"  {len(tasks)} ERROR tasks to re-run\n")

    else:
        if (output_dir / ".git").exists() and not args.dry_run:
            if args.force:
                print(f"WARNING: Removing existing output dir: {output_dir}")
                shutil.rmtree(output_dir)
            else:
                print(f"ERROR: Output directory already exists with previous results: {output_dir}")
                print("  Use --force to overwrite, or choose a different --output-dir.")
                sys.exit(1)

        print("Phase 1: Regenerating tasks from templates...")
        regenerate_tasks(bench_root)

        print("Phase 1: Discovering tasks...")
        tasks = build_task_list(bench_root, output_dir, task_filter, category_filter)
        tasks = filter_solved_tasks(tasks, bench_root, args.run_unsolved)
        if not tasks:
            print("No tasks matched. Exiting.")
            return

        if args.dry_run:
            dry_run(tasks, solver_script, args.no_docker)
            return

        print(f"Phase 1: Setting up output dir ({output_dir})...")
        setup_output_dir(bench_root, output_dir, tasks)
        git_init_output(output_dir)
        print(f"  {len(tasks)} tasks ready\n")

    if args.build_images and not args.no_docker:
        print("Phase 2: Building Docker image...")
        build_docker_image(bench_root)
        print()

    # Forward the per-task $ cap into the solver subprocess environment.
    # The Docker forwarder (_AUTH_ENV_VARS) and no-docker mode both inherit
    # from the parent's os.environ, so setting it here is sufficient. Set the
    # var for every bundled solver so --max-budget-usd is solver-agnostic.
    if args.max_budget_usd is not None:
        os.environ["CLAUDE_MAX_BUDGET_USD"] = str(args.max_budget_usd)
        os.environ["COPILOT_MAX_BUDGET_USD"] = str(args.max_budget_usd)

    timeout_s = int(args.timeout * 3600)
    budget_str = (f"${args.max_budget_usd:.2f}"
                  if args.max_budget_usd is not None else "unlimited")

    ctx = RunCtx(
        solver_script=solver_script,
        prompt=args.prompt,
        timeout=timeout_s,
        check_timeout=args.check_timeout,
        abort_after=args.abort_after,
        no_docker=args.no_docker,
        docker_extra_args=args.docker_extra_args,
        docker_network=args.docker_network,
        output_dir=output_dir,
        git_lock=threading.Lock(),
        fail_counter=_FailCounter(),
        rate_limit_tracker=_RateLimitTracker(),
    )

    all_results: List[TaskResult] = []
    rate_limit_retries = 0

    while True:
        is_retry = rate_limit_retries > 0
        label = (f"Phase 3 (rate-limit resume #{rate_limit_retries})"
                 if is_retry else "Phase 3")
        print(f"{label}: Running {len(tasks)} tasks (parallel={args.parallel}, "
              f"timeout={args.timeout}h, budget={budget_str}, "
              f"docker={'off' if args.no_docker else 'on'}, "
              f"web={'on' if args.run_unsolved else 'off'})...\n")

        # Set once the fail counter crosses --abort-after consecutive solver
        # errors, or once any worker detects a rate-limit rejection; pending
        # tasks then return ERROR without invoking the solver.
        abort_event = threading.Event()
        results: List[TaskResult] = []

        with ThreadPoolExecutor(max_workers=args.parallel) as pool:
            futures = {pool.submit(run_task, task, ctx, abort_event): task
                       for task in tasks}
            for future in as_completed(futures):
                task = futures[future]
                try:
                    result = future.result()
                except Exception as e:
                    print(f"  EXCEPTION  {task.name}: {e}")
                    result = TaskResult(task=task.name, status="ERROR", error=str(e))
                results.append(result)
                print(f"  {result.status:>7}  {result.task} ({result.elapsed_s:.0f}s)")

        all_results.extend(results)

        if not ctx.rate_limit_tracker.was_hit():
            break
        if args.no_rate_limit_wait:
            print("\n[rate-limit] Usage limit detected but "
                  "--no-rate-limit-wait is set; stopping.")
            break
        if rate_limit_retries >= args.rate_limit_max_retries:
            print(f"\n[rate-limit] Reached --rate-limit-max-retries="
                  f"{args.rate_limit_max_retries}; stopping.")
            break

        reset_ts = ctx.rate_limit_tracker.reset_time()
        wake_at = reset_ts + args.rate_limit_buffer_s
        wait_s = max(0.0, wake_at - time.time())
        reset_iso = time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime(reset_ts))
        wake_iso = time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime(wake_at))
        print(f"\n[rate-limit] Claude Code usage limit hit. "
              f"Resets at {reset_iso}.")
        print(f"[rate-limit] Sleeping {wait_s:.0f}s (until {wake_iso}, "
              f"including {args.rate_limit_buffer_s}s buffer)...", flush=True)
        if wait_s > 0:
            time.sleep(wait_s)

        ctx.rate_limit_tracker.clear()
        ctx.fail_counter.reset()
        rate_limit_retries += 1

        # Resume mode: pick up ERROR tasks (which includes every task
        # aborted by this rate-limit event) and restore their source
        # files so the next attempt starts from a clean slate.
        print(f"\n[rate-limit] Re-entering resume mode "
              f"(attempt #{rate_limit_retries})...")
        full_tasks = build_task_list(
            bench_root, output_dir, task_filter, category_filter,
        )
        full_tasks = filter_solved_tasks(
            full_tasks, bench_root, args.run_unsolved, quiet=True,
        )
        tasks = _find_resumable_tasks(full_tasks, bench_root)
        if not tasks:
            print("[rate-limit] No ERROR tasks remain; done.")
            break
        print(f"[rate-limit] {len(tasks)} tasks to rerun.\n")

    is_resume_view = args.resume or rate_limit_retries > 0
    print_summary(all_results, output_dir, is_resume=is_resume_view)


if __name__ == "__main__":
    main()
