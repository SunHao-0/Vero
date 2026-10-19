#!/usr/bin/env python3
"""Static site generator for the Vero benchmark.

Scans tasks/ and solved/ and emits a self-contained static site under site/:
an index of all problems and one page per problem. Every problem page bundles
the files a visitor needs to borrow the task (Task.lean, INSTRUCTION.md, and the
Lake project files) and shows any published agent solution. The output is plain
HTML/CSS with a small progressive-enhancement script, so it works on GitHub
Pages with no build step at serve time.

Usage:
    python3 scripts/build_site.py [--repo-url URL] [--out site]
"""
import argparse
import html
import json
import re
import shutil
import statistics
from datetime import datetime
from pathlib import Path

BENCH_ROOT = Path(__file__).resolve().parent.parent
TASKS_DIR = BENCH_ROOT / "tasks"
SOLVED_DIR = BENCH_ROOT / "solved"
RUNS_DIR = BENCH_ROOT / "assets" / "runs"
LOGOS_DIR = BENCH_ROOT / "assets" / "logos"
DEFAULT_REPO_URL = "https://github.com/SunHao-0/Vero"
KERNEL_COMMIT_URL = ("https://git.kernel.org/pub/scm/linux/kernel/git/bpf/"
                     "bpf-next.git/commit/?id=833ef4a954e1")

# Files bundled on each problem page for borrowing. The checker is deliberately
# excluded; a borrower needs the spec, the instruction, and a buildable project.
BORROW_FILES = ["Task.lean", "INSTRUCTION.md", "lakefile.lean",
                "lean-toolchain", "lake-manifest.json"]

AREAS = {
    "eBPF": "Abstract interpretation transfer functions from the Linux kernel "
            "eBPF verifier. Each operator must be sound and strictly more "
            "precise than the current implementation.",
    "LLVM": "KnownBits and DemandedBits transfer functions from LLVM: the "
            "forward and backward bit-level analyses the optimizer relies on.",
    "seL4": "Optimizations for the seL4 microkernel and CapDL, specified "
            "against the kernel's data-structure invariants.",
}


def esc(s: str) -> str:
    return html.escape(s, quote=True)


def read(p: Path) -> str:
    try:
        return p.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


# --- Task metadata -----------------------------------------------------------

def title_of(content: str, fallback: str) -> str:
    """Descriptive title from the header doc comment (mirrors gen.py)."""
    for line in content.splitlines():
        m = re.match(r'^\s*.*?\b(?:Task|Optimization)\s*:\s*(.+)', line, re.I)
        if m:
            return m.group(1).strip()
    return fallback


def description_of(content: str) -> str:
    """Text of the leading /- ... -/ doc comment, minus the title line."""
    m = re.search(r'/-(.*?)-/', content, re.S)
    if not m:
        return ""
    body = [l.strip() for l in m.group(1).strip().splitlines()]
    # Drop the first line (the title, shown separately) and rejoin paragraphs.
    body = body[1:] if body else body
    return " ".join(l for l in body if l).strip()


def group_of(name: str, content: str) -> str:
    if name.startswith("eBPF_Cnum"):
        return "Cnum"
    if name.startswith("eBPF_Interval"):
        return "Interval"
    if name.startswith("eBPF_Const"):
        return "Const"
    if name.startswith("eBPF_Tnum"):
        return "Tnum"
    if name.startswith("LLVM_KB"):
        return "KnownBits"
    if name.startswith("LLVM_DB"):
        return "DemandedBits"
    # seL4 sub-groups are marked in the header doc comment, not the title.
    if re.search(r'Candidate seL4-style', content):
        return "Candidate"
    if re.search(r'CapDL', content):
        return "CapDL"
    return "Core"


def sections_of(content: str):
    """Split Task.lean into ordered (name, kind, body) segments by markers."""
    marker = re.compile(
        r'^--\s*===\s*BEGIN:\s*([A-Za-z_]+)\s*\((provided|editable)\b[^)]*\)\s*===\s*$',
        re.M)
    segs, last, cur = [], 0, None
    for m in marker.finditer(content):
        if cur:
            body = content[last:m.start()]
            body = re.sub(r'^--\s*===\s*END:[^\n]*\n?', '', body, flags=re.M)
            segs.append((cur[0], cur[1], body.strip("\n")))
        cur, last = (m.group(1), m.group(2)), m.end()
    if cur:
        body = content[last:]
        body = re.sub(r'^--\s*===\s*END:[^\n]*\n?', '', body, flags=re.M)
        # Trim the trailing `end <namespace>` that closes the file.
        body = re.sub(r'\n?end\s+\w+\s*$', '', body)
        segs.append((cur[0], cur[1], body.strip("\n")))
    return segs


def complexity_of(instruction: str):
    if "must be O(1)" in instruction:
        return "O(1) required"
    if "No hard complexity bound" in instruction:
        return "No hard bound"
    return None


# --- Minimal Markdown (enough for INSTRUCTION.md / agent notes) --------------

def md(text: str) -> str:
    out, lines, i = [], text.splitlines(), 0
    list_open = False

    def close_list():
        nonlocal list_open
        if list_open:
            out.append("</ul>")
            list_open = False

    def inline(s):
        s = esc(s)
        s = re.sub(r'`([^`]+)`', r'<code>\1</code>', s)
        s = re.sub(r'\*\*([^*]+)\*\*', r'<strong>\1</strong>', s)
        return s

    while i < len(lines):
        ln = lines[i]
        if ln.strip().startswith("```"):
            close_list()
            i += 1
            buf = []
            while i < len(lines) and not lines[i].strip().startswith("```"):
                buf.append(esc(lines[i]))
                i += 1
            i += 1
            out.append("<pre class=code>" + "\n".join(buf) + "</pre>")
            continue
        m = re.match(r'^(#{1,4})\s+(.*)', ln)
        if m:
            close_list()
            lvl = len(m.group(1))
            out.append(f"<h{lvl}>{inline(m.group(2))}</h{lvl}>")
            i += 1
            continue
        m = re.match(r'^\s*[-*]\s+(.*)', ln)
        if m:
            if not list_open:
                out.append("<ul>")
                list_open = True
            out.append(f"<li>{inline(m.group(1))}</li>")
            i += 1
            continue
        if not ln.strip():
            close_list()
            i += 1
            continue
        if ln.strip().startswith(">"):
            close_list()
            out.append(f"<blockquote>{inline(ln.strip().lstrip('>').strip())}</blockquote>")
            i += 1
            continue
        close_list()
        out.append(f"<p>{inline(ln.strip())}</p>")
        i += 1
    close_list()
    return "\n".join(out)


# --- Solutions ---------------------------------------------------------------

def find_solution(task_name: str):
    """Locate a published solution dir for a task, or None."""
    if not SOLVED_DIR.exists():
        return None
    for d in SOLVED_DIR.iterdir():
        if not d.is_dir():
            continue
        if d.name == task_name or task_name.endswith("_" + d.name):
            return d
    return None


def solution_meta(sol_dir: Path, task_name: str):
    meta = {"agent": "Claude Code", "model": PUBLISHED_MODEL.get(task_name),
            "turns": None, "elapsed_min": None, "status": "PASS"}
    r = sol_dir / "result.json"
    if r.exists():
        try:
            d = json.loads(read(r) or "{}")
            if d.get("status"):
                meta["status"] = d["status"]
            if d.get("elapsed_s"):
                meta["elapsed_min"] = round(d["elapsed_s"] / 60, 1)
        except json.JSONDecodeError:
            pass
    m = sol_dir / "logs" / "meta.json"
    if m.exists():
        try:
            d = json.loads(read(m) or "{}")
            meta["model"] = d.get("model") or meta["model"]
            meta["turns"] = d.get("num_turns")
        except json.JSONDecodeError:
            pass
    return meta


# --- Run records -------------------------------------------------------------

# What a solver spends its calls on, in the order of the loop it runs: look
# around, edit Task.lean, compile, submit to check.sh. Hues are slots 1-4 of
# the validated categorical palette; every one is also named in the legend.
TRAJ_CATS = [("explore", "Explore", "#2a78d6"),
             ("edit", "Edit", "#eb6834"),
             ("compile", "Compile", "#1baf7a"),
             ("check", "Check", "#eda100")]

# Outcomes: the green the site already uses for PASS, with every kind of
# non-solve muted so the eye reads "how much is solved" first. A pass the
# LLM review rejected is a non-solve too, tinted so it does not read as a
# plain failure; an error is the harness or provider failing, not the model.
OUTCOMES = [("PASS", "Solved", "#1f7a37"),
            ("REJECTED", "Rejected in review", "#d6a443"),
            ("FAIL", "Failed", "#8a8f98"),
            ("TIMEOUT", "Timed out", "#c9ccd1"),
            ("ERROR", "Error", "#e2b0b0")]
OUTCOME_LABEL = {k: lbl for k, lbl, _ in OUTCOMES}
DASH = "\u2014"
OUTCOME_COLOR = {k: c for k, _, c in OUTCOMES}


# A run needs at least this many tasks before its own charts say anything.
MIN_CHART_TASKS = 10


def outcome(rec):
    """How one run on one task scores: check.sh's verdict, except that a pass
    the blind LLM review rejected does not count as solved."""
    status = rec.get("status", "UNKNOWN")
    if status == "PASS" and rec.get("review") == "REJECT":
        return "REJECTED"
    return status


def outcome_pill(rec):
    out = outcome(rec)
    if out == "REJECTED":
        return ('<span class="status rejected" title="Passed check.sh; '
                'rejected by the blind LLM review">Rejected</span>')
    cls = "solved" if out == "PASS" else "open"
    return (f'<span class="status {cls}">'
            f'{esc(OUTCOME_LABEL.get(out, out))}</span>')


def cost_rate(recs):
    """Highest cost per second the run reached on the tasks it did price."""
    return max((r["cost_usd"] / r["elapsed_s"] for r in recs
                if r.get("cost_usd") and r.get("elapsed_s")), default=0.0)


def cost_bound(rec, rate):
    """Cost of one run: what it recorded, or an upper bound when it was
    killed before writing a final record. None when neither is available."""
    if rec.get("cost_usd"):
        return rec["cost_usd"], False
    if rate and rec.get("elapsed_s"):
        return rec["elapsed_s"] * rate, True
    return None, False


def run_stats(recs):
    """Headline numbers for one run.

    Cost is reported as a range. A run killed at the wall-clock cap writes no
    final record, so its cost is unknown; leaving it out would understate the
    price of the run, and the suite's longest runs are exactly the ones that
    get killed. Each is therefore bounded by its own wall clock at the highest
    cost rate that same run reached, and the total is given as a bound.
    """
    outs = [outcome(r) for r in recs]
    solved = [r for r, o in zip(recs, outs) if o == "PASS"]
    priced = [r for r in recs if r.get("cost_usd")]
    rate = cost_rate(recs)
    recorded = sum(r["cost_usd"] for r in priced)
    bounded = sum(cost_bound(r, rate)[0] or 0 for r in recs)
    times = [r["elapsed_s"] for r in solved if r.get("elapsed_s")]
    costs = [r["cost_usd"] for r in solved if r.get("cost_usd")]
    return {
        "n": len(recs), "solved": len(solved),
        "rate": round(100 * len(solved) / len(recs)) if recs else 0,
        "checked": sum(1 for r in recs if r.get("status") == "PASS"),
        **{k.lower(): outs.count(k)
           for k in ("REJECTED", "FAIL", "TIMEOUT", "ERROR")},
        "avg_time": statistics.fmean(times) if times else 0,
        "avg_cost": statistics.fmean(costs) if costs else 0,
        "recorded": recorded, "bounded": bounded,
        # A harness that reports no cost at all (Codex CLI) is not the same
        # as runs killed before their final record: there is nothing to
        # bound, so its cost is "not reported", never $0.
        "reports_cost": bool(priced),
        "unpriced": len(recs) - len(priced), "cost_rate": rate,
    }


NOT_REPORTED = "not reported"


def fmt_run_cost(st):
    """A run's total cost: recorded, bounded when some runs were killed, or
    not reported by the harness at all."""
    if not st["reports_cost"]:
        return NOT_REPORTED
    return ("\u2264 " + fmt_usd(st["bounded"])) if st["unpriced"] \
        else fmt_usd(st["recorded"])


def fmt_web(run, recs):
    """Web access as the run set it, and whether the agent used it anyway."""
    web = run.get("web_access")
    if web is True:
        return "On"
    if web == "mixed":
        return "Mixed"
    if web is None:
        return "Not recorded"
    used = [r for r in recs if r.get("web_calls")]
    if not used:
        return "Off"
    calls = sum(r["web_calls"] for r in used)
    return (f"Off, but used in {spell(len(used))} "
            f"task{'s' if len(used) > 1 else ''} ({calls} "
            f"call{'s' if calls > 1 else ''})")


def fmt_review(run, runs):
    review = run.get("review")
    if not review:
        return "Not run"
    judge = review.get("judge")
    return f"Blind, by {model_label(judge, runs)}" if judge else "Blind"


def model_label(model, runs):
    """Display name for a model id, taken from whichever run used it."""
    for r in runs:
        if r.get("model") == model and r.get("label"):
            return r["label"]
    return model or "an agent"


def load_runs():
    """Run summaries from runs/ (scripts/collect_runs.py), newest first."""
    runs = []
    if not RUNS_DIR.exists():
        return runs
    for f in sorted(RUNS_DIR.glob("*.json")):
        try:
            r = json.loads(read(f) or "{}")
        except json.JSONDecodeError:
            continue
        if r.get("tasks"):
            recs = list(r["tasks"].values())
            r["rate"] = cost_rate(recs)
            r["reports_cost"] = (any(t.get("cost_usd") for t in recs)
                                 or bool((r.get("summary") or {}).get("cost_usd")))
            runs.append(r)
    runs.sort(key=lambda r: r.get("date") or "", reverse=True)
    return runs


def runs_for(name: str, runs):
    """Every (run, record) pair covering this task. Published solution dirs
    carry the short name (TnumStepUp), task dirs the full one."""
    out = []
    for r in runs:
        for key, rec in (r.get("tasks") or {}).items():
            if key == name or name.endswith("_" + key):
                out.append((r, rec))
    return out


def fmt_dur(sec):
    if not sec:
        return DASH
    if sec < 5400:
        return f"{sec / 60:.0f} min"
    return f"{sec / 3600:.1f}".rstrip("0").rstrip(".") + " h"


def fmt_usd(v):
    return f"${v:,.2f}" if v else DASH


def fmt_usd0(v):
    """Whole dollars: large sums do not need cents, and fit in a tile."""
    return f"${v:,.0f}" if v else DASH


_WORDS = ("zero", "one", "two", "three", "four", "five", "six", "seven",
          "eight", "nine")


def spell(n):
    """Small counts read better spelled out in a sentence."""
    return _WORDS[n] if 0 <= n < len(_WORDS) else str(n)


def fmt_count(n):
    if n is None:
        return DASH
    if not n:
        return "0"
    if n >= 1_000_000:
        return f"{n / 1_000_000:.1f}M"
    return f"{n / 1000:.0f}k" if n >= 1000 else str(n)


def fmt_date(d):
    if not d:
        return ""
    try:
        return datetime.strptime(d, "%Y-%m-%d").strftime("%d %b %Y").lstrip("0")
    except ValueError:
        return d


def fmt_span(run):
    """A run's dates: a single day, or the span it actually covered."""
    start, end = fmt_date(run.get("date")), fmt_date(run.get("date_end"))
    return f"{start} \u2013 {end}" if end and end != start else start


def traj_svg(rec):
    """Activity profile: one stacked column per time bucket of the run."""
    traj = rec.get("traj")
    if not traj or not traj.get("n"):
        return ""
    n = traj["n"]
    series = [(key, lbl, color, traj.get(key) or [0] * n)
              for key, lbl, color in TRAJ_CATS]
    peak = max((sum(s[3][i] for s in series) for i in range(n)), default=0)
    if not peak:
        return ""

    W, H, PAD = 720, 84, 4        # columns sit on a baseline at H - 18
    base, top = H - 18, 8
    colw = W / n
    bars = []
    for i in range(n):
        total = sum(s[3][i] for s in series)
        if not total:
            continue
        y = base
        for key, lbl, color, vals in series:
            if not vals[i]:
                continue
            h = vals[i] / peak * (base - top)
            # A 2px gap in the surface colour separates stacked segments.
            seg = max(h - 2, 1.5)
            y -= h
            bars.append(
                f'<rect x="{i * colw + 0.6:.1f}" y="{y + (h - seg):.1f}" '
                f'width="{colw - 1.2:.1f}" height="{seg:.1f}" rx="1.5" '
                f'fill="{color}"><title>{esc(lbl)}: {vals[i]}</title></rect>')
    by_time = traj.get("by", "time") == "time"
    end = (fmt_dur(traj.get("span_s") or rec.get("elapsed_s")) if by_time
           else f'{rec.get("tool_calls") or ""} tool calls')
    legend = "".join(
        f'<span class=key><i style="background:{color}"></i>{esc(lbl)} '
        f'{sum(vals)}</span>'
        for key, lbl, color, vals in series if sum(vals))
    return f"""
<div class=traj>
  <svg viewBox="0 0 {W} {H}" role="img"
       aria-label="Tool calls over the run, by activity">
    <line x1="0" y1="{base}" x2="{W}" y2="{base}" stroke="#e6e6e6"/>
    {''.join(bars)}
    <text x="0" y="{H - 4}" font-size="10.5" fill="#888">start</text>
    <text x="{W}" y="{H - 4}" font-size="10.5" fill="#888"
          text-anchor="end">{esc(end)}</text>
  </svg>
  <div class=legend>{legend}</div>
</div>
"""


def run_card(run, rec, published):
    """One agent run on one task: what it cost and how it was spent."""
    out = outcome(rec)
    reports_cost = run.get("reports_cost", True)
    tools = rec.get("tools") or {}
    tokens = rec.get("tokens")
    cost, est = cost_bound(rec, run.get("rate", 0))
    stats = [("Wall clock", fmt_dur(rec.get("elapsed_s"))),
             ("Cost", (("\u2264 " + fmt_usd(cost)) if est else fmt_usd(cost))
              if reports_cost else NOT_REPORTED),
             ("Turns", str(rec.get("turns") or DASH)),
             ("Tool calls", str(rec.get("tool_calls") or DASH)),
             ("Compiles", str(tools.get("compile", 0) if tools else DASH)),
             ("check.sh runs", str(tools.get("check", 0) if tools else DASH)),
             ("Output tokens", fmt_count(tokens["out"] if tokens else None))]
    tiles = "".join(f'<div class=runstat><div class=rs-num>{esc(v)}</div>'
                    f'<div class=rs-label>{esc(k)}</div></div>'
                    for k, v in stats)
    notes = []
    if out == "PASS" and not published:
        notes.append('The solution passed every gate; it is under review and '
                     'not published yet.')
    elif out == "REJECTED":
        why = " and ".join({"complexity": "the task's complexity rule",
                            "faithful": "satisfying check.sh instead of the "
                                        "specification"}.get(f, f)
                           for f in rec.get("review_flags") or [])
        notes.append('The solution passed <code>check.sh</code>, but the blind '
                     'LLM review rejected it'
                     + (f' on {esc(why)}' if why else '')
                     + ', so it does not count as solved.')
    elif out == "TIMEOUT":
        notes.append(f'Killed at the {fmt_dur(run.get("limit_s"))} cap. A '
                     f'killed run writes no final record, so its turns and '
                     f'token totals are unknown'
                     + (' and its cost is an upper bound: this much wall '
                        'clock at the highest rate the run reached elsewhere'
                        if reports_cost else '')
                     + '. The tool calls below are exact.')
    elif out == "ERROR":
        notes.append('The run failed for a reason outside the agent (the '
                     'harness or the model provider), before it could be '
                     'scored.')
    if not reports_cost:
        notes.append(f'{esc(run.get("agent") or "This harness")} reports '
                     f'token counts but neither cost nor turns.')
    if rec.get("web_calls") and run.get("web_access") is False:
        notes.append(f'Web access was meant to be off, but the agent made '
                     f'{rec["web_calls"]} web call'
                     f'{"s" if rec["web_calls"] > 1 else ""} in this run.')
    note = "".join(f'<p class=runnote>{n}</p>' for n in notes)
    meta = " \u00b7 ".join(x for x in (run.get("agent"), fmt_span(run))
                          if x)
    return f"""
<div class=runcard>
  <div class=runhead>
    <strong>{esc(run.get("label") or run.get("model") or "Agent")}</strong>
    <span class=runmeta>{esc(meta)}</span>
    {outcome_pill(rec)}
  </div>
  <div class=runstats>{tiles}</div>
  {traj_svg(rec)}
  {note}
</div>
"""


# --- Page rendering ----------------------------------------------------------

# Pages this build produced; the nav lists only what exists (a checkout
# without run data has no results page).
PAGES = {"about", "problems"}


def page(title, body, depth, repo_url, active="", landing=False):
    """Wrap body in the shared shell. `depth` = path depth for relative links.
    `landing` switches <main> to the roomier rhythm the front page uses."""
    root = "../" * depth
    def nav(href, label, key):
        if key not in PAGES:
            return ""
        cls = ' class="active"' if key == active else ""
        return f'<a href="{root}{href}"{cls}>{label}</a>'
    repo_link = (f'<a href="{repo_url}" class=ext>GitHub</a>' if repo_url else "")
    return f"""<!doctype html>
<html lang=en>
<head>
<meta charset=utf-8>
<meta name=viewport content="width=device-width, initial-scale=1">
<title>{esc(title)}</title>
<link rel=stylesheet href="{root}assets/style.css">
</head>
<body>
<header class=topbar>
  <a href="{root}index.html" class=brand>Vero</a>
  <nav>
    {nav('index.html', 'About', 'about')}
    {nav('problems.html', 'Problems', 'problems')}
    {nav('results.html', 'Results', 'results')}
    {repo_link}
  </nav>
</header>
<main class="{'landing' if landing else ''}">
{body}
</main>
<footer>
  <span>Vero benchmark for verified code generation.</span>
</footer>
<script src="{root}assets/app.js"></script>
</body>
</html>
"""


def badge(text, kind):
    return f'<span class="badge {kind}">{esc(text)}</span>'


STATUS_LABEL = {"published": "Published", "solved": "Solved", "open": "Open"}


def status_pill(status):
    return (f'<span class="status {status}">'
            f'{STATUS_LABEL.get(status, status)}</span>')


def render_index(tasks, runs, repo_url):
    solved = sum(1 for t in tasks if t["status"] != "open")
    published = sum(1 for t in tasks if t["status"] == "published")
    by_area = {}
    for t in tasks:
        by_area.setdefault(t["area"], 0)
        by_area[t["area"]] += 1
    area_line = ", ".join(f"{by_area[a]} {a}" for a in ("eBPF", "LLVM", "seL4") if a in by_area)

    rows = []
    for t in tasks:
        keywords = " ".join([t["name"], t["title"], t["area"], t["group"]]).lower()
        rows.append(
            f'<tr data-k="{esc(keywords)}" data-area="{t["area"]}" '
            f'data-status="{t["status"]}" '
            f'onclick="location=\'problems/{t["name"]}.html\'">'
            f'<td class=num>{t["id"]:03d}</td>'
            f'<td class=ttl><a href="problems/{t["name"]}.html">{esc(t["title"])}</a></td>'
            f'<td>{badge(t["area"], "area-" + t["area"])}</td>'
            f'<td class=grp>{esc(t["group"])}</td>'
            f'<td>{status_pill(t["status"])}</td></tr>')

    intro = f"""
<section class=hero>
  <h1>Verified code generation on real-world systems</h1>
  <p>A solver produces an implementation together with a Lean 4 proof that it
  meets a machine-checked specification. The {len(tasks)} problems come from
  three security- and correctness-critical systems: the Linux kernel eBPF
  verifier, LLVM, and the seL4 microkernel. Each specification encodes a new
  requirement with no existing implementation, so a correct solution improves
  the upstream system.</p>
  <p class=stat>{len(tasks)} problems ({esc(area_line)}). {solved} solved by at
  least one agent, {published} with the solution published.
  <a href="results.html">Run results and cost</a>.</p>
</section>
"""

    controls = """
<div class=controls>
  <input class=search type=search data-for=problems placeholder="Search problems" autocomplete=off>
  <div class=selects>
    <select data-for=problems data-attr=area aria-label="Filter by area">
      <option value=all>All areas</option>
      <option value=eBPF>eBPF</option>
      <option value=LLVM>LLVM</option>
      <option value=seL4>seL4</option>
    </select>
    <select data-for=problems data-attr=status aria-label="Filter by status">
      <option value=all>All status</option>
      <option value=solved>Solved</option>
      <option value=published>Published</option>
      <option value=open>Open</option>
    </select>
  </div>
</div>
"""

    table = f"""
<table class="problems filterable" id=problems>
<thead><tr><th>#</th><th>Title</th><th>Area</th><th>Group</th><th>Status</th></tr></thead>
<tbody>
{''.join(rows)}
</tbody>
</table>
<p class=empty data-for=problems hidden>No problems match.</p>
"""
    return page("Vero: Problems", intro + controls + table, 0, repo_url, "problems")


# How a task works: provided vs editable sections, then the check gates.
ANATOMY_SVG = """
<svg viewBox="0 0 860 150" role="img" aria-label="Task anatomy">
  <defs><marker id="arr" markerWidth="8" markerHeight="8" refX="6" refY="3"
    orient="auto"><path d="M0,0 L6,3 L0,6 z" fill="#888"/></marker></defs>
  <rect x="8" y="8" width="330" height="134" rx="8" fill="#fff" stroke="#ddd"/>
  <text x="24" y="32" font-size="14" font-weight="700" fill="#111">Task.lean</text>
  <rect x="24" y="44" width="298" height="40" rx="6" fill="#eef4ff" stroke="#cddffb"/>
  <text x="36" y="61" font-size="11.5" font-weight="600" fill="#1a4fa0">Provided (hash-locked)</text>
  <text x="36" y="76" font-size="11.5" fill="#334">DEFINITIONS &#183; SPEC &#183; THEOREM</text>
  <rect x="24" y="92" width="298" height="40" rx="6" fill="#fffaf0" stroke="#f0dfb5"/>
  <text x="36" y="109" font-size="11.5" font-weight="600" fill="#8a6d1a">Editable (your workspace)</text>
  <text x="36" y="124" font-size="11.5" fill="#334">IMPLEMENTATION &#183; AUX &#183; PROOF</text>
  <line x1="344" y1="75" x2="392" y2="75" stroke="#888" stroke-width="1.5" marker-end="url(#arr)"/>
  <rect x="398" y="30" width="300" height="90" rx="8" fill="#fff" stroke="#ddd"/>
  <text x="414" y="56" font-size="14" font-weight="700" fill="#111">check.sh &#8212; five gates</text>
  <text x="414" y="78" font-size="11.5" fill="#334">integrity &#183; no stubs &#183; no cheats</text>
  <text x="414" y="96" font-size="11.5" fill="#334">lake lean &#183; #print axioms</text>
  <line x1="704" y1="75" x2="752" y2="75" stroke="#888" stroke-width="1.5" marker-end="url(#arr)"/>
  <rect x="758" y="47" width="94" height="56" rx="8" fill="#eefaf0" stroke="#cbe9cf"/>
  <text x="805" y="72" font-size="15" font-weight="700" fill="#1f7a37" text-anchor="middle">PASS</text>
  <text x="805" y="90" font-size="10.5" fill="#1f7a37" text-anchor="middle">machine-checked</text>
</svg>
"""

# Example lines are HTML (static local content, already safe).
PRINCIPLES = [
    ("Real-world",
     "Every task comes from a production system, not a textbook exercise "
     "or a programming contest.",
     "The eBPF tasks are value-tracking operators of <strong>the kernel "
     "verifier</strong>, which analyzes every BPF program before it runs."),
    ("New specification",
     "Each task encodes a requirement the upstream implementation does not "
     "yet meet, distilled from upstream experience and community needs.",
     "The eBPF tasks require operators that are <strong>provably sound and "
     "optimal</strong>, a bar the verifier's current operators miss."),
    ("Valuable to solve",
     "A correct solution is an upstream contribution, not just a benchmark "
     "score: the specifications encode changes the projects want and do not "
     "yet have.",
     "The tnum_step() solution is <strong>merged into</strong> the Linux "
     "kernel."),
]

AREA_CARDS = [
    ("eBPF", "ebpf.png",
     "Sound and optimal abstract operators for the Linux kernel eBPF "
     "verifier, over the cnum and interval domains."),
    ("LLVM", "llvm.png",
     "Optimal KnownBits and DemandedBits transfer functions: the bit-level "
     "analyses the optimizer relies on."),
    ("seL4", "seL4.png",
     "Verified optimizations of seL4 microkernel routines, specified "
     "against the kernel's data-structure invariants."),
]

# (task name, display name, area, model, highlight)
PUBLISHED = [
    ("eBPF_TnumStepUp", "tnum_step()", "eBPF", "claude-opus-4-6",
     "Provably sound and optimal; merged into the Linux kernel"),
    ("LLVM_KBUmax", "KnownBits umax", "LLVM", "claude-opus-4-6",
     "Optimal transfer function for unsigned maximum"),
    ("seL4_CteRevoke", "cteRevoke", "seL4", "claude-opus-4-6",
     "Verified revocation over the capability derivation tree"),
]
PUBLISHED_MODEL = {name: model for name, _, _, model, _ in PUBLISHED}


# --- Syntax highlighting (build time, no JS) ---------------------------------

_HL_RULES = {
    "lean": [
        ("c", r"--[^\n]*|/-.*?-/"),
        ("s", r'"(?:[^"\\]|\\.)*"'),
        ("k", r"\b(def|theorem|let|by|intro|refine|unfold|simp|only|fun|"
              r"if|then|else|match|with)\b|\bbv_decide\b|·|∀|∧|→"),
        ("t", r"\b(BitVec|Prop|Bool|Nat)\b"),
        ("n", r"\b\d+\b"),
    ],
    "c": [
        ("c", r"//[^\n]*|/\*.*?\*/"),
        ("s", r'"(?:[^"\\]|\\.)*"|<[a-z_/.]+\.h>'),
        ("k", r"\b(if|else|return|struct|static|const|unsigned|long)\b|"
              r"\b(u64|s64|u32|s32)\b|#include\b"),
        ("n", r"\b(0[xX][0-9a-fA-F]+|\d+ULL|\d+)\b"),
    ],
}


def hl(code: str, lang: str) -> str:
    """Escape `code` and wrap tokens in <span class=tok-*> per _HL_RULES."""
    master = re.compile(
        "|".join(f"(?P<{n}>{p})" for n, p in _HL_RULES[lang]), re.S)
    out, pos = [], 0
    for m in master.finditer(code):
        out.append(esc(code[pos:m.start()]))
        out.append(f'<span class=tok-{m.lastgroup}>{esc(m.group(0))}</span>')
        pos = m.end()
    out.append(esc(code[pos:]))
    return "".join(out)


def merged_lean() -> str:
    """Specification, algorithm, and proof of the kernel-merged solution,
    reassembled from the published Task.lean."""
    secs = {s: b for s, _, b in
            sections_of(read(SOLVED_DIR / "TnumStepUp" / "Task.lean"))}
    return (
        "def tnumStepUp (tval tmask z : BitVec 64) : BitVec 64 :=\n"
        + secs.get("IMPLEMENTATION", "").strip("\n") + "\n\n"
        + secs.get("SPEC", "").strip("\n") + "\n"
        + secs.get("PROOF", "").strip("\n"))


def merged_c() -> str:
    """The C form of the solution, from the doc comment onward."""
    src = read(SOLVED_DIR / "TnumStepUp" / "tnum_step_c" / "tnum_step_up.c")
    i = src.find("/*")
    return src[i:].strip("\n") if i != -1 else src.strip("\n")


def render_about(tasks, runs, repo_url):
    by_area = {}
    for t in tasks:
        by_area[t["area"]] = by_area.get(t["area"], 0) + 1

    solved = sum(1 for t in tasks if t["status"] != "open")
    published = sum(1 for t in tasks if t["status"] == "published")

    # Counted tiles link into the board they summarize.
    stats = "".join(
        (f'<a class=stat-tile href="{href}">' if href else '<div class=stat-tile>')
        + f'<div class=stat-num>{esc(num)}</div>'
          f'<div class=stat-label>{esc(label)}</div>'
        + ("</a>" if href else "</div>")
        for num, label, href in [
            (str(len(tasks)), "tasks", "problems.html"),
            (str(len(by_area)), "real systems", ""),
            (str(solved), "solved by an agent", "problems.html?status=solved"),
            (str(published), "solutions published", "problems.html?status=published"),
        ])

    principle_cards = "".join(
        f'<div class=card><div class=kicker>{i:02d}</div>'
        f'<h3>{esc(title)}</h3><p>{esc(sent)}</p>'
        f'<p class=ex>{ex}</p></div>'
        for i, (title, sent, ex) in enumerate(PRINCIPLES, 1))

    area_cards = "".join(
        f'<a class="card alink areacard" href="problems.html?area={name}">'
        f'<div class=arealogo>'
        f'<img src="assets/logos/{logo}" alt="{esc(name)} logo"></div>'
        f'<p>{esc(desc)}</p>'
        f'<p class=browse><span class=areacount>{by_area.get(name, 0)} tasks</span>'
        f'<span class=go>Browse &rarr;</span></p></a>'
        for name, logo, desc in AREA_CARDS)

    published_rows = "".join(
        f'<tr><td class=ttl><a href="problems/{d}.html">{esc(n)}</a></td>'
        f'<td>{badge(a, "area-" + a)}</td>'
        f'<td>{esc(model_label(m, runs))}</td><td>{esc(h)}</td></tr>'
        for d, n, a, m, h in PUBLISHED)

    # Every model with a per-task breakdown, side by side; the results page
    # holds the conditions each ran under and the paper's totals-only run.
    run_line = ""
    full = [r for r in runs
            if sum(1 for t in tasks for run, _ in t["runs"]
                   if run["id"] == r["id"]) >= MIN_CHART_TASKS]
    if full:
        rows = ""
        for r in full:
            recs = [rec for t in tasks for run, rec in t["runs"]
                    if run["id"] == r["id"]]
            st = run_stats(recs)
            rows += (
                f'<tr><td class=ttl>{esc(r.get("label") or r.get("model"))}</td>'
                f'<td>{esc(r.get("agent") or DASH)}</td>'
                f'<td>{esc(fmt_span(r))}</td>'
                f'<td>{esc(fmt_web(r, recs))}</td>'
                f'<td>{esc(fmt_review(r, runs))}</td>'
                f'<td class=numv><strong>{st["solved"]}</strong> of {st["n"]} '
                f'({st["rate"]}%)</td>'
                f'<td class=numv>{esc(fmt_dur(st["avg_time"]))}</td></tr>')
        run_line = (
            f'<p class=sublede>Each model gets one attempt per task under a '
            f'{esc(fmt_dur(full[0].get("limit_s")))} cap, with no human help. '
            f'A task counts as solved when <code>check.sh</code> passes and, '
            f'in a reviewed run, the blind LLM review does not reject the '
            f'solution.</p>'
            f'<div class=tablewrap><table class=results>'
            f'<thead><tr><th>Model</th><th>Agent</th><th>Dates</th>'
            f'<th>Web access</th><th>LLM review</th><th>Solved</th>'
            f'<th>Average time per solve</th></tr></thead>'
            f'<tbody>{rows}</tbody></table></div>'
            f'<p class=cta><a class="btn primary" href="results.html">'
            f'Full results, conditions and cost</a>'
            f'<a class=btn href="problems.html?status=solved">'
            f'Solved tasks</a></p>')

    body = f"""
<section class=hero>
  <p class=eyebrow>The Vero benchmark</p>
  <h1>Verified code generation on real systems</h1>
  <p class=lede>Given a formal specification, a coding agent must produce an
  implementation <em>and</em> a Lean 4 proof that the implementation satisfies
  it. The proof checker decides correctness, so reviewing a solution reduces to
  reading a concise specification.</p>
  <p class=cta>
    <a class="btn primary" href="problems.html">Browse the problems</a>
    <a class="btn" href="results.html">See the results</a>
  </p>
  <div class=stats>{stats}</div>
</section>

<section>
  <p class=eyebrow>Anatomy</p>
  <h2>What a task looks like</h2>
  <p class=sublede>Each task is a single Lean file, split into sections the
  solver may edit and sections it may not, plus the checker that decides the
  outcome.</p>
  <div class=figure>{ANATOMY_SVG}</div>
</section>

<section>
  <p class=eyebrow>Principles</p>
  <h2>What makes a Vero task</h2>
  <div class=cards>{principle_cards}</div>
</section>

<section>
  <p class=eyebrow>Coverage</p>
  <h2>Three systems, {len(tasks)} tasks</h2>
  <div class=cards>{area_cards}</div>
</section>

<section>
  <p class=eyebrow>Results</p>
  <h2>How agents do</h2>
  {run_line}
  <h3>Published solutions</h3>
  <p class=sublede>{published} solutions are published in full, one per area.
  The rest of the solved tasks are under review; each is released once it has
  been read and checked.</p>
  <div class=tablewrap>
  <table class=results>
  <thead><tr><th>Solution</th><th>Area</th><th>Model</th><th>Highlight</th></tr></thead>
  <tbody>{published_rows}</tbody>
  </table>
  </div>
</section>

<section>
  <p class=eyebrow>Upstream</p>
  <h2>In the Linux kernel</h2>
  <p class=sublede>The agent-written <code>tnum_step()</code> is
  <a href="{KERNEL_COMMIT_URL}">merged into the Linux kernel</a>, and it is
  provably correct: the Lean 4 proof machine-checks the soundness and
  optimality of the exact algorithm the C code implements.</p>
  <div class=duo>
    <div class=panel>
      <div class=phead>Lean 4 <span class=ptag>algorithm, spec, proof</span></div>
      <pre class=code>{hl(merged_lean(), "lean")}</pre>
      <div class=pfoot>Five obligations, each closed by a machine-checked proof.</div>
    </div>
    <div class=panel>
      <div class=phead>C <span class=ptag>kernel/bpf/tnum.c</span></div>
      <pre class=code>{hl(merged_c(), "c")}</pre>
      <div class=pfoot><a href="{KERNEL_COMMIT_URL}">bpf-next commit 833ef4a954e1</a></div>
    </div>
  </div>
</section>

<section class=closing>
  <div class=cards>
    <div class=card>
      <h3>Borrow a problem</h3>
      <p>Every problem page bundles its specification, instruction, and Lake
      project files for download. Start from the editable sections.</p>
      <p class=browse><a class=arrow href="problems.html">Open the board</a></p>
    </div>
    <div class=card>
      <h3>Contribute</h3>
      <p>A new task from a real system, a sharper specification, or a solution
      to an open problem &mdash; all welcome.</p>
      <p class=browse><a class=arrow href="{repo_url}">The repository</a></p>
    </div>
    <div class=card>
      <h3>Authors</h3>
      <ul class=authors>
        <li>{badge("eBPF", "area-eBPF")} Hao Sun</li>
        <li>{badge("LLVM", "area-LLVM")} Cong Li</li>
        <li>{badge("seL4", "area-seL4")} Zenan Li</li>
      </ul>
    </div>
  </div>
  <p class=trademark>The eBPF, LLVM, and seL4 logos identify the upstream
  projects and are trademarks of their respective owners.</p>
</section>
"""
    return page("Vero: About", body, 0, repo_url, "about", landing=True)


def outcome_bars(rows, uid=""):
    """Solved / failed / timed out per task group, as stacked bars.

    `rows` is [(area, group, {outcome: count}, total)], longest bar = widest
    group, so the bars carry suite composition as well as the solve rate.
    `uid` keeps the clip-path ids unique when one page holds several charts.
    """
    if not rows:
        return ""
    W, LAB, RIGHT = 720, 132, 72
    span = W - LAB - RIGHT
    rowh, barh = 26, 15
    widest = max(r[3] for r in rows) or 1
    out, y = [], 6
    for area, group, counts, total in rows:
        width = span * total / widest
        clip = re.sub(r"\W", "", f"clip{uid}{area}{group}")
        segs, x = [], 0.0
        for key, label, color in OUTCOMES:
            n = counts.get(key, 0)
            if not n:
                continue
            w = width * n / total
            segs.append(
                f'<rect x="{LAB + x:.1f}" y="{y}" width="{w:.1f}" height="{barh}" '
                f'fill="{color}"><title>{esc(group)}: {n} {esc(label.lower())}'
                f'</title></rect>')
            x += w
        solved = counts.get("PASS", 0)
        out.append(f"""
  <clipPath id="{clip}"><path d="M{LAB},{y} H{LAB + width - 4:.1f}
    a4,4 0 0 1 4,4 V{y + barh - 4} a4,4 0 0 1 -4,4 H{LAB} Z"/></clipPath>
  <text x="{LAB - 10}" y="{y + 12}" font-size="11.5" fill="#333"
        text-anchor="end">{esc(group)}</text>
  <g clip-path="url(#{clip})">{''.join(segs)}</g>
  <text x="{LAB + width + 8:.1f}" y="{y + 12}" font-size="11.5" fill="#666">
    {solved}/{total}</text>""")
        y += rowh
    drawn = {k for _, _, counts, _ in rows for k, n in counts.items() if n}
    legend = "".join(f'<span class=key><i style="background:{c}"></i>{esc(l)}</span>'
                     for k, l, c in OUTCOMES if k in drawn)
    return f"""
<div class=chart>
  <svg viewBox="0 0 {W} {y + 4}" role="img"
       aria-label="Outcome by task group">{''.join(out)}
  </svg>
  <div class=legend>{legend}</div>
</div>
"""


def cost_scatter(points):
    """Cost against wall-clock time, one mark per run that recorded a cost.

    `points` is [(name, title, minutes, usd, outcome)]. Solved runs are
    filled marks, the rest hollow, so outcome never rides on colour alone.
    """
    if not points:
        return ""
    W, H = 720, 300
    L, R, T, B = 52, 14, 12, 34
    xmax = max(30, min(125, max(p[2] for p in points) * 1.06))
    ymax = max(5, max(p[3] for p in points) * 1.08)
    xs = lambda m: L + (W - L - R) * m / xmax
    ys = lambda v: H - B - (H - B - T) * v / ymax

    xticks = [t for t in (0, 30, 60, 90, 120) if t <= xmax]
    step = 5 if ymax <= 22 else 10
    yticks = [v for v in range(0, int(ymax) + step, step) if v <= ymax]
    grid = "".join(
        f'<line x1="{L}" y1="{ys(v):.1f}" x2="{W - R}" y2="{ys(v):.1f}" '
        f'stroke="#eee"/><text x="{L - 8}" y="{ys(v) + 4:.1f}" font-size="10.5" '
        f'fill="#888" text-anchor="end">${v}</text>' for v in yticks)
    grid += "".join(
        f'<text x="{xs(t):.1f}" y="{H - 12}" font-size="10.5" fill="#888" '
        f'text-anchor="middle">{t}</text>' for t in xticks)

    marks = []
    top = max(points, key=lambda p: p[3])
    for name, title, minutes, usd, status in points:
        cx, cy = xs(minutes), ys(usd)
        solved = status == "PASS"
        fill, stroke = (("#1f7a37", "#fff") if solved else ("#fff", "#8a8f98"))
        marks.append(
            f'<a href="problems/{name}.html"><circle cx="{cx:.1f}" cy="{cy:.1f}" '
            f'r="4.5" fill="{fill}" stroke="{stroke}" stroke-width="2">'
            f'<title>{esc(title)} \u2014 {minutes:.0f} min, {fmt_usd(usd)}, '
            f'{esc(OUTCOME_LABEL.get(status, status).lower())}</title>'
            f'</circle></a>')
    # Label the one extreme; the rest are carried by the axes and the table.
    marks.append(
        f'<text x="{xs(top[2]) - 9:.1f}" y="{ys(top[3]) + 4:.1f}" font-size="10.5" '
        f'fill="#444" text-anchor="end">{esc(top[1])} {fmt_usd(top[3])}</text>')
    legend = ('<span class=key><i class=dot style="background:#1f7a37"></i>Solved'
              '</span><span class=key><i class="dot hollow"></i>Not solved</span>')
    return f"""
<div class=chart>
  <svg viewBox="0 0 {W} {H}" role="img"
       aria-label="Cost against wall-clock time per run">
    {grid}
    <line x1="{L}" y1="{H - B}" x2="{W - R}" y2="{H - B}" stroke="#ddd"/>
    {''.join(marks)}
    <text x="{(L + W - R) / 2:.0f}" y="{H}" font-size="10.5" fill="#888"
          text-anchor="middle">minutes</text>
  </svg>
  <div class=legend>{legend}</div>
</div>
"""


def run_note_web(run, covered):
    """A sentence for a run that disabled the web yet reached it."""
    if run.get("web_access") is not False:
        return ""
    used = [(t, rec) for t, rec in covered if rec.get("web_calls")]
    if not used:
        return ""
    calls = sum(rec["web_calls"] for _, rec in used)
    solved = sum(1 for _, rec in used if outcome(rec) == "PASS")
    names = ", ".join(t["title"] for t, _ in used)
    if len(used) == 1:
        where = f'one task ({names}), which was {"" if solved else "not "}solved'
    else:
        where = f'{spell(len(used))} tasks ({names}), {spell(solved)} of them solved'
    return (f'{esc(run.get("label") or run.get("model"))} ran with web access '
            f'off, yet made {calls} web call{"s" if calls > 1 else ""} in '
            f'{esc(where)}.')


def render_results(tasks, runs, repo_url):
    """Every model side by side, then each run on its own: what it solved,
    what it cost, how it was spent."""
    if not runs:
        return None
    covered = {r["id"]: [(t, rec) for t in tasks for run, rec in t["runs"]
                         if run["id"] == r["id"]] for r in runs}
    stats = {r["id"]: run_stats([rec for _, rec in covered[r["id"]]])
             for r in runs}
    # A run published only as totals (e.g. the paper's evaluation) states how
    # many tasks it ran and what the whole run cost; its per-task records cover
    # just the tasks whose numbers were published individually, so the rest of
    # its outcome breakdown is unknown.
    for r in runs:
        summ = r.get("summary")
        if summ:
            st = stats[r["id"]]
            st["n"] = summ["n"]
            st["rate"] = round(100 * st["solved"] / summ["n"])
            st["recorded"] = st["bounded"] = summ["cost_usd"]
            st["unpriced"] = 0
            st["reports_cost"] = True
            st["totals_only"] = True
    charted = [r for r in runs if len(covered[r["id"]]) >= MIN_CHART_TASKS]
    label = {r["id"]: r.get("label") or r.get("model") for r in runs}

    # The side-by-side tables are the comparison: same tasks, same cap, same
    # accounting for every model, and the conditions that differ in plain
    # view. Runs are only comparable when they cover the same tasks, which
    # the "partial" tag flags.
    any_error = any(st["error"] for st in stats.values())
    out_rows = setup_rows = ""
    for r in runs:
        st = stats[r["id"]]
        # A run over a handful of tasks has a solve rate, but not one that
        # means anything next to a full-suite run; say so instead of printing
        # a percentage that invites the comparison.
        partial = st["n"] < MIN_CHART_TASKS
        tag = ' <span class=badge>partial</span>' if partial else ""
        solved = (f'{st["solved"]} of {st["n"]}' if partial
                  else f'<strong>{st["solved"]}</strong> ({st["rate"]}%)')
        part = (lambda k: DASH) if st.get("totals_only") else \
            (lambda k: str(st[k]))
        reviewed = bool(r.get("review"))
        out_rows += (
            f'<tr><td class=ttl>{esc(label[r["id"]])}{tag}</td>'
            f'<td class=numv>{st["n"]}</td>'
            f'<td class=numv>{solved}</td>'
            f'<td class=numv>{part("checked")}</td>'
            f'<td class=numv>{part("rejected") if reviewed else DASH}</td>'
            f'<td class=numv>{part("fail")}</td>'
            f'<td class=numv>{part("timeout")}</td>'
            + (f'<td class=numv>{part("error")}</td>' if any_error else "")
            + '</tr>')
        setup_rows += (
            f'<tr><td class=ttl>{esc(label[r["id"]])}</td>'
            f'<td>{esc(r.get("agent") or DASH)}</td>'
            f'<td>{esc(fmt_span(r))}</td>'
            f'<td>{esc(fmt_web(r, [rec for _, rec in covered[r["id"]]]))}</td>'
            f'<td>{esc(fmt_review(r, runs))}</td>'
            f'<td class=numv>{r.get("parallel") or DASH}</td>'
            f'<td class=numv>{esc(fmt_dur(st["avg_time"]))}</td>'
            f'<td class=numv>{esc(fmt_usd(st["avg_cost"]) if st["reports_cost"] else NOT_REPORTED)}</td>'
            f'<td class=numv>{esc(fmt_run_cost(st))}</td></tr>')

    partial_hint = (" Runs marked <em>partial</em> covered only part of the "
                    "suite and are listed for provenance, not for comparison."
                    if any(st["n"] < MIN_CHART_TASKS for st in stats.values())
                    else "")
    totals_hint = (" A run published only as totals has no per-task "
                   "breakdown, so its other columns are empty."
                   if any(st.get("totals_only") for st in stats.values())
                   else "")
    judges = sorted({r["review"]["judge"] for r in runs
                     if (r.get("review") or {}).get("judge")})
    judge_hint = ""
    if judges:
        judge_hint = (
            f'<p class=hint>The LLM review is run by '
            f'{esc(", ".join(model_label(j, runs) for j in judges))}, the '
            f'same judge for every reviewed run. It sees only the submitted '
            f'<code>Task.lean</code> next to the files the task was issued '
            f'with &mdash; never the transcript, the agent, or the model '
            f'&mdash; and it can only take a pass away, for satisfying '
            f'<code>check.sh</code> instead of the specification or for '
            f'breaking the task\'s complexity rule. Runs without a review '
            f'count every <code>check.sh</code> pass as solved.</p>')
    web_notes = " ".join(n for n in (run_note_web(r, covered[r["id"]])
                                     for r in runs) if n)
    nocost = [label[r["id"]] for r in runs if not stats[r["id"]]["reports_cost"]]
    cost_hint = (
        '<p class=hint>Cost is what the harness reported for the run at API '
        'prices.'
        + (f' {esc(" and ".join(nocost))} ran under a harness that reports '
           f'token counts but no cost, so {"its cost is" if len(nocost) == 1 else "their cost is"} '
           f'given as not reported rather than estimated.' if nocost else '')
        + ' A run killed at the cap writes no final cost record. Dropping '
        'those would understate what a model spent, since the longest runs '
        'are the ones that get killed, so the run cost bounds each of them by '
        'its wall clock at the highest cost rate that same run reached. '
        'Average time and cost are over solved tasks; "tasks at once" is how '
        'many tasks shared the machine, which wall-clock time depends on.'
        + (f' {web_notes}' if web_notes else '') + '</p>')

    comparison = f"""
<h2>Side by side</h2>
<div class=tablewrap>
<table class=results>
<thead><tr><th>Model</th><th>Tasks</th><th>Solved</th><th>Passed check.sh</th>
<th>Rejected in review</th><th>Failed</th><th>Timed out</th>{'<th>Errors</th>' if any_error else ''}</tr></thead>
<tbody>{out_rows}</tbody>
</table>
</div>
<p class=hint>A task is solved when <code>check.sh</code> passes every gate and
the blind LLM review does not reject the solution.{partial_hint}{totals_hint}</p>
{judge_hint}
<h3>How each run was set up</h3>
<div class=tablewrap>
<table class=results>
<thead><tr><th>Model</th><th>Agent</th><th>Dates</th><th>Web access</th>
<th>LLM review</th><th>Tasks at once</th><th>Average time</th><th>Average cost</th>
<th>Run cost</th></tr></thead>
<tbody>{setup_rows}</tbody>
</table>
</div>
{cost_hint}
"""

    # Per group: how each model does on the same slice of the suite.
    group_rows = ""
    if charted:
        order = []
        for t in tasks:
            if (t["area"], t["group"]) not in order:
                order.append((t["area"], t["group"]))
        by_task = {r["id"]: {t["name"]: rec for t, rec in covered[r["id"]]}
                   for r in charted}
        for area, group in order + [("", "")]:
            names = [t["name"] for t in tasks
                     if not area or (t["area"], t["group"]) == (area, group)]
            cells = ""
            for r in charted:
                recs = [by_task[r["id"]][n] for n in names
                        if n in by_task[r["id"]]]
                won = sum(1 for rec in recs if outcome(rec) == "PASS")
                cells += (f'<td class=numv>{won} / {len(recs)}</td>' if recs
                          else f'<td class=numv>{DASH}</td>')
            head = (f'<td>{badge(area, "area-" + area)}</td>'
                    f'<td class=grp>{esc(group)}</td>' if area else
                    '<td class=ttl colspan=2>All tasks</td>')
            group_rows += (f'<tr{" class=total" if not area else ""}>{head}'
                           f'<td class=numv>{len(names)}</td>{cells}</tr>')
    by_group = f"""
<h2>By task group</h2>
<p class=hint>Tasks solved out of the tasks each model ran in the group.</p>
<div class=tablewrap>
<table class=results>
<thead><tr><th>Area</th><th>Group</th><th>Tasks</th>
{''.join(f'<th>{esc(label[r["id"]])}</th>' for r in charted)}</tr></thead>
<tbody>{group_rows}</tbody>
</table>
</div>
""" if charted else ""

    # Task by task: one row per task, one column per model.
    matrix_rows = []
    for t in tasks:
        recs = {run["id"]: rec for run, rec in t["runs"]}
        keywords = " ".join([t["name"], t["title"], t["area"],
                             t["group"]]).lower()
        cells = "".join(
            f'<td>{outcome_pill(recs[r["id"]])}</td>' if r["id"] in recs
            else f'<td class=hint>not run</td>' for r in charted)
        matrix_rows.append(
            f'<tr data-k="{esc(keywords)}" data-area="{t["area"]}" '
            f'onclick="location=\'problems/{t["name"]}.html\'">'
            f'<td class=num>{t["id"]:03d}</td>'
            f'<td class=ttl><a href="problems/{t["name"]}.html">{esc(t["title"])}</a></td>'
            f'<td>{badge(t["area"], "area-" + t["area"])}</td>'
            f'<td class=grp>{esc(t["group"])}</td>{cells}</tr>')
    matrix = f"""
<h2>Task by task</h2>
<p class=hint>Every task, with each model's outcome on it. Open a task for the
run cards and activity profiles.</p>
<div class=controls>
  <input class=search type=search data-for=matrix placeholder="Search tasks" autocomplete=off>
  <div class=selects>
    <select data-for=matrix data-attr=area aria-label="Filter by area">
      <option value=all>All areas</option>
      <option value=eBPF>eBPF</option>
      <option value=LLVM>LLVM</option>
      <option value=seL4>seL4</option>
    </select>
  </div>
</div>
<div class=tablewrap>
<table class="problems filterable" id=matrix>
<thead><tr><th>#</th><th>Task</th><th>Area</th><th>Group</th>
{''.join(f'<th>{esc(label[r["id"]])}</th>' for r in charted)}</tr></thead>
<tbody>{''.join(matrix_rows)}</tbody>
</table>
</div>
<p class=empty data-for=matrix hidden>No tasks match.</p>
""" if charted else ""

    sections = []
    for run in charted:
        st = stats[run["id"]]
        rate = st["cost_rate"]
        tiles = "".join(
            f'<div class=stat-tile><div class=stat-num>{esc(num)}</div>'
            f'<div class=stat-label>{esc(lbl)}</div></div>'
            for num, lbl in [
                (f'{st["solved"]}/{st["n"]}', f'tasks solved ({st["rate"]}%)'),
                (fmt_dur(st["avg_time"]), "average time per solved task"),
                (fmt_usd(st["avg_cost"]) if st["reports_cost"] else DASH,
                 "average cost per solved task" if st["reports_cost"]
                 else "cost not reported"),
                ((f'\u2264 {fmt_usd0(st["bounded"])}' if st["unpriced"]
                  else fmt_usd0(st["recorded"])) if st["reports_cost"] else DASH,
                 ("upper bound on run cost" if st["unpriced"]
                  else "cost of the run") if st["reports_cost"]
                 else "run cost not reported"),
            ])

        order, groups = [], {}
        for t, rec in covered[run["id"]]:
            key = (t["area"], t["group"])
            if key not in groups:
                groups[key] = {}
                order.append(key)
            out = outcome(rec)
            groups[key][out] = groups[key].get(out, 0) + 1
        bars = outcome_bars([(a, g, groups[(a, g)], sum(groups[(a, g)].values()))
                             for a, g in order], uid=run["id"])
        points = [(t["name"], t["title"], rec["elapsed_s"] / 60, rec["cost_usd"],
                   outcome(rec)) for t, rec in covered[run["id"]]
                  if rec.get("cost_usd") and rec.get("elapsed_s")]
        killed = st["unpriced"]
        cost_note = ""
        if not st["reports_cost"]:
            cost_note = (f'<p class=hint>{esc(run.get("agent") or "The harness")} '
                         f'reports no cost, so there is no cost chart for '
                         f'this run.</p>')
        elif killed:
            cost_note = (
                f'<p class=hint>{killed} runs were killed at the '
                f'{esc(fmt_dur(run.get("limit_s")))} cap and write no cost '
                f'record, so they are not plotted. They are not free either: '
                f'the table below bounds each of them by its own wall clock at '
                f'the highest rate this run reached '
                f'({esc(fmt_usd(rate * 60))} per minute), which is where the '
                f'{esc(fmt_usd(st["bounded"]))} bound comes from.</p>')
        setup = [f'{esc(run.get("agent") or "")}, {esc(fmt_span(run))}.',
                 f'One attempt per task, no human help, '
                 f'{esc(fmt_dur(run.get("limit_s")))} of wall clock per task',
                 ]
        web = fmt_web(run, [rec for _, rec in covered[run["id"]]])
        setup[1] += f'; web access {esc(web[0].lower() + web[1:])}'
        if run.get("parallel"):
            setup[1] += (f'; {spell(run["parallel"])} task'
                         f'{"s" if run["parallel"] > 1 else ""} at a time')
        setup[1] += "."
        review = ("Every solution that passed <code>check.sh</code> went "
                  "through the blind LLM review."
                  if run.get("review") else
                  "This run was not LLM-reviewed.")
        sections.append(f"""
<h2>{esc(label[run["id"]])}</h2>
<p>{' '.join(setup)} {review} {st["n"]} of the {len(tasks)} tasks were run.</p>
<div class=stats>{tiles}</div>
<h3>Where it solves and where it stalls</h3>
<p class=hint>One bar per task group, as long as the group is large.</p>
{bars}
{'<h3>What a task costs</h3><p class=hint>Every run that recorded a cost, against the wall clock it took.</p>' if points else ''}
{cost_scatter(points)}
{cost_note}
""")

    # Per-task rows, every run in one table.
    multi = len(charted) > 1
    rows = []
    for run in charted or runs:
        rate = stats[run["id"]]["cost_rate"]
        reports_cost = stats[run["id"]]["reports_cost"]
        for t, rec in sorted(covered[run["id"]],
                             key=lambda tr: (outcome(tr[1]) != "PASS", tr[0]["id"])):
            tools = rec.get("tools") or {}
            out = outcome(rec)
            cost, est = cost_bound(rec, rate)
            cell = ((("\u2264 " + fmt_usd(cost)) if est else fmt_usd(cost))
                    if reports_cost else "n/r")
            tokens = rec.get("tokens")
            keywords = " ".join([t["name"], t["title"], t["area"], t["group"],
                                 label[run["id"]]]).lower()
            rows.append(
                f'<tr data-k="{esc(keywords)}" data-area="{t["area"]}" '
                f'data-status="{out}" data-model="{esc(run["id"])}" '
                f'onclick="location=\'problems/{t["name"]}.html\'">'
                f'<td class=ttl><a href="problems/{t["name"]}.html">{esc(t["title"])}</a></td>'
                + (f'<td>{esc(label[run["id"]])}</td>' if multi else '')
                + f'<td>{badge(t["area"], "area-" + t["area"])}</td>'
                f'<td class=grp>{esc(t["group"])}</td>'
                f'<td>{outcome_pill(rec)}</td>'
                f'<td class=numv>{esc(fmt_dur(rec.get("elapsed_s")))}</td>'
                f'<td class=numv>{cell}</td>'
                f'<td class=numv>{fmt_count(tokens["out"] if tokens else None)}</td>'
                f'<td class=numv>{rec.get("tool_calls") or DASH}</td>'
                f'<td class=numv>{tools.get("compile", 0) if tools else DASH}</td>'
                f'<td class=numv>{tools.get("check", 0) if tools else DASH}</td></tr>')

    model_opts = "".join(f'<option value="{esc(r["id"])}">{esc(label[r["id"]])}</option>'
                         for r in (charted or runs))
    present = {outcome(rec) for r in (charted or runs)
               for _, rec in covered[r["id"]]}
    status_opts = "".join(f'<option value={k}>{esc(lbl)}</option>'
                          for k, lbl, _ in OUTCOMES if k in present)
    controls = f"""
<div class=controls>
  <input class=search type=search data-for=problems placeholder="Search tasks" autocomplete=off>
  <div class=selects>
    {f'<select data-for=problems data-attr=model aria-label="Filter by model"><option value=all>All models</option>{model_opts}</select>' if multi else ''}
    <select data-for=problems data-attr=area aria-label="Filter by area">
      <option value=all>All areas</option>
      <option value=eBPF>eBPF</option>
      <option value=LLVM>LLVM</option>
      <option value=seL4>seL4</option>
    </select>
    <select data-for=problems data-attr=status aria-label="Filter by outcome">
      <option value=all>All outcomes</option>
      {status_opts}
    </select>
  </div>
</div>
"""

    body = f"""
<section class=prose>
<h1>Results</h1>
<p>Every run here is scored the same way: one attempt per task, no human help,
a fixed wall-clock cap, and a solution counts only when <code>check.sh</code>
passes every gate &mdash; hash integrity, no stubs, no cheats, a clean Lean
build, and no added axioms &mdash; and the blind LLM review does not reject
it. Cost and time are what the run itself reported.</p>

{comparison}
{by_group}
{matrix}
{''.join(sections)}

<h2>Every run</h2>
<p class=hint>Compiles and checks are the agent's own loop: how many times it
built the file, and how many times it submitted to <code>check.sh</code>.
Output tokens include reasoning; n/r marks a cost the harness did not report.
Open a task to see its activity profile.</p>
{controls}
<div class=tablewrap>
<table class="problems filterable" id=problems>
<thead><tr><th>Task</th>{'<th>Model</th>' if multi else ''}<th>Area</th>
<th>Group</th><th>Outcome</th><th>Time</th><th>Cost</th><th>Output tokens</th>
<th>Tool calls</th><th>Compiles</th><th>Checks</th></tr></thead>
<tbody>{''.join(rows)}</tbody>
</table>
</div>
<p class=empty data-for=problems hidden>No tasks match.</p>
</section>
"""
    return page("Vero: Results", body, 0, repo_url, "results")


def render_problem(t, runs, repo_url):
    name = t["name"]
    fdir = f"../files/{name}/"

    spec_blocks = []
    for sec, kind, body in t["sections"]:
        if not body.strip():
            continue
        tag = "Given" if kind == "provided" else "Your workspace"
        tag_cls = "given" if kind == "provided" else "editable"
        spec_blocks.append(
            f'<div class=secblock>'
            f'<div class="seclabel {tag_cls}">{esc(sec)} '
            f'<span class=sectag>{tag}</span></div>'
            f'<pre class=lean>{esc(body)}</pre></div>')
    spec = "\n".join(spec_blocks)

    dls = "".join(
        f'<li><a href="{fdir}{f}" download>{esc(f)}</a></li>'
        for f in BORROW_FILES if (TASKS_DIR / name / f).exists())

    instr_html = md(t["instruction"])

    if t["solution"]:
        s = t["solution"]
        meta_bits = [s["meta"]["agent"]]
        if s["meta"]["model"]:
            meta_bits.append(model_label(s["meta"]["model"], runs))
        sol_code = "".join(
            f'<div class=secblock><div class="seclabel editable">{esc(sec)}</div>'
            f'<pre class=lean>{esc(body)}</pre></div>'
            for sec, kind, body in s["sections"] if kind == "editable" and body.strip())
        note = ""
        if s["note"]:
            note = (f'<details class=note><summary>Agent note</summary>'
                    f'<div class=prose>{md(s["note"])}</div></details>')
        solution = f"""
<section id=solutions>
<h2>Solution</h2>
<div class=solcard>
  <div class=solmeta>{esc(' · '.join(meta_bits))} <span class="status solved">PASS</span></div>
  {sol_code}
  {note}
</div>
</section>
"""
    elif t["status"] == "solved":
        who = [run.get("label") or run.get("model") for run, rec in t["runs"]
               if outcome(rec) == "PASS"]
        names = (" and ".join(who) if len(who) < 3
                 else ", ".join(who[:-1]) + ", and " + who[-1])
        many = len(who) > 1
        solution = f"""
<section id=solutions>
<h2>Solution</h2>
<p class=open-note>{esc(names)} solved this task in the run{'s' if many else ''}
below. The solution{'s are' if many else ' is'} under review and
{'are' if many else 'is'} not published yet.</p>
</section>
"""
    else:
        solution = """
<section id=solutions>
<h2>Solution</h2>
<p class=open-note>No solution yet. This task is open.</p>
</section>
"""

    cards = "".join(
        run_card(run, rec,
                 bool(t["solution"]) and
                 t["solution"]["meta"]["model"] == run.get("model"))
        for run, rec in t["runs"])
    agent_runs = f"""
<section id=runs>
<h2>Agent run{'s' if len(t["runs"]) > 1 else ''}</h2>
<p class=hint>One attempt per model, no human help. The profile counts the
agent's tool calls over the run: what it read, edited, compiled, and submitted
to <code>check.sh</code>.</p>
{cards}
</section>
""" if t["runs"] else ""

    badges = [badge(t["area"], "area-" + t["area"]), badge(t["group"], "grp")]
    if t["complexity"]:
        badges.append(badge(t["complexity"], "cx"))
    badges.append(status_pill(t["status"]))

    desc = f'<p class=desc>{esc(t["description"])}</p>' if t["description"] else ""

    body = f"""
<p class=crumb><a href="../problems.html">Problems</a> / {t['id']:03d}</p>
<header class=probhead>
  <h1>{esc(t["title"])}</h1>
  <div class=badges>{''.join(badges)}</div>
  <div class=probid>{esc(name)}</div>
</header>
{desc}

<section>
<h2>Specification</h2>
<p class=hint>Provided sections are fixed. Fill the editable sections with an
implementation and a proof.</p>
{spec}
</section>

<section class=borrow>
<h2>Borrow this problem</h2>
<ul class=files>{dls}</ul>
</section>

{solution}

{agent_runs}

<details class=instr>
<summary>Full instruction</summary>
<div class=prose>{instr_html}</div>
</details>
"""
    return page(f"Vero: {t['title']}", body, 1, repo_url, "problems")


# --- Build -------------------------------------------------------------------

def load_tasks(runs):
    tasks = []
    for d in sorted(TASKS_DIR.iterdir()):
        if not d.is_dir() or "_" not in d.name:
            continue
        content = read(d / "Task.lean")
        instruction = read(d / "INSTRUCTION.md")
        area = d.name.split("_", 1)[0]
        ttl = title_of(content, d.name)
        sol_dir = find_solution(d.name)
        solution = None
        if sol_dir:
            solution = {
                "meta": solution_meta(sol_dir, d.name),
                "sections": sections_of(read(sol_dir / "Task.lean")),
                "note": read(sol_dir / "agent_note.md"),
            }
        task_runs = runs_for(d.name, runs)
        passed = any(outcome(rec) == "PASS" for _, rec in task_runs)
        tasks.append({
            "name": d.name, "area": area, "title": ttl,
            "runs": task_runs,
            # Published means the Lean solution is on the page; solved means
            # a run solved it (check.sh and the LLM review) but the solution
            # is still under review.
            "status": "published" if solution else
                      ("solved" if passed else "open"),
            "group": group_of(d.name, content),
            "description": description_of(content),
            "sections": sections_of(content),
            "instruction": instruction,
            "complexity": complexity_of(instruction),
            "solution": solution,
        })
    # Stable IDs: area order then name.
    order = {"eBPF": 0, "LLVM": 1, "seL4": 2}
    tasks.sort(key=lambda t: (order.get(t["area"], 9), t["name"]))
    for i, t in enumerate(tasks, 1):
        t["id"] = i
    return tasks


def main():
    ap = argparse.ArgumentParser(description="Build the Vero static site.")
    ap.add_argument("--out", default=str(BENCH_ROOT / "site"))
    ap.add_argument("--repo-url", default=DEFAULT_REPO_URL,
                    help="Repository URL for the GitHub link "
                         f"(default: {DEFAULT_REPO_URL}).")
    args = ap.parse_args()
    out = Path(args.out)

    if out.exists():
        shutil.rmtree(out)
    (out / "assets").mkdir(parents=True)
    (out / "problems").mkdir()
    (out / "files").mkdir()
    (out / ".nojekyll").write_text("")

    (out / "assets" / "style.css").write_text(STYLE)
    (out / "assets" / "app.js").write_text(APP_JS)
    if LOGOS_DIR.exists():
        shutil.copytree(LOGOS_DIR, out / "assets" / "logos")

    runs = load_runs()
    tasks = load_tasks(runs)
    if runs:
        PAGES.add("results")          # before rendering: the nav reads PAGES
    results = render_results(tasks, runs, args.repo_url)

    # About is the landing page; the task board lives at problems.html.
    (out / "index.html").write_text(render_about(tasks, runs, args.repo_url))
    (out / "problems.html").write_text(render_index(tasks, runs, args.repo_url))
    if results:
        (out / "results.html").write_text(results)
    else:
        PAGES.discard("results")

    for t in tasks:
        (out / "problems" / f"{t['name']}.html").write_text(
            render_problem(t, runs, args.repo_url))
        fdst = out / "files" / t["name"]
        fdst.mkdir()
        for f in BORROW_FILES:
            src = TASKS_DIR / t["name"] / f
            if src.exists():
                shutil.copy2(src, fdst / f)

    print(f"built {len(tasks)} problem pages into {out}")
    print(f"solved: {sum(1 for t in tasks if t['status'] != 'open')}"
          f" ({sum(1 for t in tasks if t['status'] == 'published')} published)"
          f", runs: {', '.join(r['id'] for r in runs) or 'none'}")


STYLE = """/* Vero site. Conservative CSS (no grid, no custom properties) so it
   renders identically in old and modern engines. */
* { box-sizing: border-box; }
html { -webkit-text-size-adjust: 100%; }
body {
  margin: 0; color: #14171a; background: #fff;
  font: 15px/1.65 -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto,
        Helvetica, Arial, sans-serif;
  -webkit-font-smoothing: antialiased;
}
a { color: #1a4fa0; text-decoration: none; }
a:hover { text-decoration: underline; }
main { max-width: 900px; margin: 0 auto; padding: 0 20px 64px; }

.topbar {
  border-bottom: 1px solid #ececef; background: #fff;
  display: flex; align-items: center; justify-content: space-between;
  padding: 12px 20px; max-width: 900px; margin: 0 auto;
}
.brand { font-weight: 700; font-size: 20px; color: #111; letter-spacing: .5px; }
.topbar nav a { margin-left: 18px; color: #444; font-size: 14px; }
.topbar nav a.active { color: #111; font-weight: 600; }

.hero { padding: 28px 0 8px; border-bottom: 1px solid #eee; margin-bottom: 20px; }
.hero h1 { font-size: 26px; margin: 0 0 10px; line-height: 1.25;
  letter-spacing: -.02em; }
.hero p { color: #333; margin: 8px 0; }
.hero .stat { color: #555; font-size: 14px; }

/* --- Landing page. Roomier rhythm, a mono eyebrow over every section, and
   cards that line up on a single baseline. ---------------------------------- */
.landing section { padding: 44px 0 0; }
.landing section + section { border-top: 1px solid #f0f0f2; }
.landing .eyebrow { margin: 0 0 6px; color: #1a4fa0; font-size: 11px;
  font-weight: 700; letter-spacing: .12em; text-transform: uppercase;
  font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace; }
.landing h1 { font-size: 40px; line-height: 1.12; letter-spacing: -.025em;
  margin: 0 0 14px; }
.landing h2 { font-size: 23px; line-height: 1.25; letter-spacing: -.015em;
  border: 0; padding: 0; margin: 0 0 8px; }
.landing h3 { font-size: 15px; margin: 26px 0 6px; }
.landing .lede { font-size: 17px; line-height: 1.6; color: #43474d;
  max-width: 640px; margin: 0 0 20px; }
.landing .sublede { color: #55595f; margin: 0 0 14px; max-width: 660px; }
.landing .hero { border: 0; padding: 40px 0 4px; margin: 0; }
.landing p { color: #33373d; }

.cta { margin: 0 0 24px; }
.btn { display: inline-block; margin: 0 8px 8px 0; padding: 9px 16px;
  border: 1px solid #d8dade; border-radius: 8px; background: #fff;
  color: #24272c; font-size: 14px; font-weight: 600; }
.btn:hover { text-decoration: none; border-color: #1a4fa0; color: #1a4fa0; }
.btn.primary { background: #1a4fa0; border-color: #1a4fa0; color: #fff; }
.btn.primary:hover { background: #16437f; border-color: #16437f; color: #fff; }

a.arrow { font-weight: 600; }
a.arrow:after { content: " \\2192"; }

.landing .card { border-radius: 12px; padding: 16px 18px 14px;
  background: #fff; border-color: #e9eaed; display: flex;
  flex-direction: column; }
.landing .card h3 { margin: 0 0 6px; font-size: 15.5px; letter-spacing: -.01em; }
.landing .card p { font-size: 14px; color: #4a4e54; margin: 0 0 8px; }
.landing .card .ex { margin-top: auto; padding-top: 10px; font-size: 12.5px;
  color: #6a6f76; border-top: 1px solid #f0f0f2; }
.kicker { font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace;
  font-size: 11px; font-weight: 700; color: #aeb3ba; letter-spacing: .08em;
  margin-bottom: 6px; }

.areacard .arealogo { height: 30px; margin: 2px 0 12px; }
.areacard .arealogo img { height: 28px; width: auto; max-width: 60%; }
.areacard .browse { display: flex; align-items: center;
  justify-content: space-between; margin-top: auto; padding-top: 10px;
  border-top: 1px solid #f0f0f2; }
.areacard .areacount { float: none; margin: 0; font-size: 12px; }
.areacard .go { color: #1a4fa0; font-size: 13px; font-weight: 600; }

.landing .figure { margin: 10px 0 4px; border: 1px solid #e9eaed;
  border-radius: 12px; background: #fbfbfc; padding: 14px 16px; }
.landing .duo { margin: 8px -6px 0; }
.landing .panel { border-radius: 12px; border-color: #e9eaed; }
.landing .panel pre.code { max-height: 380px; overflow: auto; }
.ptag { float: right; font-weight: 500; color: #8b9099;
  font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace;
  font-size: 11.5px; }
.landing .results { margin-top: 4px; }
.closing .card p:last-child { margin-bottom: 0; }
ul.authors { list-style: none; padding: 0; margin: 0; font-size: 14px; }
ul.authors li { margin: 6px 0; color: #33373d; }
ul.authors .badge { margin-right: 8px; }
.landing .trademark { margin: 24px 0 0; }

.controls { display: flex; align-items: center; justify-content: space-between;
  margin: 18px 0 12px; flex-wrap: wrap; }
.search { padding: 8px 12px; border: 1px solid #ccc; border-radius: 6px;
  font-size: 14px; width: 260px; max-width: 100%; }
.selects { display: flex; flex-wrap: wrap; }
.selects select { margin-left: 10px; padding: 7px 10px; border: 1px solid #ccc;
  border-radius: 6px; font-size: 13px; color: #333; background: #fff; cursor: pointer; }

table.problems { width: 100%; border-collapse: collapse; font-size: 14px; }
.problems th { text-align: left; color: #888; font-weight: 600; font-size: 12px;
  text-transform: uppercase; letter-spacing: .4px; border-bottom: 1px solid #e6e6e6;
  padding: 8px 10px; }
.problems td { border-bottom: 1px solid #f0f0f0; padding: 9px 10px; vertical-align: middle; }
.problems tbody tr { cursor: pointer; }
.problems tbody tr:hover { background: #f7f9fc; }
td.num { color: #aaa; font-variant-numeric: tabular-nums; width: 48px; }
td.numv { color: #333; font-variant-numeric: tabular-nums; white-space: nowrap; }
td.ttl { font-weight: 500; }
td.grp { color: #666; }

.badge { display: inline-block; padding: 2px 8px; border-radius: 4px; font-size: 12px;
  font-weight: 600; border: 1px solid #ddd; color: #333; }
.badge.area-eBPF { background: #eef4ff; border-color: #cddffb; color: #1a4fa0; }
.badge.area-LLVM { background: #fdf0e8; border-color: #f6d5bf; color: #a5541f; }
.badge.area-seL4 { background: #eefaf0; border-color: #cbe9cf; color: #1f7a37; }
.badge.grp { background: #f4f4f6; }
.badge.cx { background: #f6f2fb; border-color: #e2d5f2; color: #6b3fa0; }

.status { display: inline-block; font-size: 12px; font-weight: 600; padding: 2px 8px;
  border-radius: 999px; white-space: nowrap; }
.status.open { background: #f2f2f2; color: #888; }
.status.solved { background: #e7f6ea; color: #1f7a37; }
.status.published { background: #1f7a37; color: #fff; }
.status.rejected { background: #faf0dc; color: #8a5a00; }

.crumb { color: #888; font-size: 13px; margin: 18px 0 4px; }
.probhead h1 { font-size: 25px; margin: 4px 0 10px; line-height: 1.25;
  letter-spacing: -.02em; }
.badges .badge, .badges .status { margin-right: 6px; }
.probid { color: #aaa; font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace;
  font-size: 12px; margin-top: 8px; }
.desc { color: #333; background: #fafafa; border-left: 3px solid #ddd;
  padding: 10px 14px; margin: 18px 0; }

h2 { font-size: 17px; margin: 28px 0 8px; padding-bottom: 4px; border-bottom: 1px solid #eee; }
.hint, .empty { color: #888; font-size: 13px; }

.secblock { margin: 10px 0; border: 1px solid #e6e6e6; border-radius: 6px; overflow: hidden; }
.seclabel { font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace;
  font-size: 12px; font-weight: 700; padding: 6px 12px; background: #f6f8fa;
  border-bottom: 1px solid #e6e6e6; color: #333; }
.seclabel.editable { background: #fffaf0; }
.sectag { float: right; font-weight: 500; color: #999; }
.seclabel.editable .sectag { color: #b8860b; }
pre.lean, pre.code {
  margin: 0; padding: 12px 14px; overflow-x: auto; background: #fbfbfd;
  font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace;
  font-size: 12.5px; line-height: 1.5; color: #24292e;
}
pre.code { border-radius: 6px; border: 1px solid #eee; }

.borrow ul.files { list-style: none; padding: 0; margin: 8px 0; }
.files li { display: inline-block; margin: 0 8px 8px 0; }
.files a { display: inline-block; border: 1px solid #cddffb; background: #eef4ff;
  color: #1a4fa0; padding: 5px 12px; border-radius: 6px; font-size: 13px;
  font-family: ui-monospace, Menlo, Consolas, monospace; }

.solcard { border: 1px solid #cbe9cf; border-radius: 8px; padding: 4px 14px 12px;
  background: #fbfefb; }
.solmeta { font-size: 13px; color: #444; margin: 12px 0; }
.open-note { color: #888; }

details.instr, details.note { margin: 18px 0; }
details summary { cursor: pointer; font-weight: 600; color: #333; padding: 6px 0; }
.callout { background: #eef4ff; border: 1px solid #cddffb; border-radius: 8px;
  padding: 14px 16px; color: #234; margin: 14px 0; }

.prose h1 { font-size: 26px; letter-spacing: -.02em; }
.prose p, .prose li { color: #333; }
.figure { margin: 20px 0; }
.figure svg { max-width: 100%; height: auto; display: block; }

.stats { display: flex; flex-wrap: wrap; margin: 20px -6px 6px; }
.stat-tile { display: block; flex: 1 1 120px; margin: 6px;
  border: 1px solid #e9eaed; border-radius: 12px; padding: 14px 16px;
  background: #fbfbfc; }
a.stat-tile { color: inherit; }
a.stat-tile:hover { text-decoration: none; border-color: #1a4fa0;
  background: #f6f9fe; }
.stat-num { font-size: 28px; font-weight: 700; color: #14171a; line-height: 1.15;
  letter-spacing: -.02em; font-variant-numeric: tabular-nums; }
.stat-label { font-size: 11px; color: #6a6f76; margin-top: 4px;
  letter-spacing: .07em; text-transform: uppercase; font-weight: 600; }

.cards { display: flex; flex-wrap: wrap; margin: 12px -6px; }
.card { flex: 1 1 240px; margin: 6px; border: 1px solid #e6e6e6;
  border-radius: 8px; padding: 12px 16px; background: #fafbfc; }
.card h3 { margin: 2px 0 6px; font-size: 15px; }
.card p { margin: 6px 0; font-size: 13.5px; }
.card .ex { color: #667; font-size: 12.5px; }
.arealogo { height: 44px; margin: 4px 0 8px; }
.arealogo img { height: 44px; width: auto; max-width: 70%; }
.areacount { float: right; font-size: 12px; font-weight: 600; color: #555;
  background: #f2f2f2; border-radius: 999px; padding: 2px 10px; margin-top: 12px; }
a.alink { color: inherit; }
a.alink:hover { text-decoration: none; border-color: #1a4fa0; background: #f7f9fc; }
.browse { color: #1a4fa0; font-size: 13px; font-weight: 600; }

.duo { display: flex; flex-wrap: wrap; margin: 12px -6px; align-items: stretch; }
.panel { flex: 1 1 340px; margin: 6px; border: 1px solid #e6e6e6;
  border-radius: 8px; overflow: hidden; background: #fff;
  display: flex; flex-direction: column; }
.phead { font-size: 12.5px; font-weight: 700; padding: 8px 14px;
  background: #f6f8fa; border-bottom: 1px solid #e6e6e6; color: #333; }
.panel pre.code { border: 0; border-radius: 0; flex: 1; }
.pfoot { font-size: 12px; color: #667; padding: 8px 14px;
  border-top: 1px solid #f0f0f0; background: #fafbfc; }

.tok-c { color: #6e7781; font-style: italic; }
.tok-k { color: #0550ae; font-weight: 600; }
.tok-s { color: #0a3069; }
.tok-n { color: #953800; }
.tok-t { color: #8250df; }

/* Agent runs: a metric row, then the activity profile. */
.runcard { border: 1px solid #e6e6e6; border-radius: 8px; padding: 10px 14px 12px;
  background: #fafbfc; margin: 12px 0; }
.runhead { font-size: 14px; color: #333; padding-bottom: 8px;
  border-bottom: 1px solid #eee; }
.runhead .runmeta { color: #888; font-size: 12.5px; margin-left: 6px; }
.runhead .status { float: right; }
.runstats { display: flex; flex-wrap: wrap; margin: 10px -6px 2px; }
.runstat { flex: 1 1 84px; margin: 4px 6px; }
.rs-num { font-size: 17px; font-weight: 600; color: #111;
  font-variant-numeric: tabular-nums; }
.rs-label { font-size: 11.5px; color: #777; }
.runnote { font-size: 12.5px; color: #666; margin: 6px 0 0; }

.traj { margin-top: 10px; }
.traj svg, .chart svg { width: 100%; height: auto; display: block; }
.legend { margin-top: 6px; font-size: 12px; color: #666; }
.legend .key { margin-right: 14px; white-space: nowrap; }
.legend i { display: inline-block; width: 10px; height: 10px; border-radius: 2px;
  margin-right: 5px; vertical-align: -1px; }
.legend i.dot { border-radius: 999px; }
.legend i.hollow { background: #fff; border: 2px solid #8a8f98; }
.chart { margin: 14px 0 6px; }

.tablewrap { overflow-x: auto; }

table.results { width: 100%; border-collapse: collapse; font-size: 14px; margin: 10px 0; }
.results th { text-align: left; color: #888; font-weight: 600; font-size: 12px;
  text-transform: uppercase; letter-spacing: .4px; border-bottom: 1px solid #e6e6e6;
  padding: 8px 10px; }
.results td { border-bottom: 1px solid #f0f0f0; padding: 9px 10px; }
.results tr.total td { border-top: 1px solid #e6e6e6; font-weight: 600; }
.results td .badge { white-space: nowrap; }

.trademark { color: #999; font-size: 12px; margin-top: 28px; }
.prose code { background: #f4f4f6; padding: 1px 5px; border-radius: 4px;
  font-family: ui-monospace, Menlo, Consolas, monospace; font-size: 92%; }
.prose blockquote { border-left: 3px solid #ddd; margin: 10px 0; padding: 4px 14px; color: #555; }

footer { border-top: 1px solid #eee; color: #999; font-size: 13px;
  max-width: 900px; margin: 0 auto; padding: 20px; }

/* Phone: the hero headline and the section rhythm come down a step. */
@media (max-width: 560px) {
  .landing h1 { font-size: 30px; }
  .landing .lede { font-size: 16px; }
  .landing section { padding-top: 32px; }
  .landing h2 { font-size: 21px; }
}
"""

APP_JS = """// Progressive enhancement: client-side search and filters for every
// table.filterable. Its controls name it in data-for; each select filters the
// rows on the data-<data-attr> attribute.
(function () {
  function wire(table) {
    var id = table.id;
    var rows = [].slice.call(table.tBodies[0].rows);
    var search = document.querySelector('input[data-for="' + id + '"]');
    var empty = document.querySelector('.empty[data-for="' + id + '"]');
    var sels = [].slice.call(document.querySelectorAll('select[data-for="' + id + '"]'));
    var q = '';

    function apply() {
      var shown = 0;
      for (var i = 0; i < rows.length; i++) {
        var r = rows[i];
        var vis = !q || r.getAttribute('data-k').indexOf(q) !== -1;
        for (var j = 0; vis && j < sels.length; j++) {
          var v = sels[j].value;
          var rv = r.getAttribute('data-' + sels[j].getAttribute('data-attr'));
          // "solved" covers published solutions too; "published" is the subset.
          vis = v === 'all' || rv === v || (v === 'solved' && rv === 'published');
        }
        r.style.display = vis ? '' : 'none';
        if (vis) shown++;
      }
      if (empty) empty.hidden = shown !== 0;
    }
    if (search) search.addEventListener('input', function () {
      q = this.value.trim().toLowerCase(); apply();
    });
    var preset = false;
    for (var j = 0; j < sels.length; j++) {
      sels[j].addEventListener('change', apply);
      // Preset from the query string (?area=eBPF, ?status=solved): the About
      // page's area cards and stat tiles link here.
      var m = location.search.match(
        new RegExp('[?&]' + sels[j].getAttribute('data-attr') + '=([A-Za-z0-9_.-]+)'));
      if (m) {
        sels[j].value = m[1];
        if (sels[j].value === m[1]) preset = true; else sels[j].value = 'all';
      }
    }
    if (preset) apply();
  }
  var tables = document.querySelectorAll('table.filterable');
  for (var i = 0; i < tables.length; i++) wire(tables[i]);
})();
"""


if __name__ == "__main__":
    main()
