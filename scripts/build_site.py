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

# Outcomes: the green the site already uses for PASS, with both kinds of
# non-solve in neutrals so the eye reads "how much is solved" first.
OUTCOMES = [("PASS", "Solved", "#1f7a37"),
            ("FAIL", "Failed", "#8a8f98"),
            ("TIMEOUT", "Timed out", "#c9ccd1")]
OUTCOME_LABEL = {k: lbl for k, lbl, _ in OUTCOMES}
DASH = "\u2014"
OUTCOME_COLOR = {k: c for k, _, c in OUTCOMES}


# A run needs at least this many tasks before its own charts say anything.
MIN_CHART_TASKS = 10


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
    solved = [r for r in recs if r.get("status") == "PASS"]
    priced = [r for r in recs if r.get("cost_usd")]
    rate = cost_rate(recs)
    recorded = sum(r["cost_usd"] for r in priced)
    bounded = sum(cost_bound(r, rate)[0] or 0 for r in recs)
    times = [r["elapsed_s"] for r in solved if r.get("elapsed_s")]
    costs = [r["cost_usd"] for r in solved if r.get("cost_usd")]
    return {
        "n": len(recs), "solved": len(solved),
        "rate": round(100 * len(solved) / len(recs)) if recs else 0,
        "avg_time": statistics.fmean(times) if times else 0,
        "avg_cost": statistics.fmean(costs) if costs else 0,
        "recorded": recorded, "bounded": bounded,
        "unpriced": len(recs) - len(priced), "cost_rate": rate,
    }


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
            r["rate"] = cost_rate(list(r["tasks"].values()))
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
    status = rec.get("status", "UNKNOWN")
    pill_cls = "solved" if status == "PASS" else "open"
    tools = rec.get("tools") or {}
    tokens = rec.get("tokens")
    cost, est = cost_bound(rec, run.get("rate", 0))
    stats = [("Wall clock", fmt_dur(rec.get("elapsed_s"))),
             ("Cost", ("\u2264 " + fmt_usd(cost)) if est else fmt_usd(cost)),
             ("Turns", str(rec.get("turns") or DASH)),
             ("Tool calls", str(rec.get("tool_calls") or DASH)),
             ("Compiles", str(tools.get("compile", 0))),
             ("check.sh runs", str(tools.get("check", 0))),
             ("Output tokens", fmt_count(tokens["out"] if tokens else None))]
    tiles = "".join(f'<div class=runstat><div class=rs-num>{esc(v)}</div>'
                    f'<div class=rs-label>{esc(k)}</div></div>'
                    for k, v in stats)
    note = ""
    if status == "PASS" and not published:
        note = ('<p class=runnote>The solution passed every gate; it is under '
                'review and not published yet.</p>')
    elif status == "TIMEOUT":
        note = (f'<p class=runnote>Killed at the {fmt_dur(run.get("limit_s"))} '
                f'cap. A killed run writes no final record, so its turns and '
                f'token totals are unknown and its cost is an upper bound: '
                f'this much wall clock at the highest rate the run reached '
                f'elsewhere. The tool calls below are exact.</p>')
    meta = " \u00b7 ".join(x for x in (run.get("agent"), fmt_date(run.get("date")))
                          if x)
    return f"""
<div class=runcard>
  <div class=runhead>
    <strong>{esc(run.get("label") or run.get("model") or "Agent")}</strong>
    <span class=runmeta>{esc(meta)}</span>
    <span class="status {pill_cls}">{esc(status)}</span>
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


def page(title, body, depth, repo_url, active=""):
    """Wrap body in the shared shell. `depth` = path depth for relative links."""
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
<main>
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
  <p class=stat>{len(tasks)} problems ({esc(area_line)}). {solved} solved by an
  agent, {published} with the solution published.
  <a href="results.html">Run results and cost</a>.</p>
</section>
"""

    controls = """
<div class=controls>
  <input id=search type=search placeholder="Search problems" autocomplete=off>
  <div class=selects>
    <select id=areasel aria-label="Filter by area">
      <option value=all>All areas</option>
      <option value=eBPF>eBPF</option>
      <option value=LLVM>LLVM</option>
      <option value=seL4>seL4</option>
    </select>
    <select id=statussel aria-label="Filter by status">
      <option value=all>All status</option>
      <option value=solved>Solved</option>
      <option value=published>Published</option>
      <option value=open>Open</option>
    </select>
  </div>
</div>
"""

    table = f"""
<table class=problems id=problems>
<thead><tr><th>#</th><th>Title</th><th>Area</th><th>Group</th><th>Status</th></tr></thead>
<tbody>
{''.join(rows)}
</tbody>
</table>
<p class=empty id=empty hidden>No problems match.</p>
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
     "score.",
     "The tnum_step() solution is <strong>merged into</strong> the Linux "
     "kernel."),
]

AREA_CARDS = [
    ("eBPF", "ebpf.png",
     "Sound and optimal abstract operators for the Linux kernel eBPF "
     "verifier, over the cnum and interval domains."),
    ("LLVM", "llvm.png",
     "Optimal KnownBits and DemandedBits transfer functions, the forward "
     "and backward bit-level analyses the optimizer relies on."),
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

    # The two countable tiles are links into the board they summarize.
    stats = "".join(
        (f'<a class=stat-tile href="{href}">' if href else '<div class=stat-tile>')
        + f'<div class=stat-num>{esc(num)}</div>'
          f'<div class=stat-label>{esc(label)}</div>'
        + ("</a>" if href else "</div>")
        for num, label, href in [
            (str(len(tasks)), "tasks", "problems.html"),
            (str(len(by_area)), "real systems", ""),
            (str(solved), "solved by an agent", "problems.html?status=solved"),
        ])

    principle_cards = "".join(
        f'<div class=card><h3>{esc(title)}</h3><p>{esc(sent)}</p>'
        f'<p class=ex>Example: {ex}</p></div>'
        for title, sent, ex in PRINCIPLES)

    area_cards = "".join(
        f'<a class="card alink" href="problems.html?area={name}">'
        f'<div class=arealogo>'
        f'<img src="assets/logos/{logo}" alt="{esc(name)} logo">'
        f'<span class=areacount>{by_area.get(name, 0)} tasks</span></div>'
        f'<p>{esc(desc)}</p>'
        f'<p class=browse>Browse {esc(name)} tasks &rarr;</p></a>'
        for name, logo, desc in AREA_CARDS)

    published_rows = "".join(
        f'<tr><td><a href="problems/{d}.html">{esc(n)}</a></td>'
        f'<td>{badge(a, "area-" + a)}</td>'
        f'<td>{esc(model_label(m, runs))}</td><td>{esc(h)}</td></tr>'
        for d, n, a, m, h in PUBLISHED)

    run_line = ""
    if runs:
        r = runs[0]
        recs = [rec for t in tasks for run, rec in t["runs"]
                if run["id"] == r["id"]]
        st = run_stats(recs)
        total = ("\u2264 " + fmt_usd(st["bounded"])) if st["unpriced"] \
            else fmt_usd(st["recorded"])
        run_line = (
            f'<p>The suite was run once with '
            f'<strong>{esc(r.get("label"))}</strong> on '
            f'{esc(fmt_date(r.get("date")))}, one attempt per task under a '
            f'{esc(fmt_dur(r.get("limit_s")))} cap: it solved '
            f'<strong>{st["solved"]} of the {st["n"]} tasks it ran</strong>, at '
            f'an average of {esc(fmt_dur(st["avg_time"]))} and '
            f'{esc(fmt_usd(st["avg_cost"]))} per solved task, for {esc(total)} '
            f'of API spend in total. '
            f'<a href="results.html">Full results, cost, and what the agent did '
            f'&rarr;</a></p>')

    body = f"""
<section class=prose>
<h1>About</h1>
<p>Vero evaluates coding agents on verified code generation: given a formal
specification, the agent must produce an implementation together with a Lean 4
proof that the implementation satisfies it. The proof checker decides
correctness, so reviewing a solution reduces to reading a concise
specification.</p>

<div class=stats>{stats}</div>

<div class=figure>{ANATOMY_SVG}</div>

<h2>Principles</h2>
<div class=cards>{principle_cards}</div>

<h2>Three areas, {len(tasks)} tasks</h2>
<div class=cards>{area_cards}</div>

<h2>Results</h2>
{run_line}

<h3>Published solutions</h3>
<p>{published} solutions are published in full, one per area. The rest of the
solved tasks are under review; each solution is released once it has been read
and checked.</p>
<table class=results>
<thead><tr><th>Solution</th><th>Area</th><th>Model</th><th>Highlight</th></tr></thead>
<tbody>{published_rows}</tbody>
</table>

<h3>In the Linux kernel</h3>
<p>The agent-written <code>tnum_step()</code> is
<a href="{KERNEL_COMMIT_URL}">merged into the Linux kernel</a>, and it is
<strong>provably correct</strong>: the Lean 4 proof on the left machine-checks
the soundness and optimality of the exact algorithm that the C code on the
right implements.</p>
<div class=duo>
<div class=panel>
  <div class=phead>Lean 4 &mdash; algorithm, specification, proof</div>
  <pre class=code>{hl(merged_lean(), "lean")}</pre>
  <div class=pfoot>Five obligations, each closed by a machine-checked proof.</div>
</div>
<div class=panel>
  <div class=phead>C &mdash; as merged in <code>kernel/bpf/tnum.c</code></div>
  <pre class=code>{hl(merged_c(), "c")}</pre>
  <div class=pfoot><a href="{KERNEL_COMMIT_URL}">bpf-next commit 833ef4a954e1</a></div>
</div>
</div>

<h2>Borrow a problem</h2>
<p>Every problem page bundles its specification, instruction, and Lake project
files for download; start from the editable sections. Contributions are
welcome: a new task from a real system, a sharper specification, or a solution
to an open problem.</p>

<h2>Authors</h2>
<ul>
<li>eBPF tasks: Hao Sun</li>
<li>LLVM tasks: Cong Li</li>
<li>seL4 tasks: Zenan Li</li>
</ul>
<p class=trademark>The eBPF, LLVM, and seL4 logos identify the upstream
projects and are trademarks of their respective owners.</p>
</section>
"""
    return page("Vero: About", body, 0, repo_url, "about")


def outcome_bars(rows):
    """Solved / failed / timed out per task group, as stacked bars.

    `rows` is [(area, group, {status: count}, total)], longest bar = widest
    group, so the bars carry suite composition as well as the solve rate.
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
        clip = f"clip{area}{group}"
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
    legend = "".join(f'<span class=key><i style="background:{c}"></i>{esc(l)}</span>'
                     for _, l, c in OUTCOMES)
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

    `points` is [(name, title, minutes, usd, status)]. Solved runs are filled
    marks, failed ones hollow, so outcome never rides on colour alone.
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
              '</span><span class=key><i class="dot hollow"></i>Failed</span>')
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


def render_results(tasks, runs, repo_url):
    """One section per run: what it solved, what it cost, how it was spent."""
    if not runs:
        return None
    covered = {r["id"]: [(t, rec) for t in tasks for run, rec in t["runs"]
                         if run["id"] == r["id"]] for r in runs}
    stats = {r["id"]: run_stats([rec for _, rec in covered[r["id"]]])
             for r in runs}
    charted = [r for r in runs if len(covered[r["id"]]) >= MIN_CHART_TASKS]

    # The run table is the comparison: same tasks, same cap, same accounting
    # for every model.  Runs are only comparable when they cover the same
    # tasks, which the "partial" tag flags.
    run_rows = ""
    for r in runs:
        st = stats[r["id"]]
        # A run over a handful of tasks has a solve rate, but not one that
        # means anything next to a full-suite run; say so instead of printing
        # a percentage that invites the comparison.
        partial = r not in charted
        tag = ' <span class=badge>partial</span>' if partial else ""
        solved = (f'{st["solved"]} of {st["n"]}' if partial
                  else f'{st["solved"]} ({st["rate"]}%)')
        total = (("&le; " + fmt_usd(st["bounded"])) if st["unpriced"]
                 else fmt_usd(st["recorded"]))
        run_rows += (
            f'<tr><td class=ttl>{esc(r.get("label") or r.get("model"))}{tag}</td>'
            f'<td>{esc(fmt_date(r.get("date")))}</td>'
            f'<td class=numv>{st["n"]}</td>'
            f'<td class=numv>{solved}</td>'
            f'<td class=numv>{esc(fmt_dur(st["avg_time"]))}</td>'
            f'<td class=numv>{esc(fmt_usd(st["avg_cost"]))}</td>'
            f'<td class=numv>{esc(fmt_usd(st["recorded"]))}</td>'
            f'<td class=numv>{total}</td></tr>')

    sections = []
    for run in charted:
        st = stats[run["id"]]
        rate = st["cost_rate"]
        tiles = "".join(
            f'<div class=stat-tile><div class=stat-num>{esc(num)}</div>'
            f'<div class=stat-label>{esc(label)}</div></div>'
            for num, label in [
                (f'{st["solved"]}/{st["n"]}', f'tasks solved ({st["rate"]}%)'),
                (fmt_dur(st["avg_time"]), "average time per solved task"),
                (fmt_usd(st["avg_cost"]), "average cost per solved task"),
                ((f'\u2264 {fmt_usd0(st["bounded"])}' if st["unpriced"]
                  else fmt_usd0(st["recorded"])),
                 "upper bound on run cost" if st["unpriced"]
                 else "cost of the run"),
            ])

        order, groups = [], {}
        for t, rec in covered[run["id"]]:
            key = (t["area"], t["group"])
            if key not in groups:
                groups[key] = {}
                order.append(key)
            groups[key][rec["status"]] = groups[key].get(rec["status"], 0) + 1
        bars = outcome_bars([(a, g, groups[(a, g)], sum(groups[(a, g)].values()))
                             for a, g in order])
        points = [(t["name"], t["title"], rec["elapsed_s"] / 60, rec["cost_usd"],
                   rec["status"]) for t, rec in covered[run["id"]]
                  if rec.get("cost_usd") and rec.get("elapsed_s")]
        killed = st["unpriced"]
        cost_note = ""
        if killed:
            cost_note = (
                f'<p class=hint>{killed} runs were killed at the '
                f'{esc(fmt_dur(run.get("limit_s")))} cap and write no cost '
                f'record, so they are not plotted. They are not free either: '
                f'the table below bounds each of them by its own wall clock at '
                f'the highest rate this run reached '
                f'({esc(fmt_usd(rate * 60))} per minute), which is where the '
                f'{esc(fmt_usd(st["bounded"]))} bound comes from.</p>')
        sections.append(f"""
<h2>{esc(run.get("label") or run.get("model"))}</h2>
<p>{esc(run.get("agent"))}, {esc(fmt_date(run.get("date")))}. One attempt per
task, no human help, {esc(fmt_dur(run.get("limit_s")))} of wall clock per task.
{st["n"]} of the {len(tasks)} tasks were run.</p>
<div class=stats>{tiles}</div>
<h3>Where it solves and where it stalls</h3>
<p class=hint>One bar per task group, as long as the group is large.</p>
{bars}
<h3>What a task costs</h3>
<p class=hint>Every run that recorded a cost, against the wall clock it
took.</p>
{cost_scatter(points)}
{cost_note}
""")

    # Per-task rows, every run in one table.
    multi = len(charted) > 1
    rows = []
    for run in charted or runs:
        rate = stats[run["id"]]["cost_rate"]
        label = run.get("label") or run.get("model")
        for t, rec in sorted(covered[run["id"]],
                             key=lambda tr: (tr[1]["status"] != "PASS", tr[0]["id"])):
            tools = rec.get("tools") or {}
            status = rec["status"]
            cost, est = cost_bound(rec, rate)
            cell = ("\u2264 " + fmt_usd(cost)) if est else fmt_usd(cost)
            cls = "solved" if status == "PASS" else "open"
            keywords = " ".join([t["name"], t["title"], t["area"], t["group"],
                                 label]).lower()
            rows.append(
                f'<tr data-k="{esc(keywords)}" data-area="{t["area"]}" '
                f'data-status="{status}" onclick="location=\'problems/{t["name"]}.html\'">'
                f'<td class=ttl><a href="problems/{t["name"]}.html">{esc(t["title"])}</a></td>'
                + (f'<td>{esc(label)}</td>' if multi else '')
                + f'<td>{badge(t["area"], "area-" + t["area"])}</td>'
                f'<td class=grp>{esc(t["group"])}</td>'
                f'<td><span class="status {cls}">'
                f'{esc(OUTCOME_LABEL.get(status, status))}</span></td>'
                f'<td class=numv>{esc(fmt_dur(rec.get("elapsed_s")))}</td>'
                f'<td class=numv>{cell}</td>'
                f'<td class=numv>{rec.get("turns") or DASH}</td>'
                f'<td class=numv>{tools.get("compile", 0)}</td>'
                f'<td class=numv>{tools.get("check", 0)}</td></tr>')

    controls = """
<div class=controls>
  <input id=search type=search placeholder="Search tasks" autocomplete=off>
  <div class=selects>
    <select id=areasel aria-label="Filter by area">
      <option value=all>All areas</option>
      <option value=eBPF>eBPF</option>
      <option value=LLVM>LLVM</option>
      <option value=seL4>seL4</option>
    </select>
    <select id=statussel aria-label="Filter by outcome">
      <option value=all>All outcomes</option>
      <option value=PASS>Solved</option>
      <option value=FAIL>Failed</option>
      <option value=TIMEOUT>Timed out</option>
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
build, and no added axioms. Cost and time are what the run itself reported.</p>

<div class=tablewrap>
<table class=results>
<thead><tr><th>Model</th><th>Date</th><th>Tasks</th><th>Solved</th>
<th>Average time</th><th>Average cost</th><th>Cost recorded</th>
<th>Cost incl. killed runs</th></tr></thead>
<tbody>{run_rows}</tbody>
</table>
</div>
<p class=hint>A run killed at the cap writes no final cost record. Dropping
those would understate what a model spent, since the longest runs are the ones
that get killed, so the last column bounds each of them by its wall clock at
the highest cost rate that same run reached. Runs marked <em>partial</em>
covered only part of the suite and are listed for provenance, not for
comparison.</p>

{''.join(sections)}

<h2>Every run</h2>
<p class=hint>Compiles and checks are the agent's own loop: how many times it
built the file, and how many times it submitted to <code>check.sh</code>. Open
a task to see its activity profile.</p>
{controls}
<div class=tablewrap>
<table class=problems id=problems>
<thead><tr><th>Task</th>{'<th>Model</th>' if multi else ''}<th>Area</th>
<th>Group</th><th>Outcome</th><th>Time</th><th>Cost</th><th>Turns</th>
<th>Compiles</th><th>Checks</th></tr></thead>
<tbody>{''.join(rows)}</tbody>
</table>
</div>
<p class=empty id=empty hidden>No tasks match.</p>
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
        who = model_label(t["runs"][0][0].get("model"), runs)
        solution = f"""
<section id=solutions>
<h2>Solution</h2>
<p class=open-note>{esc(who)} solved this task in the run below. The solution
is under review and is not published yet.</p>
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
<p class=hint>One attempt, no human help. The profile counts the agent's tool
calls over the run: what it read, edited, compiled, and submitted to
<code>check.sh</code>.</p>
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
        passed = any(rec.get("status") == "PASS" for _, rec in task_runs)
        tasks.append({
            "name": d.name, "area": area, "title": ttl,
            "runs": task_runs,
            # Published means the Lean solution is on the page; solved means
            # a run passed check.sh but the solution is still under review.
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
  margin: 0; color: #1a1a1a; background: #fff;
  font: 15px/1.6 -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
}
a { color: #1a4fa0; text-decoration: none; }
a:hover { text-decoration: underline; }
main { max-width: 900px; margin: 0 auto; padding: 0 20px 64px; }

.topbar {
  border-bottom: 1px solid #e6e6e6; background: #fff;
  display: flex; align-items: center; justify-content: space-between;
  padding: 12px 20px; max-width: 900px; margin: 0 auto;
}
.brand { font-weight: 700; font-size: 20px; color: #111; letter-spacing: .5px; }
.topbar nav a { margin-left: 18px; color: #444; font-size: 14px; }
.topbar nav a.active { color: #111; font-weight: 600; }

.hero { padding: 28px 0 8px; border-bottom: 1px solid #eee; margin-bottom: 20px; }
.hero h1 { font-size: 26px; margin: 0 0 10px; line-height: 1.25; }
.hero p { color: #333; margin: 8px 0; }
.hero .stat { color: #555; font-size: 14px; }

.controls { display: flex; align-items: center; justify-content: space-between;
  margin: 18px 0 12px; flex-wrap: wrap; }
#search { padding: 8px 12px; border: 1px solid #ccc; border-radius: 6px;
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
  border-radius: 999px; }
.status.open { background: #f2f2f2; color: #888; }
.status.solved { background: #e7f6ea; color: #1f7a37; }
.status.published { background: #1f7a37; color: #fff; }

.crumb { color: #888; font-size: 13px; margin: 18px 0 4px; }
.probhead h1 { font-size: 24px; margin: 4px 0 10px; line-height: 1.25; }
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

.prose h1 { font-size: 24px; }
.prose p, .prose li { color: #333; }
.figure { margin: 20px 0; }
.figure svg { max-width: 100%; height: auto; display: block; }

.stats { display: flex; flex-wrap: wrap; margin: 18px -6px 6px; }
.stat-tile { display: block; flex: 1 1 120px; margin: 6px; text-align: center;
  border: 1px solid #e6e6e6; border-radius: 8px; padding: 12px 8px; background: #fafbfc; }
a.stat-tile { color: inherit; }
a.stat-tile:hover { text-decoration: none; border-color: #1a4fa0; background: #f7f9fc; }
.stat-num { font-size: 26px; font-weight: 700; color: #1a4fa0; line-height: 1.2; }
.stat-label { font-size: 12px; color: #666; margin-top: 2px; }

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

.trademark { color: #999; font-size: 12px; margin-top: 28px; }
.prose code { background: #f4f4f6; padding: 1px 5px; border-radius: 4px;
  font-family: ui-monospace, Menlo, Consolas, monospace; font-size: 92%; }
.prose blockquote { border-left: 3px solid #ddd; margin: 10px 0; padding: 4px 14px; color: #555; }

footer { border-top: 1px solid #eee; color: #999; font-size: 13px;
  max-width: 900px; margin: 0 auto; padding: 20px; }
"""

APP_JS = """// Progressive enhancement: client-side search and area filter on the index.
(function () {
  var search = document.getElementById('search');
  var table = document.getElementById('problems');
  if (!table) return;
  var rows = [].slice.call(table.tBodies[0].rows);
  var empty = document.getElementById('empty');
  var area = 'all', status = 'all', q = '';

  function apply() {
    var shown = 0;
    for (var i = 0; i < rows.length; i++) {
      var r = rows[i];
      var okA = area === 'all' || r.getAttribute('data-area') === area;
      // "solved" covers published solutions too; "published" is the subset.
      var rs = r.getAttribute('data-status');
      var okS = status === 'all' || rs === status ||
                (status === 'solved' && rs === 'published');
      var okQ = !q || r.getAttribute('data-k').indexOf(q) !== -1;
      var vis = okA && okS && okQ;
      r.style.display = vis ? '' : 'none';
      if (vis) shown++;
    }
    if (empty) empty.hidden = shown !== 0;
  }
  if (search) search.addEventListener('input', function () {
    q = this.value.trim().toLowerCase(); apply();
  });
  var areasel = document.getElementById('areasel');
  var statussel = document.getElementById('statussel');
  if (areasel) areasel.addEventListener('change', function () { area = this.value; apply(); });
  if (statussel) statussel.addEventListener('change', function () { status = this.value; apply(); });

  // Preset the filters from the query string: the About page's area cards
  // and stat tiles link here.
  var m = location.search.match(/[?&]area=(eBPF|LLVM|seL4)/);
  if (m && areasel) { area = m[1]; areasel.value = area; }
  var ms = location.search.match(/[?&]status=(published|solved|open|PASS|FAIL|TIMEOUT)/);
  if (ms && statussel) { status = ms[1]; statussel.value = status; }
  if (m || ms) apply();
})();
"""


if __name__ == "__main__":
    main()
