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
from pathlib import Path

BENCH_ROOT = Path(__file__).resolve().parent.parent
TASKS_DIR = BENCH_ROOT / "tasks"
SOLVED_DIR = BENCH_ROOT / "solved"

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


def solution_meta(sol_dir: Path):
    meta = {"agent": "Claude Code", "model": None, "turns": None,
            "elapsed_min": None, "status": "PASS"}
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
            meta["model"] = d.get("model")
            meta["turns"] = d.get("num_turns")
        except json.JSONDecodeError:
            pass
    return meta


# --- Page rendering ----------------------------------------------------------

def page(title, body, depth, repo_url, active=""):
    """Wrap body in the shared shell. `depth` = path depth for relative links."""
    root = "../" * depth
    def nav(href, label, key):
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
    {nav('index.html', 'Problems', 'problems')}
    {nav('about.html', 'About', 'about')}
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


def render_index(tasks, repo_url):
    solved = sum(1 for t in tasks if t["solution"])
    by_area = {}
    for t in tasks:
        by_area.setdefault(t["area"], 0)
        by_area[t["area"]] += 1
    area_line = ", ".join(f"{by_area[a]} {a}" for a in ("eBPF", "LLVM", "seL4") if a in by_area)

    rows = []
    for t in tasks:
        status = ('<span class="status solved">Solved</span>' if t["solution"]
                  else '<span class="status open">Open</span>')
        keywords = " ".join([t["name"], t["title"], t["area"], t["group"]]).lower()
        st = "solved" if t["solution"] else "open"
        rows.append(
            f'<tr data-k="{esc(keywords)}" data-area="{t["area"]}" data-status="{st}" '
            f'onclick="location=\'problems/{t["name"]}.html\'">'
            f'<td class=num>{t["id"]:03d}</td>'
            f'<td class=ttl><a href="problems/{t["name"]}.html">{esc(t["title"])}</a></td>'
            f'<td>{badge(t["area"], "area-" + t["area"])}</td>'
            f'<td class=grp>{esc(t["group"])}</td>'
            f'<td>{status}</td></tr>')

    intro = f"""
<section class=hero>
  <h1>Verified code generation on real-world systems</h1>
  <p>A solver produces an implementation together with a Lean 4 proof that it
  meets a machine-checked specification. The {len(tasks)} problems come from
  three security- and correctness-critical systems: the Linux kernel eBPF
  verifier, LLVM, and the seL4 microkernel. Each specification encodes a new
  requirement with no existing implementation, so a correct solution improves
  the upstream system.</p>
  <p class=stat>{len(tasks)} problems ({esc(area_line)}). {solved} with a
  published solution. <a href="about.html">About and results</a>.</p>
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


def render_about(tasks, repo_url):
    body = f"""
<section class=prose>
<h1>About</h1>
<p>Vero evaluates coding agents on verified code generation. Given a formal
specification, an agent must produce an implementation and a Lean 4 proof that
the implementation satisfies it. A proof checker decides correctness, so the
review burden shifts from reading code to validating a concise specification.</p>

<h2>Design principles</h2>
<ul>
<li><strong>Real-world.</strong> Every task originates from a production system,
not a textbook exercise or a programming contest.</li>
<li><strong>New specification.</strong> Each specification encodes a requirement
for which no implementation exists in the system or in public sources.</li>
<li><strong>Valuable to solve.</strong> A correct solution benefits the upstream
system, for example by improving the soundness or precision of a critical
component.</li>
</ul>

<h2>Areas</h2>
<ul>
<li><strong>eBPF.</strong> {esc(AREAS['eBPF'])}</li>
<li><strong>LLVM.</strong> {esc(AREAS['LLVM'])}</li>
<li><strong>seL4.</strong> {esc(AREAS['seL4'])}</li>
</ul>

<h2>Results</h2>
<p>Claude Code solved 3 of the {len(tasks)} tasks, one in each area. Real-world
verified code generation remains an open problem, and the unsolved tasks are
concrete targets for future work.</p>
<div class=callout>
One solution found by an agent has been merged into the Linux kernel. It
replaces a 20-line algorithm proposed by domain experts with a 4-line
provably-correct alternative in the eBPF verifier.
</div>

<h2>Borrow a problem</h2>
<p>Each problem page bundles its specification, instruction, and Lake project
files for download. Open a problem, read the specification, and start from the
editable sections.</p>

<h2>Contribute</h2>
<p>Contributions are welcome: a new task from a real system, an improvement to a
specification, or a published solution to an open problem. A task is a Lean 4
specification with provided and editable sections and a checker that enforces
proof soundness and integrity.</p>

<h2>Authors</h2>
<ul>
<li>eBPF tasks: Hao Sun</li>
<li>LLVM tasks: Cong Li</li>
<li>seL4 tasks: Zenan Li</li>
</ul>
<p>Vero is described in our ASPLOS paper.</p>
</section>
"""
    return page("Vero: About", body, 0, repo_url, "about")


def render_problem(t, repo_url):
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
            meta_bits.append(s["meta"]["model"])
        if s["meta"]["turns"]:
            meta_bits.append(f'{s["meta"]["turns"]} turns')
        if s["meta"]["elapsed_min"]:
            meta_bits.append(f'{s["meta"]["elapsed_min"]} min')
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
    else:
        solution = """
<section id=solutions>
<h2>Solution</h2>
<p class=open-note>No published solution. This task is open.</p>
</section>
"""

    badges = [badge(t["area"], "area-" + t["area"]), badge(t["group"], "grp")]
    if t["complexity"]:
        badges.append(badge(t["complexity"], "cx"))
    badges.append('<span class="status solved">Solved</span>' if t["solution"]
                  else '<span class="status open">Open</span>')

    desc = f'<p class=desc>{esc(t["description"])}</p>' if t["description"] else ""

    body = f"""
<p class=crumb><a href="../index.html">Problems</a> / {t['id']:03d}</p>
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

<details class=instr>
<summary>Full instruction</summary>
<div class=prose>{instr_html}</div>
</details>
"""
    return page(f"Vero: {t['title']}", body, 1, repo_url, "problems")


# --- Build -------------------------------------------------------------------

def load_tasks():
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
                "meta": solution_meta(sol_dir),
                "sections": sections_of(read(sol_dir / "Task.lean")),
                "note": read(sol_dir / "agent_note.md"),
            }
        tasks.append({
            "name": d.name, "area": area, "title": ttl,
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
    ap.add_argument("--repo-url", default="",
                    help="Public repository URL for the GitHub link (optional).")
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

    tasks = load_tasks()

    (out / "index.html").write_text(render_index(tasks, args.repo_url))
    (out / "about.html").write_text(render_about(tasks, args.repo_url))

    for t in tasks:
        (out / "problems" / f"{t['name']}.html").write_text(
            render_problem(t, args.repo_url))
        fdst = out / "files" / t["name"]
        fdst.mkdir()
        for f in BORROW_FILES:
            src = TASKS_DIR / t["name"] / f
            if src.exists():
                shutil.copy2(src, fdst / f)

    print(f"built {len(tasks)} problem pages into {out}")
    print(f"solved: {sum(1 for t in tasks if t['solution'])}")


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
      var okS = status === 'all' || r.getAttribute('data-status') === status;
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
})();
"""


if __name__ == "__main__":
    main()
