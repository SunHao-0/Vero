#!/usr/bin/env bash
# Solver: GitHub Copilot CLI with full transcript logging.
#
# Usage (via run_bench.py):
#   --solver scripts/copilot.sh
#
# Authentication (headless): set ONE of the following (precedence order):
#   COPILOT_GITHUB_TOKEN, GH_TOKEN, GITHUB_TOKEN
# Supported token types: a fine-grained PAT with the "Copilot Requests"
# permission, or an OAuth token from the GitHub Copilot CLI / gh app.
# Classic ghp_ personal access tokens are NOT supported by Copilot.
#
# Environment variables:
#   COPILOT_MODEL     Model to use (default: claude-opus-5)
#   COPILOT_CONTEXT   Context window tier: 'long_context' (1M) or 'default'
#                     (default: long_context)
#   COPILOT_EFFORT    Reasoning effort: none|low|medium|high|xhigh|max (optional)
#   COPILOT_MAX_BUDGET_USD
#                     Per-task cost cap in dollars (default: 30). Converted to
#                     AI credits at 1 credit = $0.01 (so $30 -> 3000 credits;
#                     CLI minimum is 30 credits). Set to "" to disable the cap.
#   COPILOT_MAX_AI_CREDITS
#                     Per-task cost cap in raw AI credits (overrides *_BUDGET_USD).
#   COPILOT_LEAN4_PLUGIN_DIR
#                     Local lean4 plugin dir passed via --plugin-dir. Fallback
#                     for --no-docker runs where the image's plugin seed is
#                     absent; in Docker the plugin is installed at build time.
#
# The wall-clock half of the budget (e.g. 2 hours) is enforced by run_bench.py
# --timeout, which hard-kills the container — not by this script.
#
# Logs written to <task_dir>/logs/:
#   transcript.jsonl  Raw stream-json events (full interaction transcript)
#   stderr.log        Copilot stderr output
#   meta.json         Invocation metadata (command, model, timing, exit code)
#   copilot-internal/ Copilot's own session logs (MCP/skill diagnostics)

set -euo pipefail

TASK_DIR="$1"
PROMPT="$2"
MODEL="${COPILOT_MODEL:-claude-opus-5}"
CONTEXT="${COPILOT_CONTEXT:-long_context}"

cd "$TASK_DIR"
mkdir -p logs

# --- MCP: lean-lsp server (stdio via uvx). Written to the user config dir so
# both the agent session and `copilot mcp list` pick it up. It augments
# ~/.copilot/mcp-config.json automatically. In Docker $HOME=/home/solver lives
# inside the container, so this never leaks per-task state to the host. ---
COPILOT_CFG_DIR="${COPILOT_HOME:-$HOME/.copilot}"
if [[ -f "$TASK_DIR/lean-toolchain" ]] || ls "$TASK_DIR"/*.lean &>/dev/null; then
    mkdir -p "$COPILOT_CFG_DIR"
    cat > "$COPILOT_CFG_DIR/mcp-config.json" <<'MCPEOF'
{
  "mcpServers": {
    "lean-lsp": { "command": "uvx", "args": ["lean-lsp-mcp"] }
  }
}
MCPEOF
fi

# Non-interactive mode requires --allow-all-tools; --no-ask-user makes
# the agent run autonomously.
# --disable-builtin-mcps drops the builtin github MCP: irrelevant to Lean
# proofs and keeps the tool surface focused on lean-lsp.
# --secret-env-vars redacts the auth token from tool/MCP environments and logs.
#
# --excluded-tools task removes the subagent-spawning tool. In headless (-p)
# mode a background subagent is a trap: the `task` tool returns immediately with
# "you'll be notified when it completes — tell the user you're waiting and end
# your response", the model complies and ends its turn, and the -p session then
# terminates before the orphaned subagent writes anything (observed: agent
# delegated the whole solve, went idle, session exited with Task.lean untouched
# and only agent_note.md written -> FAIL). Excluding it forces the model to do
# the work in its own foreground context. (--deny-tool only gates permission
# prompting and is overridden by --allow-all-tools, so it does NOT remove the
# tool; --excluded-tools does.)
FLAGS=(
    --allow-all-tools
    --allow-all-paths
    --excluded-tools task
    --no-ask-user
    --disable-builtin-mcps
    --no-auto-update
    --secret-env-vars "COPILOT_GITHUB_TOKEN,GH_TOKEN,GITHUB_TOKEN"
    --output-format json
    --log-level default
    --log-dir "$(pwd)/logs/copilot-internal"
    --model "$MODEL"
)

# URL fetches are a separate permission axis from tools; without
# --allow-all-urls, --no-ask-user auto-denies them. VERO_DISABLE_WEB
# (run_bench.py --run-all) omits the grant so published solutions
# cannot be looked up.
if [[ -z "${VERO_DISABLE_WEB:-}" ]]; then
    FLAGS+=(--allow-all-urls)
fi

# Context window tier (long_context = 1M for opus 5).
[[ -n "$CONTEXT" ]] && FLAGS+=(--context "$CONTEXT")

[[ -n "${COPILOT_EFFORT:-}" ]] && FLAGS+=(--effort "$COPILOT_EFFORT")

# Optional local plugin dir (fallback for --no-docker; in Docker the lean4
# plugin is installed at image build time).
if [[ -n "${COPILOT_LEAN4_PLUGIN_DIR:-}" && -d "${COPILOT_LEAN4_PLUGIN_DIR}" ]]; then
    FLAGS+=(--plugin-dir "$COPILOT_LEAN4_PLUGIN_DIR")
fi

# --- Cost budget (per task). Copilot meters spend in AI credits, where
# 1 credit = $0.01, so a dollar cap of COPILOT_MAX_BUDGET_USD maps to
# usd * 100 credits. The CLI enforces a 30-credit ($0.30) minimum. Precedence:
#   COPILOT_MAX_AI_CREDITS   raw credit count (wins if set)
#   COPILOT_MAX_BUDGET_USD   dollar cap; unset -> $30 default, "" -> disabled
# This is a soft cap: usage is only known after a model response returns, so a
# turn may overshoot slightly before the next call is blocked. The wall-clock
# half of the budget (e.g. 2h) is enforced by run_bench.py --timeout, which
# hard-kills the container. ---
BUDGET_FLAGS=()
AI_CREDITS="${COPILOT_MAX_AI_CREDITS:-}"
if [[ -z "$AI_CREDITS" ]]; then
    USD="${COPILOT_MAX_BUDGET_USD-30}"   # unset -> 30; explicit "" -> disabled
    if [[ -n "$USD" ]]; then
        AI_CREDITS=$(python3 -c "
try:
    print(max(30, round(float('$USD') * 100)))
except Exception:
    pass
" 2>/dev/null)
    fi
fi
[[ -n "$AI_CREDITS" ]] && BUDGET_FLAGS+=(--max-ai-credits "$AI_CREDITS")

START_TIME="$(date -Is)"
cat > logs/meta.json <<METAEOF
{
  "task_dir": "$TASK_DIR",
  "solver": "copilot",
  "model": "$MODEL",
  "context": "$CONTEXT",
  "max_ai_credits": "${AI_CREDITS:-}",
  "web_access": $([[ -z "${VERO_DISABLE_WEB:-}" ]] && echo true || echo false),
  "start_time": "$START_TIME"
}
METAEOF

# pipefail is disabled around the pipeline so a non-zero copilot exit is
# captured (via PIPESTATUS) rather than aborting the script.
run_copilot() {
    set +e
    copilot -p "$PROMPT" "$@" \
        2> logs/stderr.log \
        | tee logs/transcript.jsonl
    local rc=${PIPESTATUS[0]}
    set -e
    return "$rc"
}

# `|| EXIT_CODE=$?` keeps a non-zero solver exit from tripping `set -e` before
# we can capture it, run the retry, and write meta.json.
EXIT_CODE=0
run_copilot "${FLAGS[@]}" ${BUDGET_FLAGS[@]+"${BUDGET_FLAGS[@]}"} || EXIT_CODE=$?

# Safety net: a few Copilot CLI builds advertise --max-ai-credits in --help but
# reject it in prompt (-p) mode. That parse error is instant — no model call and
# no spend — so retry once without the cost cap, leaving the wall-clock budget
# (run_bench.py --timeout) as the sole limiter rather than failing every task.
if [[ $EXIT_CODE -ne 0 && ${#BUDGET_FLAGS[@]} -gt 0 ]] \
   && grep -q "unknown option '--max-ai-credits'" logs/stderr.log 2>/dev/null; then
    echo "WARN: copilot CLI rejected --max-ai-credits; retrying without cost cap" >&2
    BUDGET_FLAGS=()
    EXIT_CODE=0
    run_copilot "${FLAGS[@]}" || EXIT_CODE=$?
fi

END_TIME="$(date -Is)"
python3 - "$EXIT_CODE" "$END_TIME" <<'PYEOF'
import json, sys
exit_code = int(sys.argv[1]); end_time = sys.argv[2]
try:
    with open('logs/meta.json') as f:
        m = json.load(f)
except Exception:
    m = {}
m['end_time'] = end_time
m['exit_code'] = exit_code
try:
    with open('logs/transcript.jsonl') as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                evt = json.loads(line)
            except Exception:
                continue
            if evt.get('type') == 'result':
                m['session_id'] = evt.get('sessionId')
                m['result_exit_code'] = evt.get('exitCode')
                m['usage'] = evt.get('usage')
                break
except Exception:
    pass
with open('logs/meta.json', 'w') as f:
    json.dump(m, f, indent=2)
PYEOF

exit "$EXIT_CODE"
