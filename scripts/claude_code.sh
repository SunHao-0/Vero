#!/usr/bin/env bash
# Solver: Claude Code with full transcript logging.
#
# Usage (via run_bench.py):
#   --solver scripts/claude_code.sh
#
# Authentication: set CLAUDE_CODE_OAUTH_TOKEN env var (or ANTHROPIC_API_KEY).
#
# Environment variables:
#   CLAUDE_MODEL            Model to use (default: claude-opus-5)
#   CLAUDE_MAX_BUDGET_USD   Per-task $ cap (optional; passed as --max-budget-usd)
#
# Logs written to <task_dir>/logs/:
#   transcript.jsonl  Raw stream-json events (full interaction transcript)
#   stderr.log        Claude stderr output
#   meta.json         Invocation metadata (command, model, timing, exit code)

set -euo pipefail

TASK_DIR="$1"
PROMPT="$2"
MODEL="${CLAUDE_MODEL:-claude-opus-5}"
# Raise output token limit to avoid truncation on long reasoning/proofs
export CLAUDE_CODE_MAX_OUTPUT_TOKENS="${CLAUDE_CODE_MAX_OUTPUT_TOKENS:-64000}"

cd "$TASK_DIR"
mkdir -p logs

# `Skill` enables the pre-installed lean4 plugin; `Task` allows subagents;
# WebFetch/WebSearch cover Mathlib lookups that leansearch/loogle miss.
# VERO_DISABLE_WEB (run_bench.py --run-all) drops the web tools so
# published solutions cannot be looked up.
TOOLS="Bash,Edit,Read,Write,Glob,Grep,Skill,Task,TodoWrite"
if [[ -z "${VERO_DISABLE_WEB:-}" ]]; then
    TOOLS="${TOOLS},WebFetch,WebSearch"
fi

# MCP config for the lean-lsp server. Written to the solver user's config
# dir ($HOME/.claude/), which is NOT bind-mounted to the host in Docker
# mode, so it doesn't leak per-task state outside the container.
MCP_CONFIG="$HOME/.claude/mcp-lean-lsp.json"
EXTRA_FLAGS=()
if [[ -f "$TASK_DIR/lean-toolchain" ]] || ls "$TASK_DIR"/*.lean &>/dev/null; then
    mkdir -p "$(dirname "$MCP_CONFIG")"
    cat > "$MCP_CONFIG" <<'MCPEOF'
{
  "mcpServers": {
    "lean-lsp": { "command": "uvx", "args": ["lean-lsp-mcp"] }
  }
}
MCPEOF
    EXTRA_FLAGS+=(--mcp-config "$MCP_CONFIG" --strict-mcp-config)

    for t in \
        lean_goal lean_diagnostic_messages lean_hover_info lean_completions \
        lean_multi_attempt lean_local_search lean_leansearch lean_loogle \
        lean_leanfinder lean_state_search lean_hammer_premise lean_code_actions \
        lean_file_outline lean_run_code lean_verify lean_build \
        lean_declaration_file lean_term_goal
    do
        TOOLS="${TOOLS},mcp__lean-lsp__${t}"
    done
fi

# Per-task cost cap: safety net against runaway agents.
if [[ -n "${CLAUDE_MAX_BUDGET_USD:-}" ]]; then
    EXTRA_FLAGS+=(--max-budget-usd "$CLAUDE_MAX_BUDGET_USD")
fi

# Feature-detect optional flags. The Docker image may carry an older
# Claude Code CLI than the host (npm install is cache-pinned); passing a
# flag the CLI doesn't recognize hard-fails the run. Cache the help text
# once so we can probe cheaply.
CLAUDE_HELP="$(claude --help 2>&1 || true)"
_has_flag() { grep -q -- "$1" <<<"$CLAUDE_HELP"; }

# Prompt-cache optimization (introduced in newer CLIs): moves per-machine
# preamble into the first user message so parallel workers share the
# static system prompt cache.
if _has_flag '--exclude-dynamic-system-prompt-sections'; then
    EXTRA_FLAGS+=(--exclude-dynamic-system-prompt-sections)
fi

# --setting-sources project was tried here for hermeticity, but it also
# blocks Claude from reading the user-scoped plugin registration that
# `claude plugin install` writes at Docker build time — which kills the
# lean4 skill at runtime. Hermeticity is already achieved structurally:
# the Docker image starts with only what we put there, so the default
# (user+project+local) is already contamination-free.

START_TIME="$(date -Is)"
cat > logs/meta.json << METAEOF
{
  "task_dir": "$TASK_DIR",
  "model": "$MODEL",
  "max_budget_usd": "${CLAUDE_MAX_BUDGET_USD:-}",
  "start_time": "$START_TIME",
  "web_access": $([[ -z "${VERO_DISABLE_WEB:-}" ]] && echo true || echo false),
  "allowed_tools": "$TOOLS"
}
METAEOF

claude -p "$PROMPT" \
    --dangerously-skip-permissions \
    --output-format stream-json \
    --verbose \
    --model "$MODEL" \
    --allowedTools "$TOOLS" \
    "${EXTRA_FLAGS[@]}" \
    2> logs/stderr.log \
    | python3 -u -c "
import sys, json, time
for line in sys.stdin:
    line = line.rstrip('\n')
    if not line:
        print(line, flush=True)
        continue
    try:
        ev = json.loads(line)
        ev['ts'] = time.time()
        print(json.dumps(ev, separators=(',', ':')), flush=True)
    except Exception:
        print(line, flush=True)
" \
    | tee logs/transcript.jsonl

EXIT_CODE=${PIPESTATUS[0]}

END_TIME="$(date -Is)"
python3 -c "
import json
with open('logs/meta.json') as f:
    m = json.load(f)
m['end_time'] = '$END_TIME'
m['exit_code'] = $EXIT_CODE
try:
    with open('logs/transcript.jsonl') as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            evt = json.loads(line)
            if evt.get('type') == 'result':
                m['cost_usd'] = evt.get('cost_usd')
                m['num_turns'] = evt.get('num_turns')
                m['is_error'] = evt.get('is_error', False)
                m['session_id'] = evt.get('session_id')
                break
except Exception:
    pass
with open('logs/meta.json', 'w') as f:
    json.dump(m, f, indent=2)
"

exit "$EXIT_CODE"
