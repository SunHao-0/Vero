#!/usr/bin/env bash

set -euo pipefail

TASK_DIR="$1"
PROMPT="$2"
MODEL="${CODEX_MODEL:-gpt-6-astra}"
AUTH_MODE="${CODEX_AUTH_MODE:-api}"

cd "$TASK_DIR"
TASK_DIR="$(pwd)"
mkdir -p logs

case "$AUTH_MODE" in
    chatgpt)
        unset CODEX_API_KEY OPENAI_API_KEY OPENAI_BASE_URL CODEX_BASE_URL CODEX_PROVIDER_NAME
        ;;
    api)
        if [[ -z "${CODEX_API_KEY:-}" && -n "${OPENAI_API_KEY:-}" ]]; then
            export CODEX_API_KEY="$OPENAI_API_KEY"
        fi
        ;;
    *) echo "error: CODEX_AUTH_MODE must be api or chatgpt" >&2; exit 2 ;;
esac

if [[ -d /home/solver/.lean4-codex ]]; then
    export LEAN4_PLUGIN_ROOT=/home/solver/.lean4-codex
    export LEAN4_SCRIPTS="$LEAN4_PLUGIN_ROOT/lib/scripts"
    export LEAN4_REFS="$LEAN4_PLUGIN_ROOT/skills/lean4/references"
fi

FLAGS=(
    --dangerously-bypass-approvals-and-sandbox
    --skip-git-repo-check
    --json
    --color never
    --model "$MODEL"
)
if [[ "$AUTH_MODE" == chatgpt ]]; then
    FLAGS+=(
        -c 'forced_login_method="chatgpt"'
        -c 'cli_auth_credentials_store="file"'
        -c 'model_provider="openai"'
    )
fi

WEB_SEARCH=live
if [[ -n "${VERO_DISABLE_WEB:-}" ]]; then
    WEB_SEARCH=disabled
fi
FLAGS+=(-c "web_search=\"$WEB_SEARCH\"")

if [[ -f "$TASK_DIR/lean-toolchain" ]] || ls "$TASK_DIR"/*.lean &>/dev/null; then
    LEAN_TOOLS='[
        "lean_goal", "lean_diagnostic_messages", "lean_hover_info", "lean_completions",
        "lean_multi_attempt", "lean_local_search", "lean_leansearch", "lean_loogle",
        "lean_leanfinder", "lean_state_search", "lean_hammer_premise", "lean_code_actions",
        "lean_file_outline", "lean_run_code", "lean_verify", "lean_build",
        "lean_declaration_file", "lean_term_goal"
    ]'
    FLAGS+=(
        -c 'mcp_servers.lean-lsp.command="uvx"'
        -c 'mcp_servers.lean-lsp.args=["lean-lsp-mcp"]'
        -c "mcp_servers.lean-lsp.enabled_tools=$LEAN_TOOLS"
    )
fi

if [[ -n "${CODEX_BASE_URL:-}" ]]; then
    PROVIDER_CONFIG=$(python3 - <<'PY'
import json, os
values = {
    "name": os.environ.get("CODEX_PROVIDER_NAME") or "Vero",
    "base_url": os.environ["CODEX_BASE_URL"],
    "env_key": "CODEX_API_KEY",
    "wire_api": "responses",
}
print("model_providers.vero={" + ",".join(
    key + "=" + json.dumps(value, ensure_ascii=False)
    for key, value in values.items()
) + "}")
PY
)
    FLAGS+=(-c 'model_provider="vero"' -c "$PROVIDER_CONFIG")
fi

CLI_VERSION="$(codex --version)"
python3 - "$MODEL" "$CLI_VERSION" "$WEB_SEARCH" "$AUTH_MODE" "${FLAGS[@]}" -- "$PROMPT" <<'PY'
import json, os, sys
from datetime import datetime, timezone
meta = {
    "task_dir": os.getcwd(),
    "solver": "codex",
    "model": sys.argv[1],
    "cli_version": sys.argv[2],
    "web_access": sys.argv[3] == "live",
    "auth_mode": sys.argv[4],
    "start_time": datetime.now(timezone.utc).isoformat(),
    "command": ["codex", "exec", *sys.argv[5:]],
}
with open("logs/meta.json", "w") as f:
    json.dump(meta, f, indent=2)
    f.write("\n")
PY

set +e
codex exec "${FLAGS[@]}" -- "$PROMPT" </dev/null 2> logs/stderr.log \
    | python3 -u -c '
import json, sys, time
for line in sys.stdin:
    try:
        event = json.loads(line)
        event["ts"] = time.time()
        print(json.dumps(event, separators=(",", ":")), flush=True)
    except (ValueError, TypeError):
        print(line, end="", flush=True)
' \
    | tee logs/transcript.jsonl
PIPE_CODES=("${PIPESTATUS[@]}")
set -e

EXIT_CODE=${PIPE_CODES[0]}
if [[ $EXIT_CODE -eq 0 ]]; then
    for rc in "${PIPE_CODES[@]}"; do
        if [[ $rc -ne 0 ]]; then EXIT_CODE=$rc; break; fi
    done
fi

python3 - "$EXIT_CODE" <<'PY'
import json, sys
from datetime import datetime, timezone
with open("logs/meta.json") as f:
    meta = json.load(f)
meta["end_time"] = datetime.now(timezone.utc).isoformat()
meta["exit_code"] = int(sys.argv[1])
meta["num_turns"] = 0
meta["usage"] = {}
meta["is_error"] = meta["exit_code"] != 0
with open("logs/transcript.jsonl") as f:
    for line in f:
        try:
            event = json.loads(line)
        except ValueError:
            continue
        if not isinstance(event, dict):
            continue
        if event.get("type") == "thread.started":
            meta["session_id"] = event.get("thread_id")
        elif event.get("type") == "turn.completed":
            meta["num_turns"] += 1
            for key, value in (event.get("usage") or {}).items():
                if isinstance(value, (int, float)):
                    meta["usage"][key] = meta["usage"].get(key, 0) + value
        elif event.get("type") == "turn.failed":
            meta["is_error"] = True
with open("logs/meta.json", "w") as f:
    json.dump(meta, f, indent=2)
    f.write("\n")
PY

exit "$EXIT_CODE"
