# Lean4 verification environment for the Vero benchmark.
#
# Includes Lean4 via elan, the Claude Code / Gemini / Codex / Copilot CLIs,
# and the lean-lsp-mcp server.
#
# Build:
#   docker build -t vero-lean4 .
#
# Auth at runtime via:
#   docker run -e CLAUDE_CODE_OAUTH_TOKEN="$TOKEN" ...
#
FROM ubuntu:24.04

RUN apt-get update && apt-get install -y --no-install-recommends \
        curl \
        git \
        ca-certificates \
        build-essential \
        python3 \
        ripgrep \
        openssh-client \
    && rm -rf /var/lib/apt/lists/*

RUN curl -LsSf https://astral.sh/uv/install.sh | env UV_INSTALL_DIR=/usr/local/bin sh

RUN curl -fsSL https://deb.nodesource.com/setup_22.x | bash - \
    && apt-get install -y --no-install-recommends nodejs \
    && npm install -g @anthropic-ai/claude-code@latest @google/gemini-cli@latest @openai/codex@latest @github/copilot@latest \
    && rm -rf /var/lib/apt/lists/*

# Create solver user with host UID/GID so bind-mounted files have correct ownership.
ARG SOLVER_UID=1000
ARG SOLVER_GID=1000
RUN userdel -r ubuntu 2>/dev/null || true \
    && groupadd -o -g ${SOLVER_GID} solver \
    && useradd -o -u ${SOLVER_UID} -g solver -m -s /bin/bash solver

USER solver

COPY --chown=solver:solver template/task_dir/lean-toolchain /tmp/lean-toolchain
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | bash -s -- -y --default-toolchain "$(cat /tmp/lean-toolchain)"
ENV PATH="/home/solver/.elan/bin:${PATH}"
ENV ELAN_HOME="/home/solver/.elan"

RUN lean --version && lake --version

# Warm the Mathlib olean cache at build time.
COPY --chown=solver:solver \
     template/task_dir/lakefile.lean \
     template/task_dir/lake-manifest.json \
     template/task_dir/lean-toolchain \
     /home/solver/vero-warm/
RUN cd /home/solver/vero-warm \
    && printf 'import Mathlib\n' > Task.lean \
    && lake exe cache get \
    && lake lean Task.lean

ENV UV_CACHE_DIR="/home/solver/.cache/uv"
RUN uvx lean-lsp-mcp --help >/dev/null 2>&1 \
    || echo "WARNING: lean-lsp-mcp pre-cache failed (optional; the lean-lsp MCP may be slower or unavailable at run time)"

# Pre-install lean4-skills plugin into a seed directory.
RUN { claude plugin marketplace add cameronfreer/lean4-skills 2>&1 \
      && claude plugin install lean4@lean4-skills 2>&1 ; } \
      || echo "WARNING: lean4-skills plugin install for Claude Code failed (optional; the lean4 skill will be unavailable)" \
    && mkdir -p /home/solver/.plugin-seed \
    && cp -a /home/solver/.claude/plugins/* /home/solver/.plugin-seed/ 2>/dev/null || true

RUN { copilot plugin marketplace add cameronfreer/lean4-skills 2>&1 \
      && copilot plugin install lean4@lean4-skills 2>&1 ; } \
      || echo "WARNING: lean4-skills plugin install for GitHub Copilot failed (optional; the lean4 skill will be unavailable)" \
    && mkdir -p /home/solver/.copilot \
    && printf '{\n  "mcpServers": {\n    "lean-lsp": { "command": "uvx", "args": ["lean-lsp-mcp"] }\n  }\n}\n' \
        > /home/solver/.copilot/mcp-config.json

ENV NODE_OPTIONS="--max-old-space-size=4096"
ENV CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC=1
ENV DISABLE_AUTOUPDATER=1
ENV CLAUDE_CODE_PLUGIN_SEED_DIR="/home/solver/.plugin-seed"
ENV COPILOT_AUTO_UPDATE=false

RUN mkdir -p /home/solver/.claude /home/solver/.gemini /home/solver/.codex \
        /home/solver/.copilot \
    && rm -rf /home/solver/.claude/backups

WORKDIR /task
