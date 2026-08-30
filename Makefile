# Vero benchmark shortcuts. Override any variable on the command line, e.g.
#   make run SOLVER=scripts/copilot.sh PARALLEL=4 TASKS='cnum_*'

# Local credentials (see .env.example); `export` passes everything defined
# here, including .env values, to the recipes' environment.
-include .env
export

PY         ?= python3
SOLVER     ?= scripts/claude_code.sh
OUTPUT_DIR ?= ./results
PARALLEL   ?= 1
TIMEOUT    ?= 2
TASKS      ?=
CATEGORIES ?=
ARGS       ?=
REPO_URL   ?= https://github.com/SunHao-0/Vero
PORT       ?= 8000
NETWORK    ?= host
IMAGE      := vero-lean4

_filters := $(if $(TASKS),--tasks $(TASKS)) $(if $(CATEGORIES),--categories $(CATEGORIES))

.DEFAULT_GOAL := help
.PHONY: help gen list run run-all resume build analyze llm-check clean check-auth site serve

help:
	@grep -hE '^[a-z-]+:.*##' $(MAKEFILE_LIST) \
	  | awk -F':.*## ' '{printf "  \033[36m%-9s\033[0m %s\n", $$1, $$2}'

gen:  ## Instantiate lean template and produce tasks
	$(PY) template/gen.py tasks --all

list: ## List all available tasks
	$(PY) template/gen.py --list

run: check-auth ## Run the benchmark (vars: SOLVER OUTPUT_DIR PARALLEL TIMEOUT TASKS CATEGORIES NETWORK ARGS)
	$(PY) scripts/run_bench.py --output-dir $(OUTPUT_DIR) --solver $(SOLVER) \
	  --parallel $(PARALLEL) --timeout $(TIMEOUT) --docker-network "$(NETWORK)" $(_filters) $(ARGS)

run-all: check-auth ## Run all tasks incl. solved ones, with agent web access disabled
	$(PY) scripts/run_bench.py --output-dir $(OUTPUT_DIR) --solver $(SOLVER) \
	  --parallel $(PARALLEL) --timeout $(TIMEOUT) --docker-network "$(NETWORK)" --run-all $(_filters) $(ARGS)

resume: check-auth ## Re-run only the ERROR tasks of a previous run in OUTPUT_DIR
	$(PY) scripts/run_bench.py --output-dir $(OUTPUT_DIR) --solver $(SOLVER) \
	  --parallel $(PARALLEL) --timeout $(TIMEOUT) --docker-network "$(NETWORK)" --resume $(_filters) $(ARGS)

build: ## Build the Docker image (vero-lean4) with the host UID/GID (NETWORK for RUN steps)
	docker build -f Dockerfile --network=$(NETWORK) \
	  --build-arg SOLVER_UID=$$(id -u) --build-arg SOLVER_GID=$$(id -g) -t $(IMAGE) .

analyze: ## Re-check and analyze the results in OUTPUT_DIR
	$(PY) scripts/analyze_bench.py --output-dir $(OUTPUT_DIR)

llm-check: SOLVER := scripts/claude_code.sh
llm-check: check-auth ## Run llm check
	$(PY) scripts/llm_check.py $(OUTPUT_DIR) --parallel $(PARALLEL) $(ARGS)

site: ## Build the static website into site/ (pass REPO_URL=... for GitHub links)
	$(PY) scripts/build_site.py --repo-url "$(REPO_URL)"

serve: ## Build and serve the website locally (PORT, default 8000)
	$(PY) scripts/serve_site.py --port $(PORT) --repo-url "$(REPO_URL)"

clean:  ## Clean up
	rm -rf $(OUTPUT_DIR)

check-auth:
	@if echo "$(SOLVER)" | grep -q copilot; then \
	  [ -n "$$COPILOT_GITHUB_TOKEN$$GH_TOKEN$$GITHUB_TOKEN" ] \
	    || { echo "error: set COPILOT_GITHUB_TOKEN (or GH_TOKEN/GITHUB_TOKEN) for scripts/copilot.sh"; exit 1; }; \
	else \
	  [ -n "$$CLAUDE_CODE_OAUTH_TOKEN$$ANTHROPIC_API_KEY" ] \
	    || { echo "error: set CLAUDE_CODE_OAUTH_TOKEN (or ANTHROPIC_API_KEY) for scripts/claude_code.sh"; exit 1; }; \
	fi
