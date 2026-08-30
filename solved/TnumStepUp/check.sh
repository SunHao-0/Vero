#!/usr/bin/env bash
#   ./check.sh                    # verify + stubs + integrity
#   ./check.sh --compile          # sorry stubs OK
#   ./check.sh --check-integrity  # check provided sections unchanged
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

TASK_FILE="Task.lean"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

extract_provided_hash() {
    local file="$1"
    local text
    text=$(sed -n '/=== BEGIN:.*provided/,/=== END:/p' "$file")
    printf '%s' "$text" | sha256sum | cut -d' ' -f1
}

# Extract all editable sections (IMPLEMENTATION, PROOF, AUX) from the task file.
extract_editable() {
    sed -n '/=== BEGIN:.*editable/,/=== END:/p' "$TASK_FILE"
}

check_integrity() {
    if [[ ! -f .provided_hash ]]; then
        echo -e "${YELLOW}SKIP${NC} — no .provided_hash file found"
        return 0
    fi
    local current_hash
    current_hash=$(extract_provided_hash "$TASK_FILE")
    local expected_hash
    expected_hash=$(cat .provided_hash)
    if [[ "$current_hash" == "$expected_hash" ]]; then
        echo -e "${GREEN}PASS${NC} integrity — provided sections unchanged"
        return 0
    else
        echo -e "${RED}FAIL${NC} integrity — provided sections were modified"
        return 1
    fi
}

check_compile() {
    local output
    if output=$(lake lean "$TASK_FILE" 2>&1); then
        echo -e "${GREEN}PASS${NC} verify — compiles"
        return 0
    else
        echo -e "${RED}FAIL${NC} verify — compilation error"
        echo "$output" | head -20
        return 1
    fi
}

check_no_stubs() {
    if grep -qE '\b(sorry|sorryAx)\b' "$TASK_FILE"; then
        echo -e "${YELLOW}INCOMPLETE${NC} stubs — contains sorry or sorryAx"
        return 1
    fi
    echo -e "${GREEN}PASS${NC} stubs — no sorry found"
    return 0
}

check_no_cheats() {
    local editable
    editable=$(extract_editable)
    if [[ -z "$editable" ]]; then
        return 0
    fi

    # --- Proof holes ---
    # admit: equivalent to sorry but not caught by the sorry check
    # admitGoal: metaprogramming escape to admit goals during elaboration
    # sorryAx: internal axiom that sorry compiles to; bypasses \bsorry\b grep
    # sorry_proof: Lean internal sorry proof term
    # lcProof: low-level proof constructor that can fabricate proofs
    local proof_hole_patterns=(
        '\badmit\b'
        'admitGoal'
        '\bsorryAx\b'
        '\bsorry_proof\b'
        '\blcProof\b'
    )

    for pat in "${proof_hole_patterns[@]}"; do
        if echo "$editable" | grep -qE "$pat"; then
            echo -e "${RED}FAIL${NC} soundness — forbidden proof hole: $pat"
            return 1
        fi
    done

    # --- Axiom abuse ---
    # User-defined axioms in editable sections bypass proof obligations.
    # Catch both `axiom` and `private axiom` (the private keyword hid it
    # from the previous ^\s*axiom pattern).
    if echo "$editable" | grep -qE '^\s*(private\s+)?axiom\b'; then
        echo -e "${RED}FAIL${NC} soundness — forbidden: user-defined axiom in editable section"
        return 1
    fi

    # --- Brute-force / decidability abuse ---
    # These construct Fintype/Decidable/Finite instances on large types
    # (BitVec 64, Tnum, RegState) to enable enumeration-based "proofs"
    # that are computationally infeasible but type-check.
    # Also catches aliasing tricks (e.g. renaming inGamma) and multi-line
    # Decidable constructions by banning the class names outright.
    local bruteforce_patterns=(
        '\bDecidable\b'
        '\bFintype\b'
        '\bFinite\b'
        'Fin \(2 \^'
        'Classical\.'
        '\bnoncomputable\b'
        '\bnative_decide\b'
        '\bTestable\b'
        '\bplausible\b'
    )

    for pat in "${bruteforce_patterns[@]}"; do
        if echo "$editable" | grep -qE "$pat"; then
            echo -e "${RED}FAIL${NC} complexity — forbidden brute-force pattern: $pat"
            return 1
        fi
    done

    echo -e "${GREEN}PASS${NC} soundness — no cheats found"
    return 0
}

mode="full"
for arg in "$@"; do
    case "$arg" in
        --compile) mode="compile" ;;
        --check-integrity) mode="integrity" ;;
    esac
done

fail=0

case "$mode" in
    compile)
        check_compile || fail=1
        ;;
    integrity)
        check_integrity || fail=1
        ;;
    full)
        check_integrity || fail=1
        check_no_cheats || fail=1
        check_compile || fail=1
        check_no_stubs || fail=1
        ;;
esac

exit $fail
