#!/usr/bin/env bash
#   ./check.sh                        verify + stubs + integrity + cheats + axioms
#   ./check.sh --compile              compile only (sorry allowed)
#   ./check.sh --check-integrity      hash-check provided sections
#   ./check.sh --cheats-only [FILE]   cheat scan only (FILE: defaults to Task.lean)
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TASK_FILE="Task.lean"

RED='\033[0;31m'; GREEN='\033[0;32m'; YELLOW='\033[0;33m'; NC='\033[0m'

# ---------------------------------------------------------------------------
# Section extraction
#
# Task.lean is partitioned by "-- === BEGIN: NAME (provided|editable) ===" /
# "-- === END: NAME ===" markers. The hash only covers provided sections, so
# we also carve out everything outside them (gaps included) for cheat scans.
# ---------------------------------------------------------------------------

extract_provided_hash() {
    sed -n '/=== BEGIN:.*provided/,/=== END:/p' "$1" | sha256sum | cut -d' ' -f1
}

extract_editable()       { sed -n '/=== BEGIN:.*editable/,/=== END:/p'                     "$TASK_FILE"; }
extract_implementation() { sed -n '/=== BEGIN: IMPLEMENTATION/,/=== END: IMPLEMENTATION/p' "$TASK_FILE"; }

# IMPLEMENTATION + AUX — the non-proof writable surface. Proof tactics may
# legitimately mention γ / `decide`, helpers must not.
extract_impl_and_aux() {
    sed -n '/=== BEGIN: IMPLEMENTATION/,/=== END: IMPLEMENTATION/p;
            /=== BEGIN: AUX/,/=== END: AUX/p' "$TASK_FILE"
}

# Everything outside `(provided)` sections, including gaps. Gaps are not
# hashed and have historically hidden `noncomputable section` / axiom decls.
extract_non_provided() {
    awk '/=== BEGIN:.*provided/ { in_prov=1; next }
         in_prov && /=== END:/      { in_prov=0; next }
         !in_prov'                                       "$TASK_FILE"
}

# Strip `--` line comments and `/- ... -/` block comments (nesting supported),
# and drop the contents of `"..."` string literals. String awareness is
# essential: a `"/-"` / `"--"` inside a string must NOT be read as a comment
# delimiter, otherwise a solver can desync this scanner from Lean's lexer and
# hide live code from every cheat grep (the `_openDesync := "/-"` … `"-/"`
# attack). Soundness-critical tokens are additionally scanned on the RAW
# (un-stripped) surface in check_no_cheats, so no lexer trick can hide them.
strip_comments() {
    awk '
        BEGIN { depth=0 }
        {
            out=""; i=1; len=length($0)
            while (i<=len) {
                if (depth>0) {                                  # inside block comment
                    if (substr($0,i,2)=="-/")      { depth--; i+=2 }
                    else if (substr($0,i,2)=="/-") { depth++; i+=2 }
                    else i++
                }
                else if (substr($0,i,2)=="--") break            # line comment
                else if (substr($0,i,2)=="/-") { depth++; i+=2 } # block comment open
                else if (substr($0,i,1)=="\"") {                # string literal: skip contents
                    i++
                    while (i<=len) {
                        if (substr($0,i,1)=="\\")      i+=2      # escape: skip next char
                        else if (substr($0,i,1)=="\"") { i++; break }
                        else i++
                    }
                }
                else { out = out substr($0,i,1); i++ }
            }
            print out
        }'
}

# ---------------------------------------------------------------------------
# Individual checks
# ---------------------------------------------------------------------------

check_integrity() {
    if [[ ! -f .provided_hash ]]; then
        echo -e "${YELLOW}SKIP${NC} integrity — no .provided_hash file"
        return 0
    fi
    if [[ "$(extract_provided_hash "$TASK_FILE")" == "$(cat .provided_hash)" ]]; then
        echo -e "${GREEN}PASS${NC} integrity — provided sections unchanged"
        return 0
    fi
    echo -e "${RED}FAIL${NC} integrity — provided sections were modified"
    return 1
}

check_compile() {
    local output
    output=$(lake lean "$TASK_FILE" 2>&1)
    if [[ $? -ne 0 ]]; then
        echo -e "${RED}FAIL${NC} verify — compilation error"
        echo "$output" | head -40
        return 1
    fi
    # Metaprogramming can fabricate sorryAx post-elaboration; the kernel still
    # emits a "declaration uses 'sorry'" warning even if no literal `sorry`.
    if echo "$output" | grep -q "declaration uses 'sorry'"; then
        echo -e "${RED}FAIL${NC} verify — compiles but kernel reports sorry (metaprogramming cheat)"
        echo "$output" | grep "declaration uses 'sorry'" | head -10
        return 1
    fi
    echo -e "${GREEN}PASS${NC} verify — compiles"
}

check_no_stubs() {
    if grep -qE '\b(sorry|sorryAx)\b' "$TASK_FILE"; then
        echo -e "${YELLOW}INCOMPLETE${NC} stubs — contains sorry or sorryAx"
        return 1
    fi
    echo -e "${GREEN}PASS${NC} stubs — no sorry found"
}

# ---------------------------------------------------------------------------
# Cheat detection
# ---------------------------------------------------------------------------

check_no_cheats() {
    local scan_wide scan_wide_raw scan_impl scan_editable scan_non_proof
    # scan_wide_raw is the writable surface WITHOUT comment/string stripping.
    # Soundness-critical patterns (below) are scanned on it so that a
    # string-literal or comment desync in strip_comments cannot hide them. The
    # tokens scanned raw never appear in an honest solution — in code, a
    # comment, or a string — so raw matching has no real false positives.
    scan_wide_raw=$(extract_non_provided)
    scan_wide=$(     extract_non_provided    | strip_comments)
    scan_impl=$(     extract_implementation  | strip_comments)
    scan_editable=$( extract_editable        | strip_comments)
    scan_non_proof=$(extract_impl_and_aux    | strip_comments)

    [[ -z "$scan_editable" ]] && return 0

    _fail() { echo -e "${RED}FAIL${NC} $1 — $2"; return 1; }
    _scan() {
        # _scan <scope> <category> <label> <pattern>
        if echo "$1" | grep -qE "$4"; then
            _fail "$2" "$3"
            return 1
        fi
    }

    # `#exit` halts elaboration before the theorem — it would never be checked.
    _scan "$scan_wide_raw" soundness "forbidden: #exit outside provided sections" \
          '^\s*#exit\b' || return 1

    # Proof holes (admit, sorryAx, lcProof, …) — bypass \bsorry\b alone.
    local p
    for p in '\badmit\b' 'admitGoal' '\bsorryAx\b' '\bsorry_proof\b' '\blcProof\b'; do
        _scan "$scan_wide_raw" soundness "forbidden proof hole: $p" "$p" || return 1
    done

    # User `axiom`. Matches plain, attributed (`@[simp] axiom`), or `private axiom`.
    _scan "$scan_wide_raw" soundness "forbidden: user-defined axiom outside provided sections" \
          '\baxiom\s+[A-Za-z_]' || return 1

    # Metaprogramming axiom injection (addDecl, .axiomDecl).
    for p in '\baddDecl\b' '\.axiomDecl\b'; do
        _scan "$scan_wide_raw" soundness "forbidden metaprogramming axiom injection: $p" "$p" || return 1
    done

    # Command/syntax hijack. `syntax`+`elab_rules` can redeclare `#print axioms`
    # to a no-op, silently defeating the kernel axiom check. Honest solutions
    # never need macro/elab machinery. Raw-scanned: this is what could disable
    # the axiom backstop, so it must be impossible to hide.
    local meta_cmd=(
        '^\s*(private\s+|protected\s+|scoped\s+|local\s+)*syntax\b'
        '^\s*(private\s+|protected\s+|scoped\s+|local\s+)*macro\b'
        '^\s*(private\s+|protected\s+|scoped\s+|local\s+)*macro_rules\b'
        '^\s*(private\s+|protected\s+|scoped\s+|local\s+)*elab\b'
        '^\s*(private\s+|protected\s+|scoped\s+|local\s+)*elab_rules\b'
        '^\s*(private\s+|protected\s+|scoped\s+|local\s+)*notation3?\b'
        '@\[\s*(command|term|tactic)_elab\b'
        '@\[\s*builtin_(command|term|tactic)_elab\b'
        '\b(CommandElabM|TermElabM|TacticElabM)\b'
        '\bLean\.(Elab|Macro|Syntax)\b'
    )
    for p in "${meta_cmd[@]}"; do
        _scan "$scan_wide_raw" soundness "forbidden metaprogramming / command hijack: $p" "$p" || return 1
    done

    # Manual native-evaluation / compiler-trust escapes. `bv_decide` is
    # allowed (check_axioms whitelists its Lean.ofReduceBool /
    # Lean.trustCompiler axioms), but invoking the same machinery by hand
    # — especially combined with @[implemented_by] / @[extern] overrides
    # of the evaluated functions — can "prove" false statements while
    # depending only on the whitelisted axioms. Raw-scanned: these bypass the
    # axiom backstop, so they must be impossible to hide.
    local native=(
        '\b(ofReduceBool|ofReduceNat|reduceBool|reduceNat)\b'
        '\btrustCompiler\b'
        '\bimplemented_by\b'
        '\bextern\b'
        '\bnative_decide\b'
    )
    for p in "${native[@]}"; do
        _scan "$scan_wide_raw" soundness "forbidden native-code trust escape: $p" "$p" || return 1
    done

    # Brute-force / nonconstructive abuse across the whole writable surface.
    # Example: `decide (∃ x : BitVec 64, …)` forces enumeration over 2^64 values
    # via an auto-synthesized Fintype instance.
    local brute=(
        '\bDecidable(Eq|Pred)?\b'
        '\b(Fintype|Finite)\b'
        'Fin\s*\(\s*2\s*\^'
        'List\.range\s*\(\s*2\s*\^'
        '\bClassical\.[A-Za-z]'
        '\bopen\s+Classical\b'
        '\bnoncomputable\b'
        '\b(native_decide|Testable|plausible)\b'
        '\bFinset\.univ\b'
        '\bNat\.find(Greatest)?\b'
        '\b(decide|Decidable\.decide)\s*\(\s*[∃∀]'
        '\bdecide\s*\(\s*(Exists|Forall)\b'
    )
    for p in "${brute[@]}"; do
        _scan "$scan_wide" complexity "forbidden brute-force / nonconstructive pattern: $p" "$p" || return 1
    done

    # IMPLEMENTATION-only: must compute on abstract-state fields, never name γ
    # or quantify over it. Pi-type `(x : T) → …` is the Lean-equivalent of ∀
    # without the symbol — catches `if (x : BitVec 64) → … then` spec-mirrors.
    local impl_pat=(
        '∀|∃|\b(forall|exists|Forall|Exists)\b'
        '\([A-Za-z_]\w*\s*:\s*[^)]+\)\s*(→|->)'
        '\b(inGamma|satisfiesTnum|satisfiesTnum32|satisfiesTnum64)\b'
        '\.choose\b'
        '\.choose_spec\b'
        '\bconcrete[A-Z]\w*\b'
    )
    local impl_msg=(
        'quantifier in implementation (spec-mirroring)'
        'Pi-type binder `(x : T) →` in implementation (quantifier evasion)'
        'γ / satisfiesTnum reference in implementation (spec-mirroring)'
        '`.choose` witness extraction in implementation'
        '`.choose_spec` in implementation'
        'call to concrete* operator in implementation'
    )
    local i
    for i in "${!impl_pat[@]}"; do
        _scan "$scan_impl" soundness "forbidden ${impl_msg[$i]}" "${impl_pat[$i]}" || return 1
    done

    # Tactic mode in IMPLEMENTATION (bare `by`, or `:= by`, `=> by`, etc.)
    _scan "$scan_impl" soundness "forbidden tactic mode (\`by\`) in implementation" \
          '(:=|↦|=>|\bdo\b)\s*by\b|^\s*by\b' || return 1

    # IMPL+AUX spec-mirror via `decide (namedProp arg …)`. Legitimate
    # `decide (x ≤ y)` has a relational operator after the first ident and
    # does not match. PROOF is allowed — proofs may reason about `decide foo`.
    _scan "$scan_non_proof" soundness \
          "forbidden: \`decide (<namedProp> …)\` in IMPL/AUX (boolified spec-mirror)" \
          '\bdecide\s*\(\s*[A-Za-z_][A-Za-z0-9_.]*\s+[A-Za-z_(]' || return 1

    echo -e "${GREEN}PASS${NC} soundness — no cheats found"
}

# Kernel-level axiom check: re-run `lake lean` with `#print axioms <thm>`
# appended, then reject any axiom other than:
#   - the three standard Lean 4 ones (propext, Classical.choice, Quot.sound),
#   - Lean.ofReduceBool / Lean.trustCompiler, which `bv_decide` introduces
#     via its verified-but-natively-executed LRAT certificate checker
#     (manually invoking that machinery is separately forbidden by the
#     cheat scan: reduceBool / implemented_by / extern), and
#   - axioms declared inside the task's own provided AXIOMS section
#     (e.g. tnumStepUp), which the instructions explicitly permit.
# This is the backstop — it catches any exotic axiom injection the
# source-level regexes miss.
check_axioms() {
    # Theorem declarations live in whichever `(provided)` block the task
    # template chose — `THEOREM`, `SPEC`, or `SPEC_CORRECT`.
    local theorem_names
    theorem_names=$(awk '
        /=== BEGIN:.*provided/ { in_prov=1; next }
        in_prov && /=== END:/      { in_prov=0; next }
        in_prov' "$TASK_FILE" | grep -oP 'theorem\s+\K\w+')
    if [[ -z "$theorem_names" ]]; then
        echo -e "${YELLOW}SKIP${NC} axioms — no theorem found in provided sections"
        return 0
    fi

    local ns ns_prefix=""
    ns=$(grep -oP '^\s*namespace\s+\K\S+' "$TASK_FILE" | head -1)
    [[ -n "$ns" ]] && ns_prefix="${ns}."

    local tmp_file="${TASK_FILE%.lean}_axiom_check.lean"
    cp "$TASK_FILE" "$tmp_file"
    while IFS= read -r name; do
        echo "#print axioms ${ns_prefix}${name}" >> "$tmp_file"
    done <<< "$theorem_names"

    local output
    output=$(lake lean "$tmp_file" 2>&1)
    local rc=$?
    rm -f "$tmp_file"
    if [[ $rc -ne 0 ]]; then
        # `verify` compiles Task.lean separately; if appending the
        # `#print axioms` lines makes compilation fail, a target theorem name
        # did not resolve (e.g. a `#exit` skipped it, a namespace mismatch, or
        # a renamed theorem). This must NOT silently pass — otherwise the
        # backstop can be disabled by making the theorem unresolvable.
        echo -e "${RED}FAIL${NC} axioms — '#print axioms' did not run (unresolved theorem or compile error)"
        echo "$output" | grep -iE 'error' | head -10
        return 1
    fi

    # Flatten once: Lean pretty-prints long axiom lists across multiple lines,
    # so a line-based grep would only ever see the first element.
    local flat
    flat=$(echo "$output" | tr '\n' ' ')

    # Every target theorem must actually be reported on. A missing report means
    # the backstop did not check that theorem (defense in depth against the
    # unresolved-name path above).
    local name
    while IFS= read -r name; do
        [[ -z "$name" ]] && continue
        if ! echo "$flat" | grep -qF "'${ns_prefix}${name}'"; then
            echo -e "${RED}FAIL${NC} axioms — no report for ${ns_prefix}${name} (backstop did not run)"
            return 1
        fi
    done <<< "$theorem_names"

    local allowed='propext|Classical\.choice|Quot\.sound|Lean\.ofReduceBool|Lean\.trustCompiler'

    # Axioms declared in the task's provided sections are part of the task
    # and legal for proofs to use. Allow them under the file's namespace.
    local task_axioms ax
    task_axioms=$(awk '
        /=== BEGIN:.*provided/ { in_prov=1; next }
        in_prov && /=== END:/      { in_prov=0; next }
        in_prov' "$TASK_FILE" | grep -oP '^\s*axiom\s+\K\w+' | sort -u)
    for ax in $task_axioms; do
        allowed="${allowed}|${ns_prefix//./\\.}${ax}"
    done

    local bad
    bad=$(echo "$flat" \
          | grep -oP 'depends on axioms: \[\K[^]]*' \
          | tr ',' '\n' | sed 's/^ *//; s/ *$//' \
          | grep -vE "^(${allowed})$" | grep -v '^$' | sort -u)
    if [[ -n "$bad" ]]; then
        echo -e "${RED}FAIL${NC} axioms — non-standard axioms detected:"
        echo "$bad"
        return 1
    fi
    echo -e "${GREEN}PASS${NC} axioms — only standard axioms"
}

# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

mode="full"
positional=()
for arg in "$@"; do
    case "$arg" in
        --compile)         mode="compile"   ;;
        --check-integrity) mode="integrity" ;;
        --cheats-only)     mode="cheats"    ;;
        --*) echo "unknown flag: $arg" >&2; exit 2 ;;
        *)   positional+=("$arg") ;;
    esac
done

# --cheats-only may take an explicit target file; run from its directory so
# the script still finds Task.lean / .provided_hash relative lookups.
if [[ "$mode" == "cheats" && ${#positional[@]} -ge 1 ]]; then
    target="${positional[0]}"
    [[ -f "$target" ]] || { echo "file not found: $target" >&2; exit 2; }
    TASK_FILE="$(basename "$target")"
    cd "$(dirname "$target")"
else
    cd "$SCRIPT_DIR"
fi

fail=0
case "$mode" in
    compile)   check_compile    || fail=1 ;;
    integrity) check_integrity  || fail=1 ;;
    cheats)    check_no_cheats  || fail=1 ;;
    full)
        check_integrity  || fail=1
        check_no_stubs   || fail=1
        check_no_cheats  || fail=1
        check_compile    || fail=1
        check_axioms     || fail=1
        ;;
esac
exit $fail
