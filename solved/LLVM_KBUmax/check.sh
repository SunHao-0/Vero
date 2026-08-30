#!/usr/bin/env bash
#   ./check.sh                       # verify + stubs + integrity + cheats
#   ./check.sh --compile             # sorry stubs OK
#   ./check.sh --check-integrity     # check provided sections unchanged
#   ./check.sh --cheats-only [FILE]  # run cheat detection only (FILE defaults to Task.lean)
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

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

# Extract just the IMPLEMENTATION section.
extract_implementation() {
    sed -n '/=== BEGIN: IMPLEMENTATION/,/=== END: IMPLEMENTATION/p' "$TASK_FILE"
}

# Extract everything OUTSIDE of `(provided)` sections, i.e. every byte the
# solver could have touched — both editable sections and the unchecked gaps
# between sections. Used for widened cheat scanning.
extract_non_provided() {
    awk '
        /=== BEGIN:.*\(provided\)/ { in_prov=1; next }
        in_prov && /=== END:/       { in_prov=0; next }
        !in_prov                    { print }
    ' "$TASK_FILE"
}

# Strip Lean comments (`--` to EOL and `/- … -/` block comments, nested OK).
# Preserves line numbers where feasible to keep grep output diagnostic.
strip_comments() {
    awk '
        BEGIN { depth=0 }
        {
            line=$0
            out=""
            i=1
            len=length(line)
            while (i<=len) {
                if (depth==0 && substr(line,i,2)=="--") {
                    break  # rest of line is a comment
                } else if (substr(line,i,2)=="/-") {
                    depth++; i+=2
                } else if (depth>0 && substr(line,i,2)=="-/") {
                    depth--; i+=2
                } else {
                    if (depth==0) out = out substr(line,i,1)
                    i++
                }
            }
            print out
        }
    '
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
    output=$(lake lean "$TASK_FILE" 2>&1)
    local exit_code=$?

    if [[ $exit_code -ne 0 ]]; then
        echo -e "${RED}FAIL${NC} verify — compilation error"
        echo "$output" | head -40
        return 1
    fi

    # Even when compilation succeeds, Lean reports sorry usage via kernel
    # warnings. This catches metaprogramming cheats that construct sorryAx
    # dynamically (e.g. Name.str .anonymous ("sor" ++ "ryAx")).
    local sorry_lines
    sorry_lines=$(echo "$output" | grep "declaration uses 'sorry'")
    if [[ -n "$sorry_lines" ]]; then
        echo -e "${RED}FAIL${NC} verify — compiles but sorry detected in output (metaprogramming cheat)"
        echo "$sorry_lines" | head -10
        return 1
    fi

    echo -e "${GREEN}PASS${NC} verify — compiles"
    return 0
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
    # Two scan scopes:
    #   - `scan_wide`: all text NOT inside a (provided) section, comments
    #     stripped. Used for patterns that are forbidden anywhere the
    #     solver could have written them (including the unchecked gaps
    #     between provided sections — see cheating_patterns.md #5).
    #   - `scan_impl`: just the IMPLEMENTATION block, comments stripped.
    #     Used for patterns that are only illegal inside the implementation
    #     (quantifiers, γ-mentions, `.choose`, etc.).
    local scan_wide scan_impl scan_editable
    scan_wide=$(extract_non_provided    | strip_comments)
    scan_impl=$(extract_implementation  | strip_comments)
    scan_editable=$(extract_editable    | strip_comments)

    if [[ -z "$scan_editable" ]]; then
        return 0
    fi

    _fail() {
        echo -e "${RED}FAIL${NC} $1 — $2"
        return 1
    }

    # --- Early exit ---
    # #exit stops Lean from processing the rest of the file, so everything
    # after it (SPEC, THEOREM, PROOF) is silently skipped.
    if echo "$scan_wide" | grep -qE '^\s*#exit\b'; then
        _fail soundness "forbidden: #exit outside provided sections"
        return 1
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
        if echo "$scan_wide" | grep -qE "$pat"; then
            _fail soundness "forbidden proof hole: $pat"
            return 1
        fi
    done

    # --- Axiom abuse (source-level) ---
    if echo "$scan_wide" | grep -qE '^\s*(private\s+|protected\s+)?axiom\b'; then
        _fail soundness "forbidden: user-defined axiom outside provided sections"
        return 1
    fi

    # --- Metaprogramming axiom injection ---
    local meta_axiom_patterns=(
        '\baddDecl\b'
        '\.axiomDecl\b'
    )
    for pat in "${meta_axiom_patterns[@]}"; do
        if echo "$scan_wide" | grep -qE "$pat"; then
            _fail soundness "forbidden metaprogramming axiom injection: $pat"
            return 1
        fi
    done

    # --- Command / syntax hijacking ---
    #
    # `syntax` + `elab_rules` (or `macro_rules`) can **redeclare** an
    # existing command so that the declaration captures dispatch ahead of
    # the built-in handler. Seen in the wild as:
    #
    #     syntax (name := breakAxiomCheck) "#print" " axioms " ident : command
    #     elab_rules (kind := breakAxiomCheck) : command
    #       | `(#print axioms $id:ident) => pure ()
    #
    # This silently no-ops Lean's `#print axioms`, so the `check_axioms`
    # step in check.sh (which re-runs `lake lean` with an appended
    # `#print axioms <theorem>`) produces no "depends on axioms" output
    # and the kernel-level axiom check trivially "passes". The same
    # trick can be used to hijack any command (`#check`, `#eval`,
    # `theorem`, even `def`) or any term-level notation.
    #
    # Honest solutions NEVER need `syntax` / `macro` / `elab` machinery —
    # they are pure definitions and proofs. Blanket-ban any occurrence
    # outside provided sections. `notation3` and plain `notation` are
    # also included because they can rebind operators the checker or
    # tests depend on.
    local meta_command_patterns=(
        '^\s*(private\s+|protected\s+|scoped\s+|local\s+)*syntax\b'
        '^\s*(private\s+|protected\s+|scoped\s+|local\s+)*macro\b'
        '^\s*(private\s+|protected\s+|scoped\s+|local\s+)*macro_rules\b'
        '^\s*(private\s+|protected\s+|scoped\s+|local\s+)*elab\b'
        '^\s*(private\s+|protected\s+|scoped\s+|local\s+)*elab_rules\b'
        '^\s*(private\s+|protected\s+|scoped\s+|local\s+)*notation3?\b'
        '@\[\s*(command|term|tactic)_elab\b'
        '@\[\s*builtin_(command|term|tactic)_elab\b'
        '\bCommandElabM\b'
        '\bTermElabM\b'
        '\bTacticElabM\b'
        '\bLean\.Elab\b'
        '\bLean\.Macro\b'
        '\bLean\.Syntax\b'
    )
    for pat in "${meta_command_patterns[@]}"; do
        if echo "$scan_wide" | grep -qE "$pat"; then
            _fail soundness "forbidden metaprogramming / command hijack: $pat"
            return 1
        fi
    done

    # --- Brute-force / decidability / nonconstructive abuse ---
    #
    # These patterns are forbidden anywhere in the solver-writable surface
    # (editable sections + gaps between provided sections). Scanned after
    # stripping comments so docstrings mentioning "Classical" etc. are safe.
    #
    # Notes on each pattern:
    #   \bDecidable\b, \bDecidableEq\b, \bDecidablePred\b
    #       Constructing decidability instances over γ is how Pattern 1
    #       (spec-mirror `if`) is made to typecheck.
    #   \bFintype\b, \bFinite\b
    #       Enables Finset.univ over BitVec n (Pattern 3).
    #   Fin\s*\(\s*2\s*\^
    #       The Fintype.ofEquiv trick; tolerant of any whitespace so
    #       `Fin (2^32)`, `Fin ( 2 ^ 64 )` etc. all match.
    #   \bClassical\.[A-Za-z]   AND   \bopen\s+Classical\b
    #       `Classical.propDecidable`, `Classical.choose`, `Classical.dec`,
    #       etc. PLUS bare `open Classical in …` which slipped through the
    #       previous regex.
    #   \bnoncomputable\b
    #       Any `noncomputable def`, `noncomputable section`, etc. — there
    #       is no legitimate reason for a solver to mark anything
    #       noncomputable in an implementation task.
    #   \bnative_decide\b, \bTestable\b, \bplausible\b
    #       Runtime decision procedures / test frameworks abuse.
    #   \bFinset\.univ\b
    #       Strong signal of brute-force enumeration over a finite type.
    #   \bNat\.find\b, \bNat\.findGreatest\b
    #       Pattern 4: minimize/maximize a classical predicate.
    #   decide\s*\(\s*[∃∀] / decide\s*\(\s*(Exists|Forall)
    #       Pattern 7 (LLVM DBMul): `decide` applied to a quantifier is a
    #       spec-mirror that relies on the auto-synthesized Fintype instance
    #       for BitVec n to enumerate 2^n values. The literal `Fintype` /
    #       `Decidable` tokens are absent because the instance is implicit,
    #       so the other patterns miss it. Any honest implementation
    #       applies `decide` only to simple boolean propositions, never to
    #       a quantifier.
    local bruteforce_patterns=(
        '\bDecidable\b'
        '\bDecidableEq\b'
        '\bDecidablePred\b'
        '\bFintype\b'
        '\bFinite\b'
        'Fin\s*\(\s*2\s*\^'
        '\bClassical\.[A-Za-z]'
        '\bopen\s+Classical\b'
        '\bnoncomputable\b'
        '\bnative_decide\b'
        '\bTestable\b'
        '\bplausible\b'
        '\bFinset\.univ\b'
        '\bNat\.find\b'
        '\bNat\.findGreatest\b'
        '\bdecide\s*\(\s*[∃∀]'
        '\bdecide\s*\(\s*(Exists|Forall)\b'
        '\bDecidable\.decide\s*\(\s*[∃∀]'
    )
    for pat in "${bruteforce_patterns[@]}"; do
        if echo "$scan_wide" | grep -qE "$pat"; then
            _fail complexity "forbidden brute-force / nonconstructive pattern: $pat"
            return 1
        fi
    done

    # --- Implementation-only restrictions ---
    #
    # The following are *only* rejected inside the IMPLEMENTATION block.
    # They are legal in PROOF / AUX (a proof may legitimately use
    # `Classical.choose_spec`, quantifiers, reference γ, etc.).
    #
    # Notes:
    #   (∀|∃|\\bforall\\b|\\bexists\\b)
    #       Pattern 1 (spec-mirroring `if ∀ x y, … then …`). A real
    #       constructive implementation of a best-abstract-transformer
    #       should never need to *name* a universal or existential
    #       quantifier — it works on the components of the abstract state.
    #   \b(inGamma|satisfiesTnum(32|64)?)\b
    #       Pattern 1/2: the implementation should operate on abstract
    #       state fields (`reg.umin_value`, `reg.var_off.value`, …), never
    #       on the γ relation itself.
    #   \.choose\b, \.choose_spec\b
    #       Pattern 2: `h.choose` from an existence witness is the hallmark
    #       of the "let Classical pick the answer" cheat.
    #   \bby\b
    #       Tactic mode inside the implementation is disallowed by the
    #       task rules (see INSTRUCTION.md rule 5).
    local impl_only_patterns=(
        '∀|∃|\\bforall\\b|\\bexists\\b'
        '\b(inGamma|satisfiesTnum|satisfiesTnum32|satisfiesTnum64)\b'
        '\.choose\b'
        '\.choose_spec\b'
        '\bconcrete[A-Z]\w*\b'
    )
    local impl_only_names=(
        'quantifier in implementation (Pattern 1 — spec-mirroring if)'
        'γ / satisfiesTnum reference in implementation (Pattern 1/2 — spec-mirroring)'
        'Classical.choose-style witness extraction in implementation (Pattern 2)'
        'Classical.choose_spec in implementation (Pattern 2)'
        'call to concrete* operator in implementation (brute-force enumeration over γ — the abstract transformer must not invoke the concrete op)'
    )
    local i
    for i in "${!impl_only_patterns[@]}"; do
        if echo "$scan_impl" | grep -qE "${impl_only_patterns[$i]}"; then
            _fail soundness "forbidden ${impl_only_names[$i]}"
            return 1
        fi
    done

    # Tactic mode in implementation: rule-based disallow, but we must be
    # careful — `\bby\b` could match an identifier containing "by". Look
    # for `:=\s*by\b` or leading-whitespace `\bby\b` at start of a line.
    if echo "$scan_impl" | grep -qE '(:=|↦|=>|\bdo\b)\s*by\b|^\s*by\b'; then
        _fail soundness "forbidden tactic mode (\`by\`) in implementation"
        return 1
    fi

    echo -e "${GREEN}PASS${NC} soundness — no cheats found"
    return 0
}

check_axioms() {
    # Kernel-level axiom check: verify the theorem only depends on standard
    # Lean 4 axioms (propext, Classical.choice, Quot.sound). This catches ALL
    # forms of axiom injection — direct `axiom`, metaprogramming elab/macro,
    # or any future creative exploit — because it checks the compiled kernel
    # output, not source-level patterns.

    # Extract theorem name(s) from THEOREM provided section
    local theorem_names
    theorem_names=$(sed -n '/=== BEGIN: THEOREM/,/=== END: THEOREM/p' "$TASK_FILE" \
                    | grep -oP 'theorem\s+\K\w+')
    if [[ -z "$theorem_names" ]]; then
        echo -e "${YELLOW}SKIP${NC} axioms — no theorem found in THEOREM section"
        return 0
    fi

    # Resolve namespace prefix (e.g. "BPF" → "BPF.theorem_name")
    local ns_prefix=""
    local ns
    ns=$(grep -oP '^\s*namespace\s+\K\S+' "$TASK_FILE" | head -1)
    if [[ -n "$ns" ]]; then
        ns_prefix="${ns}."
    fi

    # Create temp file: Task.lean + #print axioms for each theorem
    local tmp_file="${TASK_FILE%.lean}_axiom_check.lean"
    cp "$TASK_FILE" "$tmp_file"
    while IFS= read -r name; do
        echo "#print axioms ${ns_prefix}${name}" >> "$tmp_file"
    done <<< "$theorem_names"

    local output
    output=$(lake lean "$tmp_file" 2>&1)
    local exit_code=$?
    rm -f "$tmp_file"

    if [[ $exit_code -ne 0 ]]; then
        # Compilation failed — will be caught by check_compile
        echo -e "${YELLOW}SKIP${NC} axioms — compilation failed (deferred to verify step)"
        return 0
    fi

    # Allowed axioms: the three standard Lean 4 axioms
    local allowed="propext|Classical\.choice|Quot\.sound"

    # Parse #print axioms output and check for non-standard axioms
    local bad_axioms
    bad_axioms=$(echo "$output" \
        | grep "depends on axioms" \
        | sed 's/.*\[//; s/\]//' \
        | tr ',' '\n' \
        | sed 's/^ *//; s/ *$//' \
        | grep -vE "^($allowed)$" \
        | grep -v '^$' \
        | sort -u)

    if [[ -n "$bad_axioms" ]]; then
        echo -e "${RED}FAIL${NC} axioms — non-standard axioms detected:"
        echo "$bad_axioms"
        return 1
    fi

    echo -e "${GREEN}PASS${NC} axioms — only standard axioms"
    return 0
}

mode="full"
cheats_target=""
positional=()
for arg in "$@"; do
    case "$arg" in
        --compile) mode="compile" ;;
        --check-integrity) mode="integrity" ;;
        --cheats-only) mode="cheats" ;;
        --*) echo "unknown flag: $arg" >&2; exit 2 ;;
        *) positional+=("$arg") ;;
    esac
done

if [[ "$mode" == "cheats" && ${#positional[@]} -ge 1 ]]; then
    cheats_target="${positional[0]}"
fi

if [[ -n "$cheats_target" ]]; then
    # When given an explicit file, resolve it and run in its directory so
    # `Task.lean` / `.provided_hash` lookups still work.
    if [[ ! -f "$cheats_target" ]]; then
        echo "file not found: $cheats_target" >&2
        exit 2
    fi
    TASK_FILE="$(basename "$cheats_target")"
    cd "$(dirname "$cheats_target")"
else
    cd "$SCRIPT_DIR"
fi

fail=0

case "$mode" in
    compile)
        check_compile || fail=1
        ;;
    integrity)
        check_integrity || fail=1
        ;;
    cheats)
        check_no_cheats || fail=1
        ;;
    full)
        check_integrity || fail=1
        check_no_stubs || fail=1
        check_no_cheats || fail=1
        check_compile || fail=1
        check_axioms || fail=1
        ;;
esac

exit $fail
