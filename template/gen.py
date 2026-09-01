"""
Template expansion for Lean4 verification task generation.

Layout:
  template/
    gen.py                         ← this script
    AluOp.lean, BranchTaken.lean,  ← Task.lean templates (eBPF/LLVM)
    RefineCond.lean, ...
    seL4/<Name>/Task.lean          ← direct task sources (seL4)
    eBPF/<Name>/Task.lean          ← direct task sources (eBPF, e.g. TnumStepUp)
    task_dir/                      ← skeleton copied into each task dir
      check_template.sh
      instruction_template.md
      lakefile.lean
      lean-toolchain
      lake-manifest.json

Generated tasks go to <output>/<category>_<TaskName>/ — e.g.
eBPF_Cnum_Alu64Add, LLVM_KBUdiv, seL4_FindFreeHWASID. eBPF/LLVM tasks
expand from the .lean templates; direct tasks copy their hand-maintained
Task.lean from template/<category>/<Name>/. tasks/ is therefore fully
regenerable: delete it and run the generator to rebuild everything.

Each task directory contains:
  - Task.lean        (Lean4 source with section markers)
  - lakefile.lean    (Lake project config, per-task package name)
  - lean-toolchain   (Lean version pinning)
  - lake-manifest.json (Pinned Mathlib + transitive dependencies)
  - check.sh         (verification + integrity check script)
  - .provided_hash   (SHA256 of provided sections for integrity checking)
  - INSTRUCTION.md   (task description and rules)
"""

import hashlib
import re
import shutil
import stat
from pathlib import Path
from typing import Dict


def _lean_name(parts):
    """Convert parts to PascalCase Lean name: ['jmp64', 'eq'] -> 'Jmp64Eq'"""
    return "".join(p.capitalize() for p in parts)


def _branch_taken_op(prefix, name, relation_title, lean_rel_expr,
                     family="Interval"):
    """Build a BranchTaken operator substitution dict.

    family: "Interval" (old interval+tnum RegState, 32-bit tasks) or
    "Cnum" (cnum+tnum RegState, 64-bit tasks). It prefixes the task
    directory name only; Lean identifiers stay family-free.
    """
    key = f"{prefix}_{name.lower()}"
    lean_name = _lean_name(key.split("_"))
    func_name = f"is{lean_name}Taken"
    always_name = f"alwaysProp{lean_name}"
    never_name = f"neverProp{lean_name}"
    return {
        "OPERATOR_NAME": f"{prefix.upper()}_{name}",
        "RELATION_TITLE": relation_title,
        "LEAN_REL_EXPR": lean_rel_expr,
        "LEAN_FUNC_NAME": func_name,
        "LEAN_ALWAYS_NAME": always_name,
        "LEAN_NEVER_NAME": never_name,
        "LEAN_TASK_NAME": f"{family}_{lean_name}",
    }


def _refine_cond_op(prefix, name, relation_title, lean_rel_expr,
                    family="Interval"):
    """Build a RefineCond operator substitution dict (family as above)."""
    key = f"{prefix}_{name.lower()}"
    lean_name = _lean_name(["refine"] + key.split("_"))
    func_name = f"refineCond{_lean_name(key.split('_'))}"
    return {
        "OPERATOR_NAME": f"{prefix.upper()}_{name}",
        "RELATION_TITLE": relation_title,
        "LEAN_REL_EXPR": lean_rel_expr,
        "LEAN_FUNC_NAME": func_name,
        "LEAN_TASK_NAME": f"{family}_{lean_name}",
    }


def _alu_op(width, name, op_title, lean_op_desc, lean_concrete_name,
            lean_concrete_body, extra_preconditions="", family="Interval"):
    """Build an AluOp operator substitution dict (family as above)."""
    key = f"alu{width}_{name.lower()}"
    lean_name = _lean_name(key.split("_"))
    func_name = f"alu{width}{name.capitalize()}"
    return {
        "OPERATOR_NAME": f"ALU{width}_{name.upper()}",
        "OPERATION_TITLE": op_title,
        "LEAN_OP_DESCRIPTION": lean_op_desc,
        "LEAN_CONCRETE_OP_NAME": lean_concrete_name,
        "LEAN_CONCRETE_OP_BODY": lean_concrete_body,
        "LEAN_FUNC_NAME": func_name,
        "LEAN_TASK_NAME": f"{family}_{lean_name}",
        "LEAN_EXTRA_PRECONDITIONS": extra_preconditions,
    }


# ── BranchTaken operators ────────────────────────────────────────────
#
# 32-bit comparisons keep the old interval+tnum RegState
# (template/BranchTaken.lean); 64-bit comparisons use the bpf-next
# cnum+tnum RegState (template/CnumBranchTaken.lean).

BRANCH_TAKEN_OPS = {
    # === JMP32 operators (32-bit comparisons, interval+tnum domain) ===
    "interval_jmp32_eq": _branch_taken_op("jmp32", "EQ",
                                  "Equality (32-bit)",
                                  "x.truncate 32 = y.truncate 32"),
    "interval_jmp32_lt": _branch_taken_op("jmp32", "LT",
                                  "Less Than, unsigned (32-bit)",
                                  "(x.truncate 32 : BitVec 32) < y.truncate 32"),
    "interval_jmp32_le": _branch_taken_op("jmp32", "LE",
                                  "Less Than or Equal, unsigned (32-bit)",
                                  "(x.truncate 32 : BitVec 32) ≤ y.truncate 32"),
    "interval_jmp32_slt": _branch_taken_op("jmp32", "SLT",
                                   "Less Than, signed (32-bit)",
                                   "(x.truncate 32 : BitVec 32).toInt < (y.truncate 32 : BitVec 32).toInt"),
    "interval_jmp32_sle": _branch_taken_op("jmp32", "SLE",
                                   "Less Than or Equal, signed (32-bit)",
                                   "(x.truncate 32 : BitVec 32).toInt ≤ (y.truncate 32 : BitVec 32).toInt"),
    "interval_jmp32_jset": _branch_taken_op("jmp32", "JSET",
                                    "Bitwise Test (32-bit)",
                                    "((x.truncate 32 : BitVec 32) &&& y.truncate 32) ≠ 0"),
}

CNUM_BRANCH_TAKEN_OPS = {
    # === JMP64 operators (64-bit comparisons, cnum+tnum domain) ===
    "cnum_jmp64_eq": _branch_taken_op("jmp64", "EQ",
                                  "Equality (64-bit)",
                                  "x = y", family="Cnum"),
    "cnum_jmp64_lt": _branch_taken_op("jmp64", "LT",
                                  "Less Than, unsigned (64-bit)",
                                  "x < y", family="Cnum"),
    "cnum_jmp64_le": _branch_taken_op("jmp64", "LE",
                                  "Less Than or Equal, unsigned (64-bit)",
                                  "x ≤ y", family="Cnum"),
    "cnum_jmp64_slt": _branch_taken_op("jmp64", "SLT",
                                   "Less Than, signed (64-bit)",
                                   "x.toInt < y.toInt", family="Cnum"),
    "cnum_jmp64_sle": _branch_taken_op("jmp64", "SLE",
                                   "Less Than or Equal, signed (64-bit)",
                                   "x.toInt ≤ y.toInt", family="Cnum"),
    "cnum_jmp64_jset": _branch_taken_op("jmp64", "JSET",
                                    "Bitwise Test (64-bit)",
                                    "(x &&& y) ≠ 0", family="Cnum"),
}

# ── RefineCond operators ─────────────────────────────────────────────
#
# 32-bit refinements keep the old interval+tnum RegState
# (template/RefineCond.lean); 64-bit refinements use the bpf-next
# cnum+tnum RegState (template/CnumRefineCond.lean).

REFINE_COND_OPS = {
    # === 32-bit refinements (interval+tnum domain) ===
    "interval_refine_jmp32_eq": _refine_cond_op("jmp32", "EQ",
                                        "Equality (32-bit)",
                                        "x.truncate 32 = y.truncate 32"),
    "interval_refine_jmp32_ne": _refine_cond_op("jmp32", "NE",
                                        "Not Equal (32-bit)",
                                        "x.truncate 32 ≠ y.truncate 32"),
    "interval_refine_jmp32_lt": _refine_cond_op("jmp32", "LT",
                                        "Less Than, unsigned (32-bit)",
                                        "(x.truncate 32 : BitVec 32) < y.truncate 32"),
    "interval_refine_jmp32_le": _refine_cond_op("jmp32", "LE",
                                        "Less Than or Equal, unsigned (32-bit)",
                                        "(x.truncate 32 : BitVec 32) ≤ y.truncate 32"),
    "interval_refine_jmp32_slt": _refine_cond_op("jmp32", "SLT",
                                         "Less Than, signed (32-bit)",
                                         "(x.truncate 32 : BitVec 32).toInt < (y.truncate 32 : BitVec 32).toInt"),
    "interval_refine_jmp32_sle": _refine_cond_op("jmp32", "SLE",
                                         "Less Than or Equal, signed (32-bit)",
                                         "(x.truncate 32 : BitVec 32).toInt ≤ (y.truncate 32 : BitVec 32).toInt"),
    "interval_refine_jmp32_jset": _refine_cond_op("jmp32", "JSET",
                                          "Bitwise Test (32-bit)",
                                          "((x.truncate 32 : BitVec 32) &&& y.truncate 32) ≠ 0"),
    "interval_refine_jmp32_xjset": _refine_cond_op("jmp32", "XJSET",
                                           "Bitwise Not-Set (32-bit)",
                                           "((x.truncate 32 : BitVec 32) &&& y.truncate 32) = 0"),
}

CNUM_REFINE_COND_OPS = {
    # === 64-bit refinements (cnum+tnum domain) ===
    "cnum_refine_jmp64_ne": _refine_cond_op("jmp64", "NE",
                                        "Not Equal (64-bit)",
                                        "x ≠ y", family="Cnum"),
    "cnum_refine_jmp64_lt": _refine_cond_op("jmp64", "LT",
                                        "Less Than, unsigned (64-bit)",
                                        "x < y", family="Cnum"),
    "cnum_refine_jmp64_le": _refine_cond_op("jmp64", "LE",
                                        "Less Than or Equal, unsigned (64-bit)",
                                        "x ≤ y", family="Cnum"),
    "cnum_refine_jmp64_slt": _refine_cond_op("jmp64", "SLT",
                                         "Less Than, signed (64-bit)",
                                         "x.toInt < y.toInt", family="Cnum"),
    "cnum_refine_jmp64_sle": _refine_cond_op("jmp64", "SLE",
                                         "Less Than or Equal, signed (64-bit)",
                                         "x.toInt ≤ y.toInt", family="Cnum"),
    "cnum_refine_jmp64_jset": _refine_cond_op("jmp64", "JSET",
                                          "Bitwise Test (64-bit)",
                                          "(x &&& y) ≠ 0", family="Cnum"),
    "cnum_refine_jmp64_xjset": _refine_cond_op("jmp64", "XJSET",
                                           "Bitwise Not-Set (64-bit)",
                                           "(x &&& y) = 0", family="Cnum"),
}

# ── ALU operators ────────────────────────────────────────────────────
#
# 32-bit ALU ops keep the old interval+tnum RegState
# (template/AluOp.lean); 64-bit ALU ops use the bpf-next cnum+tnum
# RegState (template/CnumAluOp.lean).

def _alu64_op(name, title, desc, body, extra=""):
    return _alu_op(64, name, title, desc,
                   f"concrete{name.capitalize()}64", body, extra,
                   family="Cnum")

def _alu32_op(name, title, desc, body, extra=""):
    return _alu_op(32, name, title, desc,
                   f"concrete{name.capitalize()}32", body, extra)

CNUM_ALU_OPS = {
    # === 64-bit ALU (cnum+tnum domain) ===
    "cnum_alu64_add": _alu64_op("add", "Addition (64-bit, cnum domain)",
        "wrapping 64-bit addition (dst + src)",
        "d + s"),
    "cnum_alu64_sub": _alu64_op("sub", "Subtraction (64-bit, cnum domain)",
        "wrapping 64-bit subtraction (dst - src)",
        "d - s"),
    "cnum_alu64_and": _alu64_op("and", "Bitwise AND (64-bit, cnum domain)",
        "bitwise AND (dst & src)",
        "d &&& s"),
    "cnum_alu64_or": _alu64_op("or", "Bitwise OR (64-bit, cnum domain)",
        "bitwise OR (dst | src)",
        "d ||| s"),
    "cnum_alu64_xor": _alu64_op("xor", "Bitwise XOR (64-bit, cnum domain)",
        "bitwise XOR (dst ^ src)",
        "d ^^^ s"),
    "cnum_alu64_lsh": _alu64_op("lsh", "Left Shift (64-bit, cnum domain)",
        "logical left shift (dst << src), shift amount < 64",
        "d <<< s.toNat",
        extra="(hshift : ∀ s, inGamma src s → s.toNat < 64)"),
    "cnum_alu64_rsh": _alu64_op("rsh", "Logical Right Shift (64-bit, cnum domain)",
        "logical right shift (dst >> src), shift amount < 64",
        "d >>> s.toNat",
        extra="(hshift : ∀ s, inGamma src s → s.toNat < 64)"),
    "cnum_alu64_arsh": _alu64_op("arsh", "Arithmetic Right Shift (64-bit, cnum domain)",
        "arithmetic right shift ((s64)dst >> src), shift amount < 64",
        "BitVec.ofInt 64 (d.toInt >>> s.toNat)",
        extra="(hshift : ∀ s, inGamma src s → s.toNat < 64)"),
}

ALU_OPS = {
    # === 32-bit ALU (interval+tnum domain, zero-extended result) ===
    "interval_alu32_add": _alu32_op("add", "Addition (32-bit)",
        "32-bit wrapping addition, zero-extended to 64",
        "(((d.truncate 32 : BitVec 32) + (s.truncate 32 : BitVec 32)).zeroExtend 64 : BitVec 64)"),
    "interval_alu32_sub": _alu32_op("sub", "Subtraction (32-bit)",
        "32-bit wrapping subtraction, zero-extended to 64",
        "(((d.truncate 32 : BitVec 32) - (s.truncate 32 : BitVec 32)).zeroExtend 64 : BitVec 64)"),
    "interval_alu32_and": _alu32_op("and", "Bitwise AND (32-bit)",
        "32-bit bitwise AND, zero-extended to 64",
        "(((d.truncate 32 : BitVec 32) &&& (s.truncate 32 : BitVec 32)).zeroExtend 64 : BitVec 64)"),
    "interval_alu32_or": _alu32_op("or", "Bitwise OR (32-bit)",
        "32-bit bitwise OR, zero-extended to 64",
        "(((d.truncate 32 : BitVec 32) ||| (s.truncate 32 : BitVec 32)).zeroExtend 64 : BitVec 64)"),
    "interval_alu32_xor": _alu32_op("xor", "Bitwise XOR (32-bit)",
        "32-bit bitwise XOR, zero-extended to 64",
        "(((d.truncate 32 : BitVec 32) ^^^ (s.truncate 32 : BitVec 32)).zeroExtend 64 : BitVec 64)"),
    "interval_alu32_lsh": _alu32_op("lsh", "Left Shift (32-bit)",
        "32-bit logical left shift, zero-extended to 64, shift amount < 32",
        "(((d.truncate 32 : BitVec 32) <<< (s.truncate 32 : BitVec 32).toNat).zeroExtend 64 : BitVec 64)",
        extra="(hshift : ∀ s, inGamma src s → (s.truncate 32 : BitVec 32).toNat < 32)"),
    "interval_alu32_rsh": _alu32_op("rsh", "Logical Right Shift (32-bit)",
        "32-bit logical right shift, zero-extended to 64, shift amount < 32",
        "(((d.truncate 32 : BitVec 32) >>> (s.truncate 32 : BitVec 32).toNat).zeroExtend 64 : BitVec 64)",
        extra="(hshift : ∀ s, inGamma src s → (s.truncate 32 : BitVec 32).toNat < 32)"),
    "interval_alu32_arsh": _alu32_op("arsh", "Arithmetic Right Shift (32-bit)",
        "32-bit arithmetic right shift, zero-extended to 64, shift amount < 32",
        "((BitVec.ofInt 32 ((d.truncate 32 : BitVec 32).toInt >>> (s.truncate 32 : BitVec 32).toNat)).zeroExtend 64 : BitVec 64)",
        extra="(hshift : ∀ s, inGamma src s → (s.truncate 32 : BitVec 32).toNat < 32)"),
}

# ── Tnum binary operators (template/TnumBinOp.lean) ───────────────────

def _tnum_bin_op(name, op_title, lean_op_desc, lean_concrete_name,
                 lean_concrete_body):
    """Build a TnumBinOp operator substitution dict."""
    lean_name = _lean_name(["tnum", name.lower()])
    func_name = f"tnum{name.capitalize()}"
    return {
        "OPERATOR_NAME": f"TNUM_{name.upper()}",
        "OPERATION_TITLE": op_title,
        "LEAN_OP_DESCRIPTION": lean_op_desc,
        "LEAN_CONCRETE_OP_NAME": lean_concrete_name,
        "LEAN_CONCRETE_OP_BODY": lean_concrete_body,
        "LEAN_FUNC_NAME": func_name,
        "LEAN_TASK_NAME": lean_name,
    }


TNUM_BIN_OPS = {
    "tnum_mul": {**_tnum_bin_op("mul", "Tnum Multiplication",
        "wrapping 64-bit multiplication of two tnums",
        "concreteMul", "a * b"), "_O1_REQUIRED": False},
}

# ── Tnum-const operators (template/TnumConstOp.lean) ─────────────────

def _tnum_const_op(name, op_title, lean_op_desc, lean_concrete_name,
                   lean_concrete_body):
    """Build a TnumConstOp operator substitution dict.

    Task dirs are prefixed "Const_" (eBPF_Const_TnumUdiv, ...) to mark
    the constant-divisor variants; Lean identifiers stay unprefixed.
    """
    lean_name = _lean_name(["tnum", name.lower()])
    func_name = f"tnum{name.capitalize()}"
    return {
        "OPERATOR_NAME": f"TNUM_{name.upper()}",
        "OPERATION_TITLE": op_title,
        "LEAN_OP_DESCRIPTION": lean_op_desc,
        "LEAN_CONCRETE_OP_NAME": lean_concrete_name,
        "LEAN_CONCRETE_OP_BODY": lean_concrete_body,
        "LEAN_FUNC_NAME": func_name,
        "LEAN_TASK_NAME": f"Const_{lean_name}",
    }


TNUM_CONST_OPS = {
    "const_tnum_udiv": {**_tnum_const_op("udiv",
        "Tnum Unsigned Division by Constant",
        "unsigned 64-bit division of a tnum by a non-zero constant",
        "concreteUdiv", "a / c"), "_O1_REQUIRED": False},
    "const_tnum_sdiv": {**_tnum_const_op("sdiv",
        "Tnum Signed Division by Constant",
        "signed 64-bit division of a tnum by a non-zero constant "
        "(S64_MIN sdiv -1 = S64_MIN, i.e. wrapping semantics)",
        "concreteSdiv",
        "BitVec.ofInt 64 (a.toInt.tdiv c.toInt)"), "_O1_REQUIRED": False},
    "const_tnum_umod": {**_tnum_const_op("umod",
        "Tnum Unsigned Modulo by Constant",
        "unsigned 64-bit modulo of a tnum by a non-zero constant",
        "concreteUmod", "a % c"), "_O1_REQUIRED": False},
    "const_tnum_smod": {**_tnum_const_op("smod",
        "Tnum Signed Modulo by Constant",
        "signed 64-bit modulo of a tnum by a non-zero constant "
        "(remainder has the same sign as the dividend)",
        "concreteSmod",
        "BitVec.ofInt 64 (a.toInt.tmod c.toInt)"), "_O1_REQUIRED": False},
}

# ── Cast operators (template/CnumCastOp.lean, cnum+tnum domain) ───────

CNUM_CAST_OPS = {
    "cnum_cast_zext": {
        "OPERATOR_NAME": "ZEXT",
        "OPERATION_TITLE": "Zero Extension (cnum domain)",
        "LEAN_OP_DESCRIPTION":
            "zero-extending the low size*8 bits to 64 bits (coerce_reg_to_size)",
        "LEAN_CONCRETE_OP_NAME": "concreteZext",
        "LEAN_CONCRETE_OP_BODY":
            "x &&& (((1 : BitVec 64) <<< (size * 8)) - 1)",
        "LEAN_FUNC_NAME": "castZext",
        "LEAN_TASK_NAME": "Cnum_CastZext",
    },
    "cnum_cast_sext": {
        "OPERATOR_NAME": "SEXT",
        "OPERATION_TITLE": "Sign Extension (cnum domain)",
        "LEAN_OP_DESCRIPTION":
            "sign-extending the low size*8 bits to 64 bits (coerce_reg_to_size_sx)",
        "LEAN_CONCRETE_OP_NAME": "concreteSext",
        "LEAN_CONCRETE_OP_BODY":
            "let mask := ((1 : BitVec 64) <<< (size * 8)) - 1\n"
            "  let signBit := (1 : BitVec 64) <<< (size * 8 - 1)\n"
            "  let low := x &&& mask\n"
            "  if (low &&& signBit) ≠ 0 then low ||| ~~~mask else low",
        "LEAN_FUNC_NAME": "castSext",
        "LEAN_TASK_NAME": "Cnum_CastSext",
    },
}

# ── Bounds Sync (template/CnumBoundsSync.lean, cnum+tnum domain) ──────

CNUM_BOUNDS_SYNC_OPS = {
    "cnum_bounds_sync": {
        "LEAN_TASK_NAME": "Cnum_BoundsSync",
    },
}

# ── LLVM KnownBits forward operators (template/KBBinOp.lean) ─────────

def _nsw_pre_body(op):
    """Generate NSW precondition body for a binary operation (+, -, *)."""
    return (f"let sx := x.toInt\n"
            f"  let sy := y.toInt\n"
            f"  let sr := sx {op} sy\n"
            f"  sr ≥ -(2 ^ 63 : Int) ∧ sr ≤ (2 ^ 63 - 1 : Int)")


KB_BIN_OPS = {
    "kb_umax": {
        "OPERATION_TITLE": "Unsigned Maximum",
        "OPERATOR_NAME": "@llvm.umax",
        "LEAN_OP_DESCRIPTION": "unsigned 64-bit maximum",
        "LEAN_CONCRETE_OP_NAME": "concreteUmax",
        "LEAN_CONCRETE_OP_BODY": "if x.toNat ≥ y.toNat then x else y",
        "LEAN_FUNC_NAME": "kbUmax",
        "LEAN_TASK_NAME": "KBUmax",
        "_INSTRUCTION_DESC": "The function receives two KnownBits and must "
            "return a `KnownBits` for the unsigned maximum.",
    },
    "kb_umin": {
        "OPERATION_TITLE": "Unsigned Minimum",
        "OPERATOR_NAME": "@llvm.umin",
        "LEAN_OP_DESCRIPTION": "unsigned 64-bit minimum",
        "LEAN_CONCRETE_OP_NAME": "concreteUmin",
        "LEAN_CONCRETE_OP_BODY": "if x.toNat ≤ y.toNat then x else y",
        "LEAN_FUNC_NAME": "kbUmin",
        "LEAN_TASK_NAME": "KBUmin",
        "_INSTRUCTION_DESC": "The function receives two KnownBits and must "
            "return a `KnownBits` for the unsigned minimum.",
    },
    "kb_smax": {
        "OPERATION_TITLE": "Signed Maximum",
        "OPERATOR_NAME": "@llvm.smax",
        "LEAN_OP_DESCRIPTION": "signed 64-bit maximum",
        "LEAN_CONCRETE_OP_NAME": "concreteSmax",
        "LEAN_CONCRETE_OP_BODY": "if x.toInt ≥ y.toInt then x else y",
        "LEAN_FUNC_NAME": "kbSmax",
        "LEAN_TASK_NAME": "KBSmax",
        "_INSTRUCTION_DESC": "The function receives two KnownBits and must "
            "return a `KnownBits` for the signed maximum.",
    },
    "kb_smin": {
        "OPERATION_TITLE": "Signed Minimum",
        "OPERATOR_NAME": "@llvm.smin",
        "LEAN_OP_DESCRIPTION": "signed 64-bit minimum",
        "LEAN_CONCRETE_OP_NAME": "concreteSmin",
        "LEAN_CONCRETE_OP_BODY": "if x.toInt ≤ y.toInt then x else y",
        "LEAN_FUNC_NAME": "kbSmin",
        "LEAN_TASK_NAME": "KBSmin",
        "_INSTRUCTION_DESC": "The function receives two KnownBits and must "
            "return a `KnownBits` for the signed minimum.",
    },
    "kb_abdu": {
        "OPERATION_TITLE": "Unsigned Absolute Difference",
        "OPERATOR_NAME": "ISD::ABDU",
        "LEAN_OP_DESCRIPTION": "unsigned 64-bit absolute difference",
        "LEAN_CONCRETE_OP_NAME": "concreteAbdu",
        "LEAN_CONCRETE_OP_BODY": "if x.toNat ≥ y.toNat then x - y else y - x",
        "LEAN_FUNC_NAME": "kbAbdu",
        "LEAN_TASK_NAME": "KBAbdu",
        "_INSTRUCTION_DESC": "The function receives two KnownBits and must "
            "return a `KnownBits` for |x - y| (unsigned).",
    },
    "kb_abds": {
        "OPERATION_TITLE": "Signed Absolute Difference",
        "OPERATOR_NAME": "ISD::ABDS",
        "LEAN_OP_DESCRIPTION":
            "signed 64-bit absolute difference (unsigned result)",
        "LEAN_CONCRETE_OP_NAME": "concreteAbds",
        "LEAN_CONCRETE_OP_BODY":
            "BitVec.ofNat 64 (x.toInt - y.toInt).natAbs",
        "LEAN_FUNC_NAME": "kbAbds",
        "LEAN_TASK_NAME": "KBAbds",
        "_INSTRUCTION_DESC": "The function receives two KnownBits and must "
            "return a `KnownBits` for |x - y| (signed inputs, unsigned result).",
    },
    "kb_uadd_sat": {
        "OPERATION_TITLE": "Unsigned Saturating Addition",
        "OPERATOR_NAME": "@llvm.uadd.sat",
        "LEAN_OP_DESCRIPTION": "unsigned 64-bit saturating addition",
        "LEAN_CONCRETE_OP_NAME": "concreteUaddSat",
        "LEAN_CONCRETE_OP_BODY":
            "if x.toNat + y.toNat ≥ 2 ^ 64 then "
            "BitVec.ofNat 64 (2 ^ 64 - 1) else x + y",
        "LEAN_FUNC_NAME": "kbUaddSat",
        "LEAN_TASK_NAME": "KBUaddSat",
        "_INSTRUCTION_DESC": "The function receives two KnownBits and must "
            "return a `KnownBits` for min(x+y, 2^64-1).",
    },
    "kb_usub_sat": {
        "OPERATION_TITLE": "Unsigned Saturating Subtraction",
        "OPERATOR_NAME": "@llvm.usub.sat",
        "LEAN_OP_DESCRIPTION": "unsigned 64-bit saturating subtraction",
        "LEAN_CONCRETE_OP_NAME": "concreteUsubSat",
        "LEAN_CONCRETE_OP_BODY":
            "if x.toNat ≥ y.toNat then x - y else 0",
        "LEAN_FUNC_NAME": "kbUsubSat",
        "LEAN_TASK_NAME": "KBUsubSat",
        "_INSTRUCTION_DESC": "The function receives two KnownBits and must "
            "return a `KnownBits` for max(x-y, 0).",
    },
    "kb_sadd_sat": {
        "OPERATION_TITLE": "Signed Saturating Addition",
        "OPERATOR_NAME": "@llvm.sadd.sat",
        "LEAN_OP_DESCRIPTION": "signed 64-bit saturating addition",
        "LEAN_CONCRETE_OP_NAME": "concreteSaddSat",
        "LEAN_CONCRETE_OP_BODY":
            "let r := x.toInt + y.toInt\n"
            "  if r > 2 ^ 63 - 1 then BitVec.ofInt 64 (2 ^ 63 - 1)\n"
            "  else if r < -(2 ^ 63) then BitVec.ofInt 64 (-(2 ^ 63))\n"
            "  else BitVec.ofInt 64 r",
        "LEAN_FUNC_NAME": "kbSaddSat",
        "LEAN_TASK_NAME": "KBSaddSat",
        "_INSTRUCTION_DESC": "The function receives two KnownBits and must "
            "return a `KnownBits` for clamp(x+y, INT_MIN, INT_MAX).",
    },
    "kb_ssub_sat": {
        "OPERATION_TITLE": "Signed Saturating Subtraction",
        "OPERATOR_NAME": "@llvm.ssub.sat",
        "LEAN_OP_DESCRIPTION": "signed 64-bit saturating subtraction",
        "LEAN_CONCRETE_OP_NAME": "concreteSsubSat",
        "LEAN_CONCRETE_OP_BODY":
            "let r := x.toInt - y.toInt\n"
            "  if r > 2 ^ 63 - 1 then BitVec.ofInt 64 (2 ^ 63 - 1)\n"
            "  else if r < -(2 ^ 63) then BitVec.ofInt 64 (-(2 ^ 63))\n"
            "  else BitVec.ofInt 64 r",
        "LEAN_FUNC_NAME": "kbSsubSat",
        "LEAN_TASK_NAME": "KBSsubSat",
        "_INSTRUCTION_DESC": "The function receives two KnownBits and must "
            "return a `KnownBits` for clamp(x-y, INT_MIN, INT_MAX).",
    },
    "kb_mulhu": {
        "OPERATION_TITLE": "Unsigned Multiply High",
        "OPERATOR_NAME": "ISD::MULHU",
        "LEAN_OP_DESCRIPTION":
            "upper 64 bits of unsigned 128-bit multiplication",
        "LEAN_CONCRETE_OP_NAME": "concreteMulhu",
        "LEAN_CONCRETE_OP_BODY":
            "BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64)",
        "LEAN_FUNC_NAME": "kbMulhu",
        "LEAN_TASK_NAME": "KBMulhu",
        "_INSTRUCTION_DESC": "The function receives two KnownBits and must "
            "return a `KnownBits` for the upper 64 bits of the 128-bit "
            "unsigned product.",
        "_O1_REQUIRED": False,
    },
    "kb_mulhs": {
        "OPERATION_TITLE": "Signed Multiply High",
        "OPERATOR_NAME": "ISD::MULHS",
        "LEAN_OP_DESCRIPTION":
            "upper 64 bits of signed 128-bit multiplication",
        "LEAN_CONCRETE_OP_NAME": "concreteMulhs",
        "LEAN_CONCRETE_OP_BODY":
            "-- Sign-extend to 128-bit unsigned representation, "
            "multiply, extract upper half\n"
            "  let xu := if x.msb then x.toNat + "
            "(2 ^ 128 - 2 ^ 64) else x.toNat\n"
            "  let yu := if y.msb then y.toNat + "
            "(2 ^ 128 - 2 ^ 64) else y.toNat\n"
            "  BitVec.ofNat 64 ((xu * yu % 2 ^ 128) / 2 ^ 64)",
        "LEAN_FUNC_NAME": "kbMulhs",
        "LEAN_TASK_NAME": "KBMulhs",
        "_INSTRUCTION_DESC": "The function receives two KnownBits and must "
            "return a `KnownBits` for the upper 64 bits of the 128-bit "
            "signed product.",
        "_O1_REQUIRED": False,
    },
}

# ── LLVM KnownBits forward: division (template/KBBinOpDiv.lean) ──────

KB_BIN_DIV_OPS = {
    "kb_urem": {
        "OPERATION_TITLE": "Unsigned Remainder",
        "OPERATOR_NAME": "urem",
        "LEAN_OP_DESCRIPTION": "unsigned 64-bit remainder",
        "LEAN_CONCRETE_OP_NAME": "concreteUrem",
        "LEAN_CONCRETE_OP_BODY": "x % y",
        "LEAN_FUNC_NAME": "kbUrem",
        "LEAN_TASK_NAME": "KBUrem",
        "_O1_REQUIRED": False,
        "_INSTRUCTION_DESC": "The function receives two KnownBits and must "
            "return a `KnownBits` for the unsigned remainder.",
    },
    "kb_srem": {
        "OPERATION_TITLE": "Signed Remainder",
        "OPERATOR_NAME": "srem",
        "LEAN_OP_DESCRIPTION": "signed 64-bit remainder",
        "LEAN_CONCRETE_OP_NAME": "concreteSrem",
        "LEAN_CONCRETE_OP_BODY":
            "BitVec.ofInt 64 (x.toInt.tmod y.toInt)",
        "LEAN_FUNC_NAME": "kbSrem",
        "LEAN_TASK_NAME": "KBSrem",
        "_O1_REQUIRED": False,
        "_INSTRUCTION_DESC": "The function receives two KnownBits and must "
            "return a `KnownBits` for the signed remainder.",
    },
}

# ── LLVM KnownBits forward: div+exact (template/KBBinOpDivExact.lean) ─

KB_BIN_DIV_EXACT_OPS = {
    "kb_udiv": {
        "OPERATION_TITLE": "Unsigned Division",
        "OPERATOR_NAME": "udiv [exact]",
        "LEAN_OP_DESCRIPTION": "unsigned 64-bit division",
        "LEAN_CONCRETE_OP_NAME": "concreteUdiv",
        "LEAN_CONCRETE_OP_BODY": "x / y",
        "LEAN_EXACT_PRE_NAME": "udivExactPre",
        "LEAN_EXACT_PRE_BODY": "x % y = 0",
        "LEAN_FUNC_NAME": "kbUdiv",
        "LEAN_TASK_NAME": "KBUdiv",
        "_O1_REQUIRED": False,
        "_INSTRUCTION_DESC": "The function receives two KnownBits and an "
            "exact flag, and must return a `KnownBits` for the unsigned "
            "quotient.",
    },
    "kb_sdiv": {
        "OPERATION_TITLE": "Signed Division",
        "OPERATOR_NAME": "sdiv [exact]",
        "LEAN_OP_DESCRIPTION": "signed 64-bit division",
        "LEAN_CONCRETE_OP_NAME": "concreteSdiv",
        "LEAN_CONCRETE_OP_BODY":
            "BitVec.ofInt 64 (x.toInt.tdiv y.toInt)",
        "LEAN_EXACT_PRE_NAME": "sdivExactPre",
        "LEAN_EXACT_PRE_BODY":
            "BitVec.ofInt 64 (x.toInt.tmod y.toInt) = 0",
        "LEAN_FUNC_NAME": "kbSdiv",
        "LEAN_TASK_NAME": "KBSdiv",
        "_O1_REQUIRED": False,
        "_INSTRUCTION_DESC": "The function receives two KnownBits and an "
            "exact flag, and must return a `KnownBits` for the signed "
            "quotient.",
    },
}

# ── LLVM KnownBits forward: mul+flags (template/KBBinOpMulFlags.lean) ─

KB_BIN_MUL_FLAGS_OPS = {
    "kb_mul": {
        "OPERATION_TITLE": "Multiplication",
        "OPERATOR_NAME": "mul [nsw] [nuw]",
        "LEAN_OP_DESCRIPTION": "64-bit multiplication",
        "LEAN_CONCRETE_OP_NAME": "concreteMul",
        "LEAN_CONCRETE_OP_BODY": "x * y",
        "LEAN_NSW_PRE_NAME": "mulNSWPre",
        "LEAN_NSW_PRE_BODY": _nsw_pre_body("*"),
        "LEAN_NUW_PRE_NAME": "mulNUWPre",
        "LEAN_NUW_PRE_BODY": "x.toNat * y.toNat < 2 ^ 64",
        "LEAN_FLAGS_NAME": "mulFlags",
        "LEAN_FUNC_NAME": "kbMul",
        "LEAN_TASK_NAME": "KBMul",
        "_INSTRUCTION_DESC": "The function receives two KnownBits and "
            "nsw/nuw flags, and must return a `KnownBits` for the product.",
        "_O1_REQUIRED": False,
    },
}

# ── LLVM KnownBits forward: unary+flag (template/KBUnaryOpFlag.lean) ──

KB_UNARY_FLAG_OPS = {
    "kb_abs": {
        "OPERATION_TITLE": "Absolute Value",
        "OPERATOR_NAME": "@llvm.abs [IntMinIsPoison]",
        "LEAN_OP_DESCRIPTION":
            "64-bit absolute value (signed interpretation)",
        "LEAN_CONCRETE_OP_NAME": "concreteAbs",
        "LEAN_CONCRETE_OP_BODY": "if x.msb then -x else x",
        "LEAN_FLAG_PRE_NAME": "absIntMinPre",
        "LEAN_FLAG_PRE_BODY":
            "x ≠ BitVec.ofInt 64 (-(2 ^ 63))",
        "LEAN_FLAGS_NAME": "absFlags",
        "LEAN_FUNC_NAME": "kbAbs",
        "LEAN_TASK_NAME": "KBAbs",
        "_INSTRUCTION_DESC": "The function receives a KnownBits and an "
            "IntMinIsPoison flag, and must return a `KnownBits` for the "
            "absolute value.",
    },
    "kb_mul_self": {
        "OPERATION_TITLE": "Self-Multiplication (Squaring)",
        "OPERATOR_NAME": "mul [nsw] (x * x)",
        "LEAN_OP_DESCRIPTION":
            "64-bit self-multiplication (x * x)",
        "LEAN_CONCRETE_OP_NAME": "concreteMulSelf",
        "LEAN_CONCRETE_OP_BODY": "x * x",
        "LEAN_FLAG_PRE_NAME": "mulSelfNSWPre",
        "LEAN_FLAG_PRE_BODY":
            "let sx := x.toInt\n"
            "  let sr := sx * sx\n"
            "  sr ≥ -(2 ^ 63 : Int) ∧ sr ≤ (2 ^ 63 - 1 : Int)",
        "LEAN_FLAGS_NAME": "mulSelfFlags",
        "LEAN_FUNC_NAME": "kbMulSelf",
        "LEAN_TASK_NAME": "KBMulSelf",
        "_INSTRUCTION_DESC": "The function receives a KnownBits and an "
            "nsw flag, and must return a `KnownBits` for x*x.",
        "_O1_REQUIRED": False,
    },
}

# ── LLVM DemandedBits backward: binary+flags (template/DBBinOpFlags.lean)

DB_BIN_FLAGS_OPS = {
    "db_add": {
        "OPERATION_TITLE": "Backward Demanded Bits for Add",
        "OPERATOR_NAME": "add [nsw] [nuw]",
        "LEAN_OP_DESCRIPTION": "64-bit addition",
        "LEAN_CONCRETE_OP_NAME": "concreteAdd",
        "LEAN_CONCRETE_OP_BODY": "x + y",
        "LEAN_NSW_PRE_NAME": "addNSWPre",
        "LEAN_NSW_PRE_BODY": _nsw_pre_body("+"),
        "LEAN_NUW_PRE_NAME": "addNUWPre",
        "LEAN_NUW_PRE_BODY": "x.toNat + y.toNat < 2 ^ 64",
        "LEAN_FLAGS_NAME": "addFlags",
        "LEAN_FUNC_NAME": "dbAdd",
        "LEAN_TASK_NAME": "DBAdd",
    },
    "db_sub": {
        "OPERATION_TITLE": "Backward Demanded Bits for Sub",
        "OPERATOR_NAME": "sub [nsw] [nuw]",
        "LEAN_OP_DESCRIPTION": "64-bit subtraction",
        "LEAN_CONCRETE_OP_NAME": "concreteSub",
        "LEAN_CONCRETE_OP_BODY": "x - y",
        "LEAN_NSW_PRE_NAME": "subNSWPre",
        "LEAN_NSW_PRE_BODY": _nsw_pre_body("-"),
        "LEAN_NUW_PRE_NAME": "subNUWPre",
        "LEAN_NUW_PRE_BODY": "x.toNat ≥ y.toNat",
        "LEAN_FLAGS_NAME": "subFlags",
        "LEAN_FUNC_NAME": "dbSub",
        "LEAN_TASK_NAME": "DBSub",
    },
    "db_mul": {
        "OPERATION_TITLE": "Backward Demanded Bits for Mul",
        "OPERATOR_NAME": "mul [nsw] [nuw]",
        "LEAN_OP_DESCRIPTION": "64-bit multiplication",
        "LEAN_CONCRETE_OP_NAME": "concreteMul",
        "LEAN_CONCRETE_OP_BODY": "x * y",
        "LEAN_NSW_PRE_NAME": "mulNSWPre",
        "LEAN_NSW_PRE_BODY": _nsw_pre_body("*"),
        "LEAN_NUW_PRE_NAME": "mulNUWPre",
        "LEAN_NUW_PRE_BODY": "x.toNat * y.toNat < 2 ^ 64",
        "LEAN_FLAGS_NAME": "mulFlags",
        "LEAN_FUNC_NAME": "dbMul",
        "LEAN_TASK_NAME": "DBMul",
        "_O1_REQUIRED": False,
    },
}

# ── LLVM DemandedBits backward: div+exact (template/DBBinOpExact.lean) ─

DB_BIN_EXACT_OPS = {
    "db_udiv": {
        "OPERATION_TITLE": "Backward Demanded Bits for UDiv",
        "OPERATOR_NAME": "udiv [exact]",
        "LEAN_OP_DESCRIPTION": "unsigned 64-bit division",
        "LEAN_CONCRETE_OP_NAME": "concreteUdiv",
        "LEAN_CONCRETE_OP_BODY": "x / y",
        "LEAN_EXACT_PRE_NAME": "udivExactPre",
        "LEAN_EXACT_PRE_BODY": "x % y = 0",
        "LEAN_FLAGS_NAME": "udivFlags",
        "LEAN_FUNC_NAME": "dbUdiv",
        "LEAN_TASK_NAME": "DBUdiv",
        "_O1_REQUIRED": False,
    },
    "db_sdiv": {
        "OPERATION_TITLE": "Backward Demanded Bits for SDiv",
        "OPERATOR_NAME": "sdiv [exact]",
        "LEAN_OP_DESCRIPTION": "signed 64-bit division",
        "LEAN_CONCRETE_OP_NAME": "concreteSdiv",
        "LEAN_CONCRETE_OP_BODY":
            "BitVec.ofInt 64 (x.toInt.tdiv y.toInt)",
        "LEAN_EXACT_PRE_NAME": "sdivExactPre",
        "LEAN_EXACT_PRE_BODY":
            "BitVec.ofInt 64 (x.toInt.tmod y.toInt) = 0",
        "LEAN_FLAGS_NAME": "sdivFlags",
        "LEAN_FUNC_NAME": "dbSdiv",
        "LEAN_TASK_NAME": "DBSdiv",
        "_O1_REQUIRED": False,
    },
}

# ── LLVM DemandedBits backward: div no flags (template/DBBinOp.lean) ──

DB_BIN_OPS = {
    "db_srem": {
        "OPERATION_TITLE": "Backward Demanded Bits for SRem",
        "OPERATOR_NAME": "srem",
        "LEAN_OP_DESCRIPTION": "signed 64-bit remainder",
        "LEAN_CONCRETE_OP_NAME": "concreteSrem",
        "LEAN_CONCRETE_OP_BODY":
            "BitVec.ofInt 64 (x.toInt.tmod y.toInt)",
        "LEAN_FUNC_NAME": "dbSrem",
        "LEAN_TASK_NAME": "DBSrem",
        "_O1_REQUIRED": False,
    },
    "db_urem": {
        "OPERATION_TITLE": "Backward Demanded Bits for URem",
        "OPERATOR_NAME": "urem",
        "LEAN_OP_DESCRIPTION": "unsigned 64-bit remainder",
        "LEAN_CONCRETE_OP_NAME": "concreteUrem",
        "LEAN_CONCRETE_OP_BODY": "x % y",
        "LEAN_FUNC_NAME": "dbUrem",
        "LEAN_TASK_NAME": "DBUrem",
        "_O1_REQUIRED": False,
    },
}

# ── LLVM DemandedBits backward: unary+flag (template/DBUnaryOpFlags.lean)

DB_UNARY_FLAGS_OPS = {
    "db_abs": {
        "OPERATION_TITLE": "Backward Demanded Bits for Abs",
        "OPERATOR_NAME": "@llvm.abs [IntMinIsPoison]",
        "LEAN_OP_DESCRIPTION":
            "64-bit absolute value (signed interpretation)",
        "LEAN_FLAG_DESCRIPTION": "IntMinIsPoison",
        "LEAN_CONCRETE_OP_NAME": "concreteAbs",
        "LEAN_CONCRETE_OP_BODY": "if x.msb then -x else x",
        "LEAN_FLAG_PRE_NAME": "absIntMinPre",
        "LEAN_FLAG_PRE_BODY":
            "x ≠ BitVec.ofInt 64 (-(2 ^ 63))",
        "LEAN_FLAGS_NAME": "absFlags",
        "LEAN_FUNC_NAME": "dbAbs",
        "LEAN_TASK_NAME": "DBAbs",
    },
}

# Backward compat alias for external scripts (interval BranchTaken ops)
OPERATOR_SUBSTITUTIONS = BRANCH_TAKEN_OPS

# Direct tasks: task file is maintained by hand in tasks/<dir_name>/Task.lean.
# The script only generates build infra around them.
# seL4 direct tasks (no complexity requirement).
SEL4_DIRECT_TASKS = [
    "AllocRegion",
    "CDTInsert",
    "CNodeGuardCompressM",
    "CancelAllIPC",
    "CapDLSTCC",
    "CreateNewObjects",
    "CteRevoke",
    "CteSwap",
    "DeleteASIDPool",
    "FindFreeHWASID",
    "HandleOverrun",
    "IRQPendingFoldM",
    "IsFinalCapability",
    "MDBSubtreeRotateM",
    "PSpacePlaceObject",
    "PrioBitmapSetClear",
    "ReadyBitmapRebuildM",
    "ReadyQueueReindexM",
    "RefillMerge",
    "ReleaseEnqueue",
    "ReplyChainCompactM",
    "ScheduleForestMergeM",
    "ScheduleUsed",
    "ThreadStateBatch",
]

# BPF direct tasks (O(1) complexity required)
BPF_DIRECT_TASKS = [
    "TnumStepUp",
]

DIRECT_TASKS = SEL4_DIRECT_TASKS + BPF_DIRECT_TASKS


def expand_template(content: str, substitutions: Dict[str, str]) -> str:
    """Expand {{VARIABLE}} placeholders in content."""
    result = content
    for key, value in substitutions.items():
        result = result.replace(f"{{{{{key}}}}}", str(value))
    return result


def find_template_variables(content: str) -> list:
    """Find all {{VARIABLE}} placeholders in content."""
    return list(set(re.findall(r'\{\{(\w+)\}\}', content)))


def compute_provided_hash(content: str) -> str:
    """Extract provided sections and compute SHA256 hash.

    The trailing "\n" matches the bytes produced by `sed -n 'BEGIN,END/p'`
    in check.sh, which terminates every emitted line (including the last).
    Without it the two hashes would disagree over a single byte and
    integrity would fail on every unmodified task.
    """
    provided = []
    in_provided = False
    for line in content.splitlines():
        # Match `(provided)` and any `(provided, <tag>)` variant, so this
        # stays byte-identical to check.sh's bare-word `sed '/provided/'`
        # extraction. A stricter `\(provided\)` here would silently
        # diverge on tagged markers and break integrity (see docs).
        if re.search(r'=== BEGIN:.*\(provided\b', line):
            in_provided = True
            provided.append(line)
        elif re.search(r'=== END:', line) and in_provided:
            provided.append(line)
            in_provided = False
        elif in_provided:
            provided.append(line)
    text = "\n".join(provided) + "\n"
    return hashlib.sha256(text.encode()).hexdigest()


def _extract_sections(content: str) -> tuple:
    """Parse section markers and return (provided_names, editable_names).

    Tolerates tagged markers like `(editable, setBit)` used by
    multi-region tasks (one section split into several editable blocks);
    the section name is deduplicated so it is listed once.
    """
    provided: list = []
    editable: list = []
    for line in content.splitlines():
        m = re.search(r'=== BEGIN:\s+(\w+)\s+\((provided|editable)\b', line)
        if m:
            name, kind = m.group(1), m.group(2)
            bucket = provided if kind == "provided" else editable
            if name not in bucket:
                bucket.append(name)
    return provided, editable


def _task_title_from_file(content: str, fallback: str = "Unknown Task") -> str:
    """Extract task title from the header doc comment.

    Matches the descriptive title after a `Task:`/`Optimization:` keyword,
    covering both the generated eBPF/LLVM headers ("BPF ... task: X") and the
    hand-written seL4/CapDL headers ("seL4 Optimization Task: X",
    "seL4 Haskell Spec Optimization: X"). Falls back to `fallback` (the
    directory name) when no header line matches.
    """
    for line in content.splitlines():
        m = re.match(r'^\s*.*?\b(?:Task|Optimization)\s*:\s*(.+)', line, re.I)
        if m:
            return m.group(1).strip()
    return fallback


def _task_source_from_file(content: str) -> str:
    """Extract the `Source:` tag from the header doc comment.

    Every task must record its upstream origin; a missing tag is a hard
    error, not a silent omission.
    """
    for line in content.splitlines():
        m = re.match(r'^\s*Source:\s*(.+?)\s*$', line)
        if m:
            return m.group(1)
    raise ValueError(
        "Task file has no 'Source:' line in its header. Every task must "
        "record a Source pointer to its upstream origin."
    )


def _script_dir() -> Path:
    return Path(__file__).parent


def _task_dir_skeleton() -> Path:
    """Directory holding the per-task build-infra skeleton files."""
    return _script_dir() / "task_dir"


# Category prefix applied to every generated task directory name.
# The category determines both the output dir name (e.g. "eBPF_Cnum_Alu64Add")
# and the lakefile package name (e.g. "ebpf-alu32add").
CATEGORY_EBPF = "eBPF"
CATEGORY_LLVM = "LLVM"
CATEGORY_SEL4 = "seL4"


def _category_for(task_name: str) -> str:
    """Return the category prefix for a given LEAN_TASK_NAME."""
    if task_name in SEL4_DIRECT_TASKS:
        return CATEGORY_SEL4
    if task_name.startswith(("KB", "DB")):
        return CATEGORY_LLVM
    return CATEGORY_EBPF


def _task_output_dir(output_base: str, task_name: str) -> Path:
    """Return the prefixed output directory for a task."""
    return Path(output_base) / f"{_category_for(task_name)}_{task_name}"


# Fallback lakefile, used only if the skeleton file is missing. All tasks
# use the same package name `vero-task`, matching the root name in the shared
# lake-manifest.json; a mismatch makes Lake treat the manifest as stale and
# re-resolve (re-download) the dependencies.
_LAKEFILE_FALLBACK = '''import Lake
open Lake DSL

package «vero-task» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"


@[default_target]
lean_lib «VeroTask» where
  roots := #[`Task]
'''


def _write_lean_infra(task_dir: Path, task_name: str) -> None:
    """Write lakefile.lean, lean-toolchain, lake-manifest.json.

    All three are static skeleton files copied verbatim from
    template/task_dir/ (every task shares the same lakefile now that the
    package name is uniform). The Mathlib build cache (`.lake/`) is fetched
    at run time by run_bench.py (via `lake exe cache get`) and is never
    committed to the repo, so no `.lake` is created or symlinked here.
    """
    skeleton = _task_dir_skeleton()

    lakefile_src = skeleton / "lakefile.lean"
    if lakefile_src.exists():
        shutil.copy2(lakefile_src, task_dir / "lakefile.lean")
    else:
        (task_dir / "lakefile.lean").write_text(_LAKEFILE_FALLBACK)

    toolchain_src = skeleton / "lean-toolchain"
    if toolchain_src.exists():
        shutil.copy2(toolchain_src, task_dir / "lean-toolchain")
    else:
        (task_dir / "lean-toolchain").write_text("leanprover/lean4:v4.28.0\n")

    manifest_src = skeleton / "lake-manifest.json"
    if manifest_src.exists():
        shutil.copy2(manifest_src, task_dir / "lake-manifest.json")


def _write_check_sh(task_dir: Path) -> None:
    """Copy check_template.sh into task_dir/check.sh."""
    check_src = _task_dir_skeleton() / "check_template.sh"
    check_path = task_dir / "check.sh"
    shutil.copy2(check_src, check_path)
    check_path.chmod(check_path.stat().st_mode | stat.S_IEXEC | stat.S_IXGRP | stat.S_IXOTH)


def _write_provided_hash(task_dir: Path, task_file: str) -> None:
    """Compute and write .provided_hash for the task file."""
    content = (task_dir / task_file).read_text()
    provided_hash = compute_provided_hash(content)
    (task_dir / ".provided_hash").write_text(provided_hash + "\n")


# Shared optimality wording for the cnum+tnum task family. A ⊑-least
# sound RegState does not always exist in the cnum domain (minimum-size
# arc covers can tie and be incomparable), so optimality is stated
# component-wise. See docs/cnum.md for the full rationale.
_CNUM_OPTIMALITY_DESC = (
    "- **Component-wise optimality**: compared against every other sound "
    "and valid `RegState r'`:\n"
    "  - `result.r64.size ≤ r'.r64.size` — the 64-bit cnum is a "
    "minimum-size arc cover,\n"
    "  - `result.r32.size ≤ r'.r32.size` — the 32-bit cnum is a "
    "minimum-size arc cover,\n"
    "  - `result.var_off.mask &&& ~~~r'.var_off.mask = 0` — the tnum "
    "mask is minimal.\n\n"
    "A ⊑-least sound abstraction does not always exist in the cnum "
    "domain (minimum-size arc covers can tie), which is why optimality "
    "is per component rather than `γ(result) ⊆ γ(r')`."
)

_CNUM_DOMAIN_DESC = (
    "The abstract domain is the bpf-next cnum + tnum register state: a "
    "64-bit tnum (`var_off`) plus a 64-bit circular range (`r64`) and a "
    "32-bit circular range over the low 32 bits (`r32`). A cnum "
    "`{base, size}` denotes the wrapping arc `base .. base + size` "
    "(mod 2^w); the reserved encoding `base = size = 2^w - 1` denotes "
    "the empty set, so a full-circle result must use a different base "
    "(the kernel canonicalizes to `base = 0`)."
)


def _cnum_task_description(content: str) -> str:
    """Task description for the cnum+tnum (Cnum_*) task family."""
    if "BranchResult" in content:
        return (
            "Implement the function in the IMPLEMENTATION section so that it "
            "correctly determines the branch outcome (always, never, or unknown) "
            "for the relation specified in the SPEC.\n\n"
            + _CNUM_DOMAIN_DESC + "\n\n"
            "The function receives two abstract register states and must return:\n"
            "- `BranchResult.always` if the relation holds for ALL concrete value pairs\n"
            "- `BranchResult.never` if the relation holds for NO concrete value pairs\n"
            "- `BranchResult.unknown` otherwise\n\n"
            "Then prove correctness in the PROOF section. The theorem in SPEC states "
            "that your implementation's return value is equivalent to the always/never "
            "predicates. You may use the axiomatized tnum helpers (tnumStepUp/Down) "
            "from AXIOMS, and add helper lemmas in AUX."
        )
    elif "RegState × RegState" in content:
        return (
            "Implement the function in the IMPLEMENTATION section so that it "
            "computes the optimal refinement of two register states on the "
            "branch-taken path.\n\n"
            + _CNUM_DOMAIN_DESC + "\n\n"
            "The function receives two abstract register states and must return "
            "a pair `(r1', r2')` satisfying:\n"
            "- **Soundness**: every value in `γ(r1)` that has a partner in "
            "`γ(r2)` satisfying the relation is preserved in `γ(r1')` "
            "(and symmetrically for `r2'`)\n"
            + _CNUM_OPTIMALITY_DESC + "\n\n"
            "Then prove correctness in the PROOF section. "
            "You may use the axiomatized tnum helpers (tnumStepUp/Down) from "
            "AXIOMS, and add helper lemmas in AUX."
        )
    elif "reduced canonical form" in content:
        return (
            "Implement the function in the IMPLEMENTATION section so that it "
            "computes the reduced canonical form of a register state: "
            "synchronize the tnum, the 64-bit cnum, and the 32-bit cnum "
            "against each other (the kernel's `reg_bounds_sync()`).\n\n"
            + _CNUM_DOMAIN_DESC + "\n\n"
            "The function receives a single abstract register state and must "
            "return a `RegState` satisfying:\n"
            "- **Soundness**: every concrete value in `γ(reg)` is also in "
            "`γ(result)`\n"
            + _CNUM_OPTIMALITY_DESC + "\n\n"
            "Then prove correctness in the PROOF section. "
            "You may add helper lemmas in AUX."
        )
    elif "cast" in content.lower():
        return (
            "Implement the function in the IMPLEMENTATION section so that it "
            "computes the optimal abstract state for the given cast operation.\n\n"
            + _CNUM_DOMAIN_DESC + "\n\n"
            "The function receives a single abstract register state and a `size` "
            "parameter (1, 2, or 4 bytes) and must return a `RegState` satisfying:\n"
            "- **Soundness**: every concrete result `op(x, size)` for `x ∈ γ(reg)` "
            "is in `γ(result)`\n"
            + _CNUM_OPTIMALITY_DESC + "\n\n"
            "Then prove correctness in the PROOF section. "
            "You may add helper lemmas in AUX."
        )
    else:  # ALU
        return (
            "Implement the function in the IMPLEMENTATION section so that it "
            "computes the optimal abstract state for the given ALU operation.\n\n"
            + _CNUM_DOMAIN_DESC + "\n\n"
            "The function receives two abstract register states (dst, src) and "
            "must return a `RegState` satisfying:\n"
            "- **Soundness**: every concrete result `op(d, s)` for `d ∈ γ(dst)`, "
            "`s ∈ γ(src)` is in `γ(result)`\n"
            + _CNUM_OPTIMALITY_DESC + "\n\n"
            "Then prove correctness in the PROOF section. "
            "You may add helper lemmas in AUX."
        )


def _task_description(content: str) -> str:
    """Generate task description based on file content."""
    provided, _ = _extract_sections(content)

    if "Cnum64" in content:
        return _cnum_task_description(content)
    elif "reduced product canonical form" in content:
        return (
            "Implement the function in the IMPLEMENTATION section so that it "
            "computes the reduced product canonical form of a register state.\n\n"
            "The function receives a single abstract register state and must return "
            "a `RegState` satisfying:\n"
            "- **Soundness**: every concrete value in `γ(reg)` is also in `γ(result)`\n"
            "- **Component-wise optimality**: `result` is the tightest representation "
            "— for any other `RegState` `r'` that also covers `γ(reg)`, each component "
            "of `result` is at least as tight as the corresponding component of `r'` "
            "(u64/s64/u32/s32 ranges and tnum mask).\n\n"
            "Then prove correctness in the PROOF section. "
            "You may add helper lemmas in AUX."
        )
    elif "cast" in content.lower() and "best abstract transformer" in content:
        return (
            "Implement the function in the IMPLEMENTATION section so that it "
            "computes the optimal abstract state for the given cast operation.\n\n"
            "The function receives a single abstract register state and a `size` "
            "parameter (1, 2, or 4 bytes) and must return a `RegState` satisfying:\n"
            "- **Soundness**: every concrete result `op(x, size)` for `x ∈ γ(reg)` "
            "is in `γ(result)`\n"
            "- **Optimality**: `result` is the best abstract transformer — "
            "the ⊑-least sound abstraction. For any other `RegState` `r'` that "
            "is also sound, `γ(result) ⊆ γ(r')`.\n\n"
            "This is the standard Galois connection optimality condition: "
            "`result = α(f(γ(reg)))`. "
            "You may add helper lemmas in AUX."
        )
    elif "refinement" in content.lower() and "RegState × RegState" in content:
        return (
            "Implement the function in the IMPLEMENTATION section so that it "
            "computes the optimal refinement of two register states on the "
            "branch-taken path.\n\n"
            "The function receives two abstract register states and must return "
            "a pair `(r1', r2')` satisfying:\n"
            "- **Soundness**: every value in `γ(r1)` that has a partner in "
            "`γ(r2)` satisfying the relation is preserved in `γ(r1')` "
            "(and symmetrically for `r2'`)\n"
            "- **Optimality**: `γ(r1')` is contained in `γ(r')` for every "
            "`r'` that is also sound (and symmetrically for `r2'`)\n\n"
            "This is the standard Galois connection optimality condition: "
            "`r1' = α({x ∈ γ(r1) | ∃y ∈ γ(r2), R(x,y)})`. "
            "If the relation is unsatisfiable (no feasible pair exists), the "
            "optimal result is ⊥ (empty gamma). "
            "Then prove correctness in the PROOF section. "
            "You may use the axiomatized tnum helpers (tnumStepUp/Down) from "
            "AXIOMS, and add helper lemmas in AUX."
        )
    elif "tnum" in content.lower() and "validTnum" in content and "best abstract transformer" in content:
        has_const = "non-zero constant" in content
        if has_const:
            return (
                "Implement the function in the IMPLEMENTATION section so that it "
                "computes the optimal tnum for the given operation with a non-zero "
                "constant divisor.\n\n"
                "The function receives a tnum and a non-zero `BitVec 64` constant, "
                "and must return a `Tnum` satisfying:\n"
                "- **Well-formedness**: `(result.value &&& result.mask) = 0`\n"
                "- **Soundness**: for every `x ∈ γ(tnum)`, `op(x, c) ∈ γ(result)`\n"
                "- **Optimality**: `result` is the ⊑-least sound abstraction — "
                "for any other valid tnum `r'` that is also sound, "
                "`γ(result) ⊆ γ(r')`.\n\n"
                "This is the standard Galois connection optimality condition: "
                "`result = α(f(γ(tnum)))`. "
                "You may add helper lemmas in AUX."
            )
        else:
            return (
                "Implement the function in the IMPLEMENTATION section so that it "
                "computes the optimal tnum for the given binary operation on two tnums.\n\n"
                "The function receives two tnums and must return a `Tnum` satisfying:\n"
                "- **Well-formedness**: `(result.value &&& result.mask) = 0`\n"
                "- **Soundness**: for every `x ∈ γ(a)` and `y ∈ γ(b)`, "
                "`op(x, y) ∈ γ(result)`\n"
                "- **Optimality**: `result` is the ⊑-least sound abstraction — "
                "for any other valid tnum `r'` that is also sound, "
                "`γ(result) ⊆ γ(r')`.\n\n"
                "This is the standard Galois connection optimality condition: "
                "`result = α(f(γ(a) × γ(b)))`. "
                "You may add helper lemmas in AUX."
            )
    elif "ALU" in content and "best abstract transformer" in content:
        return (
            "Implement the function in the IMPLEMENTATION section so that it "
            "computes the optimal abstract state for the given ALU operation.\n\n"
            "The function receives two abstract register states (dst, src) and "
            "must return a `RegState` satisfying:\n"
            "- **Soundness**: every concrete result `op(d, s)` for `d ∈ γ(dst)`, "
            "`s ∈ γ(src)` is in `γ(result)`\n"
            "- **Optimality**: `result` is the best abstract transformer — "
            "the ⊑-least sound abstraction. For any other `RegState` `r'` that "
            "is also sound, `γ(result) ⊆ γ(r')`.\n\n"
            "This is the standard Galois connection optimality condition: "
            "`result = α(f(γ(dst) × γ(src)))`. "
            "You may add helper lemmas in AUX."
        )
    elif "AXIOMS" in provided and "BranchResult" in content:
        return (
            "Implement the function in the IMPLEMENTATION section so that it "
            "correctly determines the branch outcome (always, never, or unknown) "
            "for the relation specified in the SPEC.\n\n"
            "The function receives two abstract register states and must return:\n"
            "- `BranchResult.always` if the relation holds for ALL concrete value pairs\n"
            "- `BranchResult.never` if the relation holds for NO concrete value pairs\n"
            "- `BranchResult.unknown` otherwise\n\n"
            "Then prove correctness in the PROOF section. The theorem in SPEC states "
            "that your implementation's return value is equivalent to the always/never "
            "predicates. You may use the axiomatized tnum helpers (tnumStepUp/Down) "
            "from AXIOMS, and add helper lemmas in AUX."
        )
    elif "LLVM KnownBits" in content and "inKBGamma" in content:
        # Look up the per-task description line from operator dicts.
        task_desc = ""
        for ops_dict in (KB_BIN_OPS, KB_BIN_DIV_OPS, KB_BIN_DIV_EXACT_OPS,
                         KB_BIN_MUL_FLAGS_OPS, KB_UNARY_FLAG_OPS):
            for subs in ops_dict.values():
                # Match "def <funcName> " to avoid substring false positives
                # (e.g., "kbMul" matching inside "kbMulSelf").
                if f"def {subs['LEAN_FUNC_NAME']} " in content:
                    task_desc = subs.get("_INSTRUCTION_DESC", "")
                    break
            if task_desc:
                break
        return (
            "Implement the function in the IMPLEMENTATION section so that it "
            "computes the optimal KnownBits for the given operation.\n\n"
            + (task_desc + "\n\n" if task_desc else "")
            + "The result must satisfy:\n"
            "- **Well-formedness**: `(result.zero &&& result.one) = 0`\n"
            "- **Soundness**: for every concrete input(s) in the "
            "concretization (satisfying any flag preconditions), the concrete "
            "result is in the concretization of the output KnownBits\n"
            "- **Optimality**: the result is the ⊑-least sound abstraction "
            "— for any other valid KnownBits `r'` that is also sound, "
            "`γ(result) ⊆ γ(r')`\n\n"
            "This is the standard Galois connection optimality condition: "
            "`result = α(f(γ(a) × γ(b)))`. "
            "You may add helper lemmas in AUX."
        )
    elif "LLVM DemandedBits" in content and "flipBit" in content:
        return (
            "Implement the function in the IMPLEMENTATION section so that it "
            "computes the optimal backward demanded bits for the given "
            "operation.\n\n"
            "The function receives demanded output bits, KnownBits of "
            "the input(s), and any flag parameters. It returns demanded "
            "bit masks for the input(s).\n\n"
            "The result must satisfy:\n"
            "- **Unknown-bits constraint**: demanded bits must be a subset "
            "of the unknown bits (bits where neither `zero` nor `one` is "
            "set in the KnownBits)\n"
            "- **Soundness**: for every bit NOT marked as demanded, "
            "flipping that bit in any valid concrete input (where the "
            "flipped value is also valid and satisfies flag preconditions) "
            "must not change any demanded output bit\n"
            "- **Optimality**: every bit marked as demanded IS truly "
            "demanded — there exist concrete inputs where flipping that "
            "bit changes a demanded output bit\n\n"
            "This is the backward dual of the Galois connection: find the "
            "minimal set of input bits that can affect the demanded output "
            "bits. You may add helper lemmas in AUX."
        )
    else:
        return (
            "Implement the function in the IMPLEMENTATION section and prove "
            "correctness in the PROOF section.\n"
            "The provided theorem states that your implementation satisfies "
            "all postconditions. "
            "You may add helper lemmas in AUX."
        )


def _complexity_rule(o1_required) -> str:
    """Return the complexity rule text for the instruction template.

    o1_required: True = O(1) required (linear-ish operators), False = no
    hard bound (nonlinear operators: mul, div, mod, mulh, ...) but brute
    force still scores zero, None = no rule (seL4; the algorithm target
    is described in each task's spec).
    """
    if o1_required is None:
        return ""
    if o1_required:
        return (
            "5. The **implementation runtime must be O(1)** "
            "(bounded loops up to 64 bit-iterations OK). Recursion "
            "depth ≤ 64 is not the same as bounded time: if running "
            "time scales with the *number* of unknown bits (not their "
            "*position*), it is brute force and a FAIL."
        )
    return (
        "5. **No hard complexity bound is imposed for this operator** --- "
        "an optimal transfer function here may genuinely need more than "
        "constant work. But **brute force scores ZERO**: we expect an "
        "insightful algorithm, and the human review rejects any "
        "implementation whose running time scales with the number of "
        "concrete values represented rather than with the bit-width. "
        "This includes enumerating the concretization, "
        "O(2^popcount(mask)) case explosion, and **tree recursion over "
        "the 64 bit positions** --- recursion that branches at each bit "
        "is 2^64 work even though it is 64 levels deep. "
    )


def _write_instruction(task_dir: Path, task_file: str, dir_name: str,
                       o1_required=True) -> None:
    """Generate INSTRUCTION.md from instruction_template.md and task file content."""
    template = (_task_dir_skeleton() / "instruction_template.md").read_text()
    content = (task_dir / task_file).read_text()

    provided, editable = _extract_sections(content)
    title = _task_title_from_file(content, fallback=dir_name)
    source = _task_source_from_file(content)
    desc = _task_description(content)

    complexity_rule = _complexity_rule(o1_required)
    subs = {
        "TASK_TITLE": title,
        "TASK_SOURCE": source,
        "TASK_DIR_NAME": dir_name,
        "PROVIDED_SECTIONS": "\n".join(f"- **{s}**" for s in provided),
        "EDITABLE_SECTIONS": "\n".join(f"- **{s}**" for s in editable),
        "TASK_DESCRIPTION": desc,
        "COMPLEXITY_RULE": complexity_rule,
        # The complexity rule, when present, is list item 5; the
        # notes rule follows it.
        "NOTES_RULE_NUM": "6" if complexity_rule else "5",
    }
    (task_dir / "INSTRUCTION.md").write_text(expand_template(template, subs))


def _generate_from_template(
    template_file: str,
    subs: Dict[str, str],
    output_base: str,
) -> Path:
    """Generate a task directory from a template file via variable expansion."""
    tmpl_path = _script_dir() / template_file
    if not tmpl_path.exists():
        raise FileNotFoundError(f"Template not found: {tmpl_path}")

    content = tmpl_path.read_text()
    expanded = expand_template(content, subs)

    remaining = find_template_variables(expanded)
    if remaining:
        raise ValueError(
            f"Unexpanded variables in {subs.get('LEAN_TASK_NAME', '?')}: {remaining}"
        )

    task_name = subs["LEAN_TASK_NAME"]
    task_dir = _task_output_dir(output_base, task_name)
    task_dir.mkdir(parents=True, exist_ok=True)

    # Drop any legacy bare-name directory for this task.
    legacy_dir = Path(output_base) / task_name
    if legacy_dir.exists() and legacy_dir != task_dir:
        shutil.rmtree(legacy_dir)

    (task_dir / "Task.lean").write_text(expanded)
    _write_lean_infra(task_dir, task_name)
    _write_check_sh(task_dir)
    _write_provided_hash(task_dir, "Task.lean")
    o1_required = subs.get("_O1_REQUIRED", True)
    _write_instruction(task_dir, "Task.lean", task_name, o1_required=o1_required)

    return task_dir


# eBPF operator dicts paired with their template files and --list labels.
_EBPF_TASK_GROUPS = [
    ("BranchTaken.lean",      "branch_taken", None),   # BRANCH_TAKEN_OPS, filled below
    ("CnumBranchTaken.lean",  "cnum_branch ", None),
    ("RefineCond.lean",       "refine_cond ", None),
    ("CnumRefineCond.lean",   "cnum_refine ", None),
    ("AluOp.lean",            "alu_op      ", None),
    ("CnumAluOp.lean",        "cnum_alu_op ", None),
    ("TnumBinOp.lean",        "tnum_bin_op ", None),
    ("TnumConstOp.lean",      "tnum_const  ", None),
    ("CnumCastOp.lean",       "cnum_cast   ", None),
    ("CnumBoundsSync.lean",   "cnum_sync   ", None),
]


def _ebpf_task_groups():
    """(ops_dict, template_file, label) triples for all eBPF families."""
    dicts = [
        BRANCH_TAKEN_OPS, CNUM_BRANCH_TAKEN_OPS,
        REFINE_COND_OPS, CNUM_REFINE_COND_OPS,
        ALU_OPS, CNUM_ALU_OPS,
        TNUM_BIN_OPS, TNUM_CONST_OPS,
        CNUM_CAST_OPS, CNUM_BOUNDS_SYNC_OPS,
    ]
    return [
        (ops, template, label)
        for ops, (template, label, _) in zip(dicts, _EBPF_TASK_GROUPS)
    ]


def generate_ebpf_task(operator: str, output_base: str) -> Path:
    """Generate an eBPF task from whichever family dict owns `operator`."""
    for ops, template, _ in _ebpf_task_groups():
        if operator in ops:
            task_dir = _generate_from_template(template, ops[operator],
                                               output_base)
            print(f"  Generated: {task_dir}/")
            return task_dir
    raise KeyError(f"Unknown eBPF operator: {operator}")


def _generate_llvm_task(template_file: str, ops_dict: dict,
                        operator: str, output_base: str) -> Path:
    """Generate an LLVM KnownBits/DemandedBits task from a template."""
    subs = ops_dict[operator]
    task_dir = _generate_from_template(template_file, subs, output_base)
    print(f"  Generated: {task_dir}/")
    return task_dir


def generate_kb_bin_task(operator: str, output_base: str) -> Path:
    """Generate a KBBinOp task from template/KBBinOp.lean."""
    return _generate_llvm_task("KBBinOp.lean", KB_BIN_OPS,
                               operator, output_base)


def generate_kb_bin_div_task(operator: str, output_base: str) -> Path:
    """Generate a KBBinOpDiv task from template/KBBinOpDiv.lean."""
    return _generate_llvm_task("KBBinOpDiv.lean", KB_BIN_DIV_OPS,
                               operator, output_base)


def generate_kb_bin_div_exact_task(operator: str, output_base: str) -> Path:
    """Generate a KBBinOpDivExact task from template/KBBinOpDivExact.lean."""
    return _generate_llvm_task("KBBinOpDivExact.lean", KB_BIN_DIV_EXACT_OPS,
                               operator, output_base)


def generate_kb_bin_mul_flags_task(operator: str, output_base: str) -> Path:
    """Generate a KBBinOpMulFlags task from template/KBBinOpMulFlags.lean."""
    return _generate_llvm_task("KBBinOpMulFlags.lean", KB_BIN_MUL_FLAGS_OPS,
                               operator, output_base)


def generate_kb_unary_flag_task(operator: str, output_base: str) -> Path:
    """Generate a KBUnaryOpFlag task from template/KBUnaryOpFlag.lean."""
    return _generate_llvm_task("KBUnaryOpFlag.lean", KB_UNARY_FLAG_OPS,
                               operator, output_base)


def generate_db_bin_flags_task(operator: str, output_base: str) -> Path:
    """Generate a DBBinOpFlags task from template/DBBinOpFlags.lean."""
    return _generate_llvm_task("DBBinOpFlags.lean", DB_BIN_FLAGS_OPS,
                               operator, output_base)


def generate_db_bin_exact_task(operator: str, output_base: str) -> Path:
    """Generate a DBBinOpExact task from template/DBBinOpExact.lean."""
    return _generate_llvm_task("DBBinOpExact.lean", DB_BIN_EXACT_OPS,
                               operator, output_base)


def generate_db_bin_task(operator: str, output_base: str) -> Path:
    """Generate a DBBinOp task from template/DBBinOp.lean."""
    return _generate_llvm_task("DBBinOp.lean", DB_BIN_OPS,
                               operator, output_base)


def generate_db_unary_flags_task(operator: str, output_base: str) -> Path:
    """Generate a DBUnaryOpFlags task from template/DBUnaryOpFlags.lean."""
    return _generate_llvm_task("DBUnaryOpFlags.lean", DB_UNARY_FLAGS_OPS,
                               operator, output_base)


_LLVM_TASK_GROUPS = [
    (KB_BIN_OPS, generate_kb_bin_task),
    (KB_BIN_DIV_OPS, generate_kb_bin_div_task),
    (KB_BIN_DIV_EXACT_OPS, generate_kb_bin_div_exact_task),
    (KB_BIN_MUL_FLAGS_OPS, generate_kb_bin_mul_flags_task),
    (KB_UNARY_FLAG_OPS, generate_kb_unary_flag_task),
    (DB_BIN_FLAGS_OPS, generate_db_bin_flags_task),
    (DB_BIN_EXACT_OPS, generate_db_bin_exact_task),
    (DB_BIN_OPS, generate_db_bin_task),
    (DB_UNARY_FLAGS_OPS, generate_db_unary_flags_task),
]


def _direct_source(dir_name: str) -> Path:
    """Source Task.lean for a direct (hand-maintained) task.

    Direct tasks keep their Task.lean under template/<category>/<name>/, so tasks/
    is fully regenerable: `make gen` copies the source into place.
    """
    return _script_dir() / _category_for(dir_name) / dir_name / "Task.lean"


def generate_direct_task(dir_name: str, output_base: str) -> Path:
    """Generate a direct (hand-maintained) task from its template source.

    Copies template/<category>/<name>/Task.lean into the task directory, then
    writes the build infra around it.
    """
    src = _direct_source(dir_name)
    if not src.exists():
        raise FileNotFoundError(
            f"Direct task source not found: {src}\n"
            f"  Direct tasks are maintained under template/<category>/<name>/."
        )
    task_dir = _task_output_dir(output_base, dir_name)
    task_dir.mkdir(parents=True, exist_ok=True)
    shutil.copy2(str(src), str(task_dir / "Task.lean"))

    _write_lean_infra(task_dir, dir_name)
    _write_check_sh(task_dir)
    _write_provided_hash(task_dir, "Task.lean")
    # seL4 direct tasks have no complexity requirement; BPF direct tasks need O(1)
    if dir_name in SEL4_DIRECT_TASKS:
        o1 = None
    elif dir_name in BPF_DIRECT_TASKS:
        o1 = True
    else:
        o1 = True
    _write_instruction(task_dir, "Task.lean", dir_name, o1_required=o1)

    print(f"  Infra for: {task_dir}/")
    return task_dir


def generate_all_tasks(output_base: str) -> None:
    """Generate all task directories."""
    print(f"Generating Lean4 tasks into: {output_base}")
    count = 0
    for ops_dict, _, _ in _ebpf_task_groups():
        for operator in ops_dict:
            generate_ebpf_task(operator, output_base)
            count += 1
    for ops_dict, gen_func in _LLVM_TASK_GROUPS:
        for operator in ops_dict:
            gen_func(operator, output_base)
            count += 1
    for dir_name in DIRECT_TASKS:
        generate_direct_task(dir_name, output_base)
        count += 1
    print(f"\nProcessed {count} task directories.")


def list_available_operators() -> list:
    result = []
    for ops_dict, _, _ in _ebpf_task_groups():
        result += list(ops_dict.keys())
    for ops_dict, _ in _LLVM_TASK_GROUPS:
        result += list(ops_dict.keys())
    result += DIRECT_TASKS
    return result


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(
        description="Generate Lean4 BPF verification tasks from templates"
    )
    parser.add_argument("output_dir", nargs="?", default="tasks",
                        help="Output base directory (default: tasks)")
    parser.add_argument("operator", nargs="?", default=None,
                        help="Single operator to generate (omit with --all)")
    parser.add_argument("--all", action="store_true",
                        help="Generate all tasks")
    parser.add_argument("--list", action="store_true",
                        help="List available operators")

    args = parser.parse_args()

    if args.list:
        def _dir(task_name):
            return f"{_category_for(task_name)}_{task_name}"
        print("Available operators:")
        for ops_dict, _, label in _ebpf_task_groups():
            for op in ops_dict:
                name = ops_dict[op]["LEAN_TASK_NAME"]
                print(f"  {op:25s}  [{label}]  -> {_dir(name)}/")
        _llvm_labels = [
            (KB_BIN_OPS, "kb_bin_op   "),
            (KB_BIN_DIV_OPS, "kb_bin_div  "),
            (KB_BIN_DIV_EXACT_OPS, "kb_div_exact"),
            (KB_BIN_MUL_FLAGS_OPS, "kb_mul_flags"),
            (KB_UNARY_FLAG_OPS, "kb_unary_flg"),
            (DB_BIN_FLAGS_OPS, "db_bin_flags"),
            (DB_BIN_EXACT_OPS, "db_bin_exact"),
            (DB_BIN_OPS, "db_bin_op   "),
            (DB_UNARY_FLAGS_OPS, "db_unary_flg"),
        ]
        for ops_dict, label in _llvm_labels:
            for op in ops_dict:
                name = ops_dict[op]["LEAN_TASK_NAME"]
                print(f"  {op:25s}  [{label}]  -> {_dir(name)}/")
        for d in DIRECT_TASKS:
            print(f"  {d:25s}  [direct      ]  -> {_dir(d)}/")
    elif args.all:
        generate_all_tasks(args.output_dir)
    elif args.operator:
        if any(args.operator in ops for ops, _, _ in _ebpf_task_groups()):
            generate_ebpf_task(args.operator, args.output_dir)
        else:
            # Check LLVM task groups
            found = False
            for ops_dict, gen_func in _LLVM_TASK_GROUPS:
                if args.operator in ops_dict:
                    gen_func(args.operator, args.output_dir)
                    found = True
                    break
            if not found:
                if args.operator in DIRECT_TASKS:
                    generate_direct_task(args.operator, args.output_dir)
                else:
                    parser.error(f"Unknown operator: {args.operator}")
    else:
        parser.error("Specify an operator name, or use --all to generate all tasks.")
