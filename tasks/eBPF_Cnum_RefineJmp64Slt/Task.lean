/-
  BPF cnum refinement verification task: Less Than, signed (64-bit)
  Operator: JMP64_SLT
  Source: Linux eBPF verifier (bpf-next cnum domain), kernel/bpf/verifier.c (regs_refine_cond_op)

  Given two abstract register states in the bpf-next cnum + tnum domain,
  refine both to optimally contain only values that can participate in
  the relation x.toInt < y.toInt.
  The results must be sound and component-wise optimal: their cnums are
  minimum-size arc covers and their tnum masks are minimal among all
  sound refinements. (A ⊑-least sound RegState does not always exist in
  the cnum domain — minimum-size arc covers can tie — hence the
  component-wise formulation.)
-/
import Mathlib.Tactic
import Plausible

namespace BPF

-- === BEGIN: DEFINITIONS (provided) ===

/-- A tnum represents a set of 64-bit values:
    known bits are fixed by `value`, unknown bits are indicated by `mask`. -/
structure Tnum where
  value : BitVec 64
  mask  : BitVec 64

/-- A 64-bit cnum (circular number) represents a contiguous arc of the
    2^64 value circle: the values `base, base + 1, ..., base + size`
    (wrapping mod 2^64), i.e. `size + 1` consecutive values.
    The reserved encoding `base = size = 2^64 - 1` denotes the empty set;
    the full circle is representable with any other base and
    `size = 2^64 - 1`. -/
structure Cnum64 where
  base : BitVec 64
  size : BitVec 64

/-- A 32-bit cnum: an arc on the 2^32 value circle, with the analogous
    reserved empty encoding `base = size = 2^32 - 1`. -/
structure Cnum32 where
  base : BitVec 32
  size : BitVec 32

/-- Abstract register state of the bpf-next verifier: a 64-bit tnum plus
    64-bit and 32-bit circular ranges. The 32-bit cnum constrains the
    low 32 bits of the value. -/
structure RegState where
  var_off : Tnum
  r64     : Cnum64
  r32     : Cnum32

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

/-- A value `x` satisfies a 64-bit tnum constraint. -/
def satisfiesTnum64 (x tval tmask : BitVec 64) : Prop :=
  (x &&& ~~~tmask) = tval

/-- The reserved empty encoding of a 64-bit cnum. -/
def cnum64IsEmpty (c : Cnum64) : Prop :=
  c.base = BitVec.allOnes 64 ∧ c.size = BitVec.allOnes 64

/-- The reserved empty encoding of a 32-bit cnum. -/
def cnum32IsEmpty (c : Cnum32) : Prop :=
  c.base = BitVec.allOnes 32 ∧ c.size = BitVec.allOnes 32

/-- A value `x` is in the concretization of a 64-bit cnum:
    `x` lies on the arc, i.e. `x - base ≤ size` (wrapping subtraction). -/
def inCnum64Gamma (c : Cnum64) (x : BitVec 64) : Prop :=
  ¬ cnum64IsEmpty c ∧ x - c.base ≤ c.size

/-- A value `x` is in the concretization of a 32-bit cnum. -/
def inCnum32Gamma (c : Cnum32) (x : BitVec 32) : Prop :=
  ¬ cnum32IsEmpty c ∧ x - c.base ≤ c.size

/-- A concrete value `x` is in the gamma (concretization) of a register
    state iff it satisfies ALL three constraints: the tnum, the 64-bit
    cnum, and the 32-bit cnum (on the low 32 bits of `x`). -/
def inGamma (reg : RegState) (x : BitVec 64) : Prop :=
  satisfiesTnum64 x reg.var_off.value reg.var_off.mask ∧
  inCnum64Gamma reg.r64 x ∧
  inCnum32Gamma reg.r32 (x.truncate 32)

/-- A register state is well-formed if its tnum is consistent.
    (Every cnum encoding is meaningful — an arc or the reserved empty
    encoding — so no further conditions are needed.) -/
def validReg (reg : RegState) : Prop :=
  (reg.var_off.value &&& reg.var_off.mask) = 0

-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===

/-- Smallest value > z satisfying a tnum. -/
axiom tnumStepUp (tval tmask z : BitVec 64) : BitVec 64

axiom tnumStepUp_spec (tval tmask z : BitVec 64)
    (h_consistent : (tval &&& tmask) = 0)
    (h_lo : tval ≤ z)
    (h_hi : z < (tval ||| tmask)) :
    tval ≤ tnumStepUp tval tmask z ∧
    tnumStepUp tval tmask z ≤ (tval ||| tmask) ∧
    satisfiesTnum64 (tnumStepUp tval tmask z) tval tmask ∧
    z < tnumStepUp tval tmask z ∧
    (∀ (w : BitVec 64), satisfiesTnum64 w tval tmask → z < w →
      tnumStepUp tval tmask z ≤ w)

/-- Largest value < z satisfying a tnum. -/
axiom tnumStepDown (tval tmask z : BitVec 64) : BitVec 64

axiom tnumStepDown_spec (tval tmask z : BitVec 64)
    (h_consistent : (tval &&& tmask) = 0)
    (h_lo : tval < z)
    (h_hi : z ≤ (tval ||| tmask)) :
    tval ≤ tnumStepDown tval tmask z ∧
    tnumStepDown tval tmask z ≤ (tval ||| tmask) ∧
    satisfiesTnum64 (tnumStepDown tval tmask z) tval tmask ∧
    tnumStepDown tval tmask z < z ∧
    (∀ (w : BitVec 64), satisfiesTnum64 w tval tmask → w < z →
      w ≤ tnumStepDown tval tmask z)

/-- Refine register states on the branch-taken path for Less Than, signed (64-bit). -/
def refineCondJmp64Slt (reg1 reg2 : RegState) : RegState × RegState :=
-- === END: AXIOMS ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry

-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: SPEC (provided) ===

theorem refineCondJmp64Slt_correct (reg1 reg2 : RegState)
    (hv1 : validReg reg1) (hv2 : validReg reg2)
    (hfeas : ∃ x y, inGamma reg1 x ∧ inGamma reg2 y ∧ x.toInt < y.toInt) :
    let (r1', r2') := refineCondJmp64Slt reg1 reg2
    -- Well-formedness: results are valid register states
    validReg r1' ∧ validReg r2' ∧
    -- Soundness for r1': every feasible value is preserved
    (∀ x, inGamma reg1 x → (∃ y, inGamma reg2 y ∧ x.toInt < y.toInt) → inGamma r1' x) ∧
    -- Soundness for r2': every feasible value is preserved
    (∀ y, inGamma reg2 y → (∃ x, inGamma reg1 x ∧ x.toInt < y.toInt) → inGamma r2' y) ∧
    -- Optimality for r1' (component-wise): against every sound valid r',
    -- r1's cnums are minimum-size arc covers and its tnum mask is minimal
    (∀ r', validReg r' → (∀ x, inGamma reg1 x → (∃ y, inGamma reg2 y ∧ x.toInt < y.toInt) → inGamma r' x) →
      r1'.r64.size ≤ r'.r64.size ∧
      r1'.r32.size ≤ r'.r32.size ∧
      (r1'.var_off.mask &&& ~~~r'.var_off.mask) = 0) ∧
    -- Optimality for r2' (component-wise)
    (∀ r', validReg r' → (∀ y, inGamma reg2 y → (∃ x, inGamma reg1 x ∧ x.toInt < y.toInt) → inGamma r' y) →
      r2'.r64.size ≤ r'.r64.size ∧
      r2'.r32.size ≤ r'.r32.size ∧
      (r2'.var_off.mask &&& ~~~r'.var_off.mask) = 0) := by
-- === END: SPEC ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end BPF
