/-
  seL4 Optimization Task: Thread State Batch Setter
  Source: seL4 thread_state bitfield, include/object/structures_64.bf; slowpath setters vs fastpath mset_ variants (src/fastpath/fastpath.c)
  Original: 6 sequential read-modify-write operations on bitfield word
  Optimized: Single composite write

  The seL4 slowpath calls 6 individual bitfield setters on thread_state.words[0].
  The fastpath already has mset_ variants. Prove that a single composite write
  produces the same result as the 6 sequential RMW operations.

  You must also prove the batch setter is equivalent to
  applying 6 sequential setField operations.
-/
import Mathlib
import Std

namespace seL4.ThreadStateBatch

-- === BEGIN: DEFINITIONS (provided) ===

/-- Thread state is a 64-bit word with packed bitfields.
    Layout (from structures_64.bf):
      bits [0..3]   : tsType            (4 bits)
      bits [4..4]   : blockingIPCIsCall  (1 bit)
      bits [5..5]   : blockingIPCCanGrant (1 bit)
      bits [6..6]   : blockingIPCCanGrantReply (1 bit)
      bits [7..7]   : tcbQueued          (1 bit)
      bits [8..15]  : blockingIPCBadge   (8 bits, simplified)
      bits [16..63] : blockingObject     (48 bits)
-/
abbrev ThreadStateWord := BitVec 64

/-- Field descriptor: start bit and width. -/
structure FieldDesc where
  start : Nat
  width : Nat
  h_valid : start + width ≤ 64

/-- The 6 fields in thread_state.words[0]. -/
def tsTypeField       : FieldDesc := ⟨0,  4,  by omega⟩
def isCallField       : FieldDesc := ⟨4,  1,  by omega⟩
def canGrantField     : FieldDesc := ⟨5,  1,  by omega⟩
def canGrantReplyField: FieldDesc := ⟨6,  1,  by omega⟩
def badgeField        : FieldDesc := ⟨8,  8,  by omega⟩
def blockingObjField  : FieldDesc := ⟨16, 48, by omega⟩

/-- Create a bitmask for a field. -/
def fieldMask (fd : FieldDesc) : BitVec 64 :=
  (BitVec.allOnes fd.width).zeroExtend 64 <<< fd.start

/-- Single field read-modify-write: clear field bits then set new value. -/
def setField (w : ThreadStateWord) (fd : FieldDesc) (val : BitVec 64) : ThreadStateWord :=
  (w &&& ~~~(fieldMask fd)) ||| ((val <<< fd.start) &&& fieldMask fd)

/-- Read back a field value from a word. -/
def readField (w : ThreadStateWord) (fd : FieldDesc) : BitVec 64 :=
  (w >>> fd.start) &&& (BitVec.allOnes fd.width).zeroExtend 64

-- === END: DEFINITIONS ===

-- === BEGIN: PREDICATES (provided) ===

/-- Values fit within their respective field widths. -/
def valuesInRange (tsType blockingObj badge isCall canGrant canGrantReply : BitVec 64) : Prop :=
  tsType.toNat < 2^4 ∧
  blockingObj.toNat < 2^48 ∧
  badge.toNat < 2^8 ∧
  isCall.toNat < 2^1 ∧
  canGrant.toNat < 2^1 ∧
  canGrantReply.toNat < 2^1

-- === END: PREDICATES ===

-- === BEGIN: AXIOMS (provided) ===

-- No additional axioms needed. Pure bitwise reasoning.

-- === END: AXIOMS ===

-- === BEGIN: SPEC (provided) ===

/-- Optimized single composite write. Constructs the entire word in one expression
    without reading the old value (since all fields are written). -/
def batchSet (w : ThreadStateWord)
    (tsType blockingObj badge : BitVec 64)
    (isCall canGrant canGrantReply : BitVec 64) : ThreadStateWord :=
-- === END: SPEC ===
-- === BEGIN: IMPLEMENTATION (editable) ===
  sorry
-- === END: IMPLEMENTATION ===

-- === BEGIN: AUX (editable) ===
-- === END: AUX ===

-- === BEGIN: THEOREM (provided) ===

/-- The batch setter correctly sets each field, preserves bit 7 (tcbQueued),
    and is equivalent to 6 sequential setField operations. -/
theorem batchSet_correct
    (w : ThreadStateWord)
    (tsType blockingObj badge isCall canGrant canGrantReply : BitVec 64)
    (h_range : valuesInRange tsType blockingObj badge isCall canGrant canGrantReply) :
    let result := batchSet w tsType blockingObj badge isCall canGrant canGrantReply
    readField result tsTypeField = tsType ∧
    readField result isCallField = isCall ∧
    readField result canGrantField = canGrant ∧
    readField result canGrantReplyField = canGrantReply ∧
    readField result badgeField = badge ∧
    readField result blockingObjField = blockingObj ∧
    result.getLsbD 7 = w.getLsbD 7 ∧
    -- Equivalence with sequential setField operations
    result = setField (setField (setField (setField (setField (setField w
        tsTypeField tsType)
        blockingObjField blockingObj)
        badgeField badge)
        isCallField isCall)
        canGrantField canGrant)
        canGrantReplyField canGrantReply ∧
    -- Functional determinism: any word satisfying all field reads and
    -- preserving bit 7 must equal the result.
    (∀ r' : ThreadStateWord,
      readField r' tsTypeField = tsType →
      readField r' isCallField = isCall →
      readField r' canGrantField = canGrant →
      readField r' canGrantReplyField = canGrantReply →
      readField r' badgeField = badge →
      readField r' blockingObjField = blockingObj →
      r'.getLsbD 7 = w.getLsbD 7 →
      r' = result) ∧
    -- Order independence: any permutation of the 6 sequential setField
    -- operations yields the same result (fields are non-overlapping).
    result = setField (setField (setField (setField (setField (setField w
        blockingObjField blockingObj)
        tsTypeField tsType)
        isCallField isCall)
        badgeField badge)
        canGrantReplyField canGrantReply)
        canGrantField canGrant ∧
    -- Idempotence on one field when writing the same value.
    setField result tsTypeField tsType = result := by
-- === END: THEOREM ===
-- === BEGIN: PROOF (editable) ===
  sorry
-- === END: PROOF ===

end seL4.ThreadStateBatch
