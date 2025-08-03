import Mathlib

namespace EVM

/-! # Base EVM Trace Data Structures

This file defines the minimal data types required to describe execution
traces of EVM transactions.  These will be used to build the base execution
category `𝓔_EVM` in later phases. -/

/-- A **very small placeholder** set of EVM op-codes.  The list will be
extended as the model matures. -/
inductive OpCode
  | ADD
  | SUB
  | MUL
  | DIV
  | PUSH (n : Nat)
  | POP
  | CALL
  | RETURN
  deriving Repr, DecidableEq

/-- Execution status after running an EVM trace. -/
inductive ExecStatus
  | success  -- ^ The trace terminated without reverting.
  | revert   -- ^ Execution reverted (e.g. via `REVERT` opcode).
  deriving Repr, DecidableEq

/-- A _state diff_ summarises the storage & balance changes produced by the
trace.  For now we leave it abstract; later we will refine it into concrete
maps from addresses/storage slots to new values. -/
structure StateDiff where
  updates : List String := []
  deriving Repr, DecidableEq

/-- An **EVM execution trace**: a list of op-codes, the cumulative gas used,
the resulting state diff, and a status flag. -/
structure Trace where
  ops    : List OpCode
  gas    : Nat
  diff   : StateDiff
  status : ExecStatus
  deriving Repr, DecidableEq

end EVM 