import DSL.Syntax
import Optimization.GasEnriched

/-!
# Type Checking and Semantic Analysis for DSL

This file implements type checking, constraint validation, and semantic
analysis for DSL programs before compilation to Lean terms.
-/

namespace DSL

open Optimization

/-- State tracked during execution for type checking. -/
structure State where
  currentChain : Chain
  currentBlock : ℕ
  balances : Token → ℚ  -- Token balances
  borrowed : List (Token × ℚ × Protocol)  -- Outstanding borrows
  gasUsed : ℕ

/-- Initial state for type checking. -/
def State.init (chain : Chain) : State := {
  currentChain := chain
  currentBlock := 0
  balances := fun _ => 0
  borrowed := []
  gasUsed := 0
}

/-- Errors that can occur during type checking. -/
inductive TypeError
  | insufficientBalance (token : Token) (required available : ℚ)
  | wrongChain (expected actual : Chain)
  | unrepaidBorrow (token : Token) (amount : ℚ) (protocol : Protocol)
  | deadlineExceeded (limit actual : ℕ)
  | invalidSwap (reason : String)
  | bridgeUnavailable (from to : Chain)
  deriving Repr

/-- Result of type checking. -/
abbrev CheckResult := Except TypeError State

/-- Enhanced gas estimation using categorical optimization -/
def estimateGas : Action → ℕ := baseGasCost

/-- Estimate block delay for an action. -/
def estimateDelay : Action → ℕ
  | Action.bridge Chain.polygon Chain.arbitrum _ _ => 5
  | Action.bridge Chain.arbitrum Chain.polygon _ _ => 5
  | Action.bridge _ _ _ _ => 10  -- Conservative default
  | _ => 0  -- Same-chain actions are instant

/-- Type check a single action. -/
def checkAction (a : Action) (s : State) : CheckResult :=
  match a with
  | Action.borrow amount token protocol =>
      -- Record the borrow
      let s' := { s with
        balances := fun t => if t = token then s.balances t + amount else s.balances t
        borrowed := (token, amount, protocol) :: s.borrowed
        gasUsed := s.gasUsed + estimateGas a
        currentBlock := s.currentBlock + estimateDelay a
      }
      Except.ok s'
  
  | Action.repay amount token protocol =>
      -- Check sufficient balance
      if s.balances token < amount then
        Except.error (TypeError.insufficientBalance token amount (s.balances token))
      else
        -- Remove from borrowed list
        let borrowed' := s.borrowed.filter (fun (t, a, p) => !(t = token ∧ a = amount ∧ p = protocol))
        let s' := { s with
          balances := fun t => if t = token then s.balances t - amount else s.balances t
          borrowed := borrowed'
          gasUsed := s.gasUsed + estimateGas a
        }
        Except.ok s'
  
  | Action.swap amountIn tokenIn tokenOut minOut protocol =>
      -- Check balance
      if s.balances tokenIn < amountIn then
        Except.error (TypeError.insufficientBalance tokenIn amountIn (s.balances tokenIn))
      else
        -- Simple swap model: deduct input, add output
        let s' := { s with
          balances := fun t => 
            if t = tokenIn then s.balances t - amountIn
            else if t = tokenOut then s.balances t + minOut
            else s.balances t
          gasUsed := s.gasUsed + estimateGas a
        }
        Except.ok s'
  
  | Action.bridge toChain token amount =>
      -- Check balance and update chain
      if s.balances token < amount then
        Except.error (TypeError.insufficientBalance token amount (s.balances token))
      else
        let s' := { s with
          currentChain := toChain
          currentBlock := s.currentBlock + estimateDelay a
          gasUsed := s.gasUsed + estimateGas a
          -- Balance stays same (simplified model)
        }
        Except.ok s'
  
  | Action.deposit amount token _ =>
      if s.balances token < amount then
        Except.error (TypeError.insufficientBalance token amount (s.balances token))
      else
        Except.ok { s with gasUsed := s.gasUsed + estimateGas a }
  
  | Action.withdraw amount token _ =>
      Except.ok { s with
        balances := fun t => if t = token then s.balances t + amount else s.balances t
        gasUsed := s.gasUsed + estimateGas a
      }

/-- Enhanced type check using categorical gas optimization -/
def checkExpr : Expr → State → CheckResult
  | Expr.action a, s => checkAction a s
  
  | Expr.seq e1 e2, s => do
      let s' ← checkExpr e1 s
      checkExpr e2 s'
  
  | Expr.parallel e1 e2, s =>
      -- Simplified: check both can execute from same state
      let r1 := checkExpr e1 s
      let r2 := checkExpr e2 s
      match r1, r2 with
      | Except.ok s1, Except.ok s2 =>
          -- Merge states (simplified)
          Except.ok { s with
            gasUsed := s1.gasUsed + s2.gasUsed
            currentBlock := max s1.currentBlock s2.currentBlock
          }
      | Except.error e, _ => Except.error e
      | _, Except.error e => Except.error e
  
  | Expr.withConstraint _ e, s => checkExpr e s
  
  | Expr.onChain chain e, s =>
      if s.currentChain ≠ chain then
        Except.error (TypeError.wrongChain chain s.currentChain)
      else
        checkExpr e s

/-- Check all constraints are satisfied. -/
def checkConstraints (constraints : List Constraint) (finalState : State) : CheckResult :=
  constraints.foldlM (fun s c =>
    match c with
    | Constraint.deadline blocks =>
        if finalState.currentBlock > blocks then
          Except.error (TypeError.deadlineExceeded blocks finalState.currentBlock)
        else
          Except.ok s
    | Constraint.minBalance token amount =>
        if finalState.balances token < amount then
          Except.error (TypeError.insufficientBalance token amount (finalState.balances token))
        else
          Except.ok s
    | _ => Except.ok s  -- Other constraints checked during compilation
  ) finalState

/-- Enhanced type check with categorical gas optimization -/
def typeCheck (bundle : Bundle) : CheckResult := do
  let initState := State.init bundle.startChain
  
  -- Use categorical gas estimation for the entire expression
  let optimizedGas := categoricalEstimateGas bundle.expr
  let initStateWithGas := { initState with gasUsed := optimizedGas }
  
  let finalState ← checkExpr bundle.expr initStateWithGas
  
  -- Check all borrows are repaid
  match finalState.borrowed with
  | [] => checkConstraints bundle.constraints finalState
  | (token, amount, protocol) :: _ =>
      Except.error (TypeError.unrepaidBorrow token amount protocol)

/-- Example: Type check the flash loan. -/
#eval typeCheck exampleFlashLoan

end DSL 