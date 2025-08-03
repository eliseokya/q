import Chain
import Mathlib

/-!
# DSL Syntax for Cross-Chain Atomic Bundles

This file defines the abstract syntax tree for our domain-specific language
that compiles to formally verified cross-chain execution bundles.
-/

namespace DSL

/-- Token types supported by the DSL. -/
inductive Token
  | ETH
  | WETH  
  | USDC
  | DAI
  | custom (address : String)
  deriving Repr, DecidableEq

/-- Protocol identifiers. -/
inductive Protocol
  | Aave
  | UniswapV2
  | Compound
  | custom (name : String)
  deriving Repr, DecidableEq

/-- Primitive actions in the DSL. -/
inductive Action
  | borrow (amount : ℚ) (token : Token) (protocol : Protocol)
  | repay (amount : ℚ) (token : Token) (protocol : Protocol)
  | swap (amountIn : ℚ) (tokenIn : Token) (tokenOut : Token) (minOut : ℚ) (protocol : Protocol)
  | deposit (amount : ℚ) (token : Token) (protocol : Protocol)
  | withdraw (amount : ℚ) (token : Token) (protocol : Protocol)
  | bridge (chain : Chain) (token : Token) (amount : ℚ)
  deriving Repr

/-- Constraints that must be satisfied. -/
inductive Constraint
  | deadline (blocks : ℕ)  -- Must complete within n blocks
  | minBalance (token : Token) (amount : ℚ)  -- Maintain minimum balance
  | maxGas (amount : ℕ)  -- Total gas limit
  | invariant (name : String)  -- Named invariant to preserve
  deriving Repr

/-- Sequential composition of actions. -/
inductive Expr
  | action (a : Action)
  | seq (e1 e2 : Expr)  -- e1 then e2
  | parallel (e1 e2 : Expr)  -- e1 and e2 in parallel
  | withConstraint (c : Constraint) (e : Expr)
  | onChain (chain : Chain) (e : Expr)  -- Execute e on specific chain
  deriving Repr

/-- A complete bundle specification. -/
structure Bundle where
  name : String
  startChain : Chain
  expr : Expr
  constraints : List Constraint
  deriving Repr

/-- Example: Simple flash loan bundle. -/
def exampleFlashLoan : Bundle := {
  name := "polygon-arbitrum-flash-loan"
  startChain := Chain.polygon
  expr := 
    Expr.seq
      (Expr.action (Action.borrow 100 Token.WETH Protocol.Aave))
      (Expr.seq
        (Expr.action (Action.bridge Chain.arbitrum Token.WETH 100))
        (Expr.seq
          (Expr.onChain Chain.arbitrum 
            (Expr.action (Action.swap 100 Token.WETH Token.USDC 50000 Protocol.UniswapV2)))
          (Expr.seq
            (Expr.action (Action.bridge Chain.polygon Token.WETH 100))
            (Expr.action (Action.repay 100 Token.WETH Protocol.Aave)))))
  constraints := [
    Constraint.deadline 20,  -- Complete within 20 blocks
    Constraint.invariant "constant-product"
  ]
}

/-- Smart constructors for better syntax. -/
namespace Expr

def borrow (amount : ℚ) (token : Token) (on : Protocol := Protocol.Aave) : Expr :=
  action (Action.borrow amount token on)

def swap (amountIn : ℚ) (from to : Token) (minOut : ℚ) (on : Protocol := Protocol.UniswapV2) : Expr :=
  action (Action.swap amountIn from to minOut on)

def bridge (to : Chain) (token : Token) (amount : ℚ) : Expr :=
  action (Action.bridge to token amount)

def repay (amount : ℚ) (token : Token) (on : Protocol := Protocol.Aave) : Expr :=
  action (Action.repay amount token on)

-- Operator for sequential composition
infixr:60 " → " => seq

-- Example using operators
def flashLoanExpr : Expr :=
  borrow 100 Token.WETH →
  bridge Chain.arbitrum Token.WETH 100 →
  onChain Chain.arbitrum (swap 100 Token.WETH Token.USDC 50000) →
  bridge Chain.polygon Token.WETH 100 →
  repay 100 Token.WETH

end Expr

end DSL 