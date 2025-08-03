//! Common types used across all compiler components
//! Maps directly to the mathematical DSL types in maths/DSL/Syntax.lean

use serde::{Deserialize, Serialize};

/// Rational number representation for exact arithmetic
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub struct Rational {
    pub num: u64,
    pub den: u64,
}

impl Rational {
    pub fn new(num: u64, den: u64) -> Self {
        // TODO: Implement GCD reduction
        Self { num, den }
    }

    pub fn from_integer(n: u64) -> Self {
        Self { num: n, den: 1 }
    }
}

/// Token enumeration matching maths/DSL/Syntax.lean
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
#[serde(rename_all = "UPPERCASE")]
pub enum Token {
    WETH,
    USDC,
    DAI,
    WBTC,
    #[serde(rename = "custom")]
    Custom(String),
}

/// Protocol enumeration matching maths/DSL/Syntax.lean
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub enum Protocol {
    Aave,
    UniswapV2,
    Compound,
    #[serde(rename = "custom")]
    Custom(String),
}

/// Chain enumeration matching maths/Chain.lean
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
#[serde(rename_all = "lowercase")]
pub enum Chain {
    Polygon,
    Arbitrum,
}

/// Action types matching maths/DSL/Syntax.lean
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
#[serde(tag = "type", rename_all = "lowercase")]
pub enum Action {
    #[serde(rename = "borrow")]
    Borrow {
        amount: Rational,
        token: Token,
        protocol: Protocol,
    },
    #[serde(rename = "repay")]
    Repay {
        amount: Rational,
        token: Token,
        protocol: Protocol,
    },
    #[serde(rename = "swap")]
    Swap {
        amount_in: Rational,
        token_in: Token,
        token_out: Token,
        min_out: Rational,
        protocol: Protocol,
    },
    #[serde(rename = "bridge")]
    Bridge {
        chain: Chain,
        token: Token,
        amount: Rational,
    },
    #[serde(rename = "deposit")]
    Deposit {
        amount: Rational,
        token: Token,
        protocol: Protocol,
    },
    #[serde(rename = "withdraw")]
    Withdraw {
        amount: Rational,
        token: Token,
        protocol: Protocol,
    },
}

/// Expression types matching maths/DSL/Syntax.lean
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
#[serde(tag = "type", rename_all = "lowercase")]
pub enum Expr {
    #[serde(rename = "action")]
    Action { action: Action },
    #[serde(rename = "seq")]
    Seq { first: Box<Expr>, second: Box<Expr> },
    #[serde(rename = "parallel")]
    Parallel { exprs: Vec<Expr> },
    #[serde(rename = "onChain")]
    OnChain { chain: Chain, expr: Box<Expr> },
}

/// Invariant types
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Invariant {
    ConstantProduct,
    NoNegativeBalance,
}

/// Constraint types matching maths/DSL/Syntax.lean
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
#[serde(tag = "type", rename_all = "camelCase")]
pub enum Constraint {
    #[serde(rename = "deadline")]
    Deadline { blocks: u64 },
    #[serde(rename = "maxGas")]
    MaxGas { amount: u64 },
    #[serde(rename = "minBalance")]
    MinBalance { token: Token, amount: Rational },
    #[serde(rename = "invariant")]
    Invariant { invariant: Invariant },
}

/// Bundle type matching maths/DSL/Syntax.lean
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub struct Bundle {
    pub name: String,
    #[serde(rename = "startChain")]
    pub start_chain: Chain,
    pub expr: Expr,
    pub constraints: Vec<Constraint>,
}

/// Metadata extracted from opportunity JSON
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Metadata {
    pub opportunity_id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_chain: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub target_chain: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub timestamp: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub expected_profit: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub confidence: Option<f64>,
}

/// Intermediate data structure for pipeline communication
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PipelineData {
    pub metadata: Metadata,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub actions: Option<Vec<serde_json::Value>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub typed_actions: Option<Vec<TypedAction>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub expr: Option<Expr>,
    pub constraints: serde_json::Value,
}

/// Typed action with chain context
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypedAction {
    #[serde(flatten)]
    pub action: Action,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub chain: Option<Chain>,
}