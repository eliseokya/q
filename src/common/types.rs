//! Core types for the analyzer
//! 
//! These types represent the fundamental building blocks of the DSL.

use serde::{Serialize, Deserialize};
use std::fmt;

/// Represents a bundle of actions
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct Bundle {
    pub name: String,
    pub expr: Expr,
    pub constraints: Vec<Constraint>,
}

/// Represents an expression in the DSL
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum Expr {
    Action { action: Action },
    Seq { e1: Box<Expr>, e2: Box<Expr> },
    Parallel { exprs: Vec<Expr> },
    OnChain { chain: Chain, expr: Box<Expr> },
}

/// Represents an action in the DSL
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum Action {
    Transfer {
        from: String,
        to: String,
        token: Token,
        amount: Rational,
    },
    Swap {
        token_in: Token,
        token_out: Token,
        amount: Rational,
        protocol: Protocol,
    },
    Bridge {
        chain: Chain,
        token: Token,
        amount: Rational,
    },
    Borrow {
        token: Token,
        amount: Rational,
        protocol: Protocol,
    },
    Repay {
        token: Token,
        amount: Rational,
        protocol: Protocol,
    },
    Deposit {
        token: Token,
        amount: Rational,
        protocol: Protocol,
    },
    Withdraw {
        token: Token,
        amount: Rational,
        protocol: Protocol,
    },
}

/// Represents a token
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum Token {
    WETH,
    USDC,
    DAI,
    WBTC,
    Custom(String),
}

/// Represents a protocol
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum Protocol {
    UniswapV2,
    UniswapV3,
    Aave,
    Compound,
    Custom(String),
}

/// Represents a blockchain
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Chain {
    Ethereum,
    Polygon,
    Arbitrum,
    Optimism,
    Custom(String),
}

/// Represents an invariant
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum Invariant {
    ConstantProduct,
    NoNegativeBalance,
}

/// Represents a constraint
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum Constraint {
    Equal(Expr, Expr),
    LessThan(Expr, Expr),
    GreaterThan(Expr, Expr),
    Invariant { name: Invariant },
    MaxGas { amount: u64 },
    Deadline { blocks: u64 },
}

/// Represents a rational number
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct Rational {
    pub numerator: i64,
    pub denominator: i64,
}

impl Rational {
    pub fn new(numerator: i64, denominator: i64) -> Self {
        if denominator == 0 {
            panic!("Denominator cannot be zero");
        }
        let gcd = gcd(numerator.abs(), denominator.abs());
        let sign = if (numerator < 0) ^ (denominator < 0) { -1 } else { 1 };
        Self {
            numerator: sign * numerator.abs() / gcd,
            denominator: denominator.abs() / gcd,
        }
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.denominator == 1 {
            write!(f, "{}", self.numerator)
        } else {
            write!(f, "{}/{}", self.numerator, self.denominator)
        }
    }
}

/// Greatest common divisor
fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}