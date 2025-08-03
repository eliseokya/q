//! Optimize expression trees

use common::{Expr, Chain, CompilerError};

/// Optimize expression tree
pub fn optimize_expression(expr: Expr) -> Result<Expr, CompilerError> {
    // Apply various optimizations
    let expr = flatten_nested_seq(expr);
    let expr = flatten_nested_parallel(expr);
    let expr = flatten_nested_onchain(expr);
    let expr = remove_redundant_seq(expr);
    
    Ok(expr)
}

/// Flatten nested sequential expressions
/// Seq(a, Seq(b, c)) -> Seq(a, Seq(b, c)) (already optimal)
fn flatten_nested_seq(expr: Expr) -> Expr {
    match expr {
        Expr::Seq { e1, e2 } => {
            let e1_opt = flatten_nested_seq(*e1);
            let e2_opt = flatten_nested_seq(*e2);
            Expr::Seq { e1: Box::new(e1_opt), e2: Box::new(e2_opt) }
        },
        Expr::Parallel { exprs } => {
            Expr::Parallel { exprs: exprs.into_iter().map(flatten_nested_seq).collect() }
        },
        Expr::OnChain { chain, expr } => {
            Expr::OnChain { chain, expr: Box::new(flatten_nested_seq(*expr)) }
        },
        other => other,
    }
}

/// Flatten nested parallel expressions
/// Parallel([a, Parallel([b, c])]) -> Parallel([a, b, c])
fn flatten_nested_parallel(expr: Expr) -> Expr {
    match expr {
        Expr::Parallel { exprs } => {
            let mut flattened = Vec::new();
            for e in exprs {
                match flatten_nested_parallel(e) {
                    Expr::Parallel { exprs: inner } => {
                        // Flatten nested parallel
                        flattened.extend(inner);
                    },
                    other => {
                        flattened.push(other);
                    }
                }
            }
            
            // Don't create single-element parallel
            if flattened.len() == 1 {
                flattened.into_iter().next().unwrap()
            } else {
                Expr::Parallel { exprs: flattened }
            }
        },
        Expr::Seq { e1, e2 } => {
            Expr::Seq {
                e1: Box::new(flatten_nested_parallel(*e1)),
                e2: Box::new(flatten_nested_parallel(*e2))
            }
        },
        Expr::OnChain { chain, expr } => {
            Expr::OnChain { chain, expr: Box::new(flatten_nested_parallel(*expr)) }
        },
        other => other,
    }
}

/// Flatten nested OnChain expressions with same chain
/// OnChain(polygon, OnChain(polygon, expr)) -> OnChain(polygon, expr)
fn flatten_nested_onchain(expr: Expr) -> Expr {
    match expr {
        Expr::OnChain { chain, expr: inner } => {
            match flatten_nested_onchain(*inner) {
                Expr::OnChain { chain: inner_chain, expr: inner_expr } if chain == inner_chain => {
                    // Flatten nested OnChain with same chain
                    Expr::OnChain { chain, expr: inner_expr }
                },
                other => Expr::OnChain { chain, expr: Box::new(other) },
            }
        },
        Expr::Seq { e1, e2 } => {
            Expr::Seq {
                e1: Box::new(flatten_nested_onchain(*e1)),
                e2: Box::new(flatten_nested_onchain(*e2))
            }
        },
        Expr::Parallel { exprs } => {
            Expr::Parallel { exprs: exprs.into_iter().map(flatten_nested_onchain).collect() }
        },
        other => other,
    }
}

/// Remove redundant sequential wrappers
/// Seq(action, Seq(action, action)) stays as is (already optimal)
fn remove_redundant_seq(expr: Expr) -> Expr {
    match expr {
        Expr::Seq { e1, e2 } => {
            let e1_opt = remove_redundant_seq(*e1);
            let e2_opt = remove_redundant_seq(*e2);
            
            // Check for empty expressions (shouldn't happen in practice)
            match (&e1_opt, &e2_opt) {
                (Expr::Parallel { exprs: v1 }, _) if v1.is_empty() => e2_opt,
                (_, Expr::Parallel { exprs: v2 }) if v2.is_empty() => e1_opt,
                _ => Expr::Seq { e1: Box::new(e1_opt), e2: Box::new(e2_opt) },
            }
        },
        Expr::Parallel { exprs } => {
            let optimized: Vec<_> = exprs.into_iter()
                .map(remove_redundant_seq)
                .filter(|e| !matches!(e, Expr::Parallel { exprs: v } if v.is_empty()))
                .collect();
                
            if optimized.is_empty() {
                Expr::Parallel { exprs: vec![] }
            } else if optimized.len() == 1 {
                optimized.into_iter().next().unwrap()
            } else {
                Expr::Parallel { exprs: optimized }
            }
        },
        Expr::OnChain { chain, expr } => {
            Expr::OnChain { chain, expr: Box::new(remove_redundant_seq(*expr)) }
        },
        other => other,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use common::{Action, Token, Protocol, Rational};

    fn create_action() -> Expr {
        Expr::Action { action: Action::Swap {
            amount_in: Rational::from_integer(100),
            token_in: Token::WETH,
            token_out: Token::USDC,
            min_out: Rational::from_integer(0),
            protocol: Protocol::UniswapV2,
        } }
    }

    #[test]
    fn test_flatten_nested_parallel() {
        let expr = Expr::Parallel { exprs: vec![
            create_action(),
            Expr::Parallel { exprs: vec![
                create_action(),
                create_action(),
            ] },
        ] };

        let optimized = optimize_expression(expr).unwrap();
        
        match optimized {
            Expr::Parallel { exprs } => {
                assert_eq!(exprs.len(), 3);
                for e in exprs {
                    assert!(matches!(e, Expr::Action { action: _ }));
                }
            },
            _ => panic!("Expected flattened parallel"),
        }
    }

    #[test]
    fn test_flatten_nested_onchain() {
        let expr = Expr::OnChain {
            chain: Chain::Polygon,
            expr: Box::new(Expr::OnChain {
                chain: Chain::Polygon,
                expr: Box::new(create_action())
            })
        };

        let optimized = optimize_expression(expr).unwrap();
        
        match optimized {
            Expr::OnChain { chain, expr: inner } => {
                assert_eq!(chain, Chain::Polygon);
                assert!(matches!(*inner, Expr::Action { action: _ }));
            },
            _ => panic!("Expected flattened OnChain"),
        }
    }

    #[test]
    fn test_no_flatten_different_chains() {
        let expr = Expr::OnChain {
            chain: Chain::Polygon,
            expr: Box::new(Expr::OnChain {
                chain: Chain::Arbitrum,
                expr: Box::new(create_action())
            })
        };

        let optimized = optimize_expression(expr).unwrap();
        
        match optimized {
            Expr::OnChain { chain: chain1, expr: inner } => {
                assert_eq!(chain1, Chain::Polygon);
                match *inner {
                    Expr::OnChain { chain: chain2, expr: _ } => {
                        assert_eq!(chain2, Chain::Arbitrum);
                    },
                    _ => panic!("Expected nested OnChain with different chain"),
                }
            },
            _ => panic!("Expected OnChain"),
        }
    }

    #[test]
    fn test_single_element_parallel() {
        let expr = Expr::Parallel { exprs: vec![create_action()] };

        let optimized = optimize_expression(expr).unwrap();
        
        // Single element parallel should be unwrapped
        assert!(matches!(optimized, Expr::Action { action: _ }));
    }

    #[test]
    fn test_complex_optimization() {
        let expr = Expr::OnChain {
            chain: Chain::Polygon,
            expr: Box::new(Expr::Seq {
                e1: Box::new(create_action()),
                e2: Box::new(Expr::Parallel { exprs: vec![
                    create_action(),
                    Expr::Parallel { exprs: vec![create_action()] },
                ] })
            })
        };

        let optimized = optimize_expression(expr).unwrap();
        
        match optimized {
            Expr::OnChain { chain: Chain::Polygon, expr: inner } => {
                match *inner {
                    Expr::Seq { e1: first, e2: second } => {
                        assert!(matches!(*first, Expr::Action { action: _ }));
                        match *second {
                            Expr::Parallel { exprs } => {
                                assert_eq!(exprs.len(), 2); // Nested parallel flattened
                            },
                            _ => panic!("Expected parallel"),
                        }
                    },
                    _ => panic!("Expected Seq"),
                }
            },
            _ => panic!("Expected OnChain"),
        }
    }
}