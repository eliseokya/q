//! Build DSL expression trees from typed actions

use common::{Expr, TypedAction, Chain, CompilerError, build_errors};
use crate::parallel_analyzer::ParallelGroup;
use serde_json::json;
use std::collections::HashMap;

/// Build expression tree from typed actions with parallel opportunities
pub fn build_expression_tree(
    actions: &[TypedAction],
    parallel_groups: &[ParallelGroup],
) -> Result<Expr, CompilerError> {
    if actions.is_empty() {
        return Err(CompilerError::new(
            "build-expression",
            build_errors::EMPTY_ACTIONS,
            "Cannot build expression from empty action list".to_string()
        ));
    }

    // Build a map of which actions are in parallel groups
    let mut action_to_group: HashMap<usize, usize> = HashMap::new();
    for (group_idx, group) in parallel_groups.iter().enumerate() {
        for &action_idx in &group.actions {
            action_to_group.insert(action_idx, group_idx);
        }
    }

    // Build expressions recursively
    let expr = build_expr_recursive(actions, 0, actions.len(), &action_to_group, parallel_groups)?;

    // Wrap in chain context
    wrap_with_chain_context(expr, actions)
}

/// Recursively build expression for a range of actions
fn build_expr_recursive(
    actions: &[TypedAction],
    start: usize,
    end: usize,
    action_to_group: &HashMap<usize, usize>,
    parallel_groups: &[ParallelGroup],
) -> Result<Expr, CompilerError> {
    if start >= end {
        return Err(CompilerError::new(
            "build-expression",
            "INVALID_RANGE",
            format!("Invalid range: start {} >= end {}", start, end)
        ));
    }

    // Single action case
    if end - start == 1 {
        return Ok(Expr::Action { action: actions[start].action.clone() });
    }

    // Check if the start action is part of a parallel group
    if let Some(&group_idx) = action_to_group.get(&start) {
        let group = &parallel_groups[group_idx];
        
        // Verify this is the start of the group
        if group.start_index == start {
            // Build parallel expression for the group
            let mut parallel_exprs = Vec::new();
            for &idx in &group.actions {
                parallel_exprs.push(Expr::Action { action: actions[idx].action.clone() });
            }
            
            let parallel_expr = if parallel_exprs.len() == 1 {
                parallel_exprs.into_iter().next().unwrap()
            } else {
                Expr::Parallel { exprs: parallel_exprs }
            };

            // Continue with remaining actions after the group
            let next_start = group.end_index + 1;
            if next_start >= end {
                // This parallel group was the last thing
                return Ok(parallel_expr);
            } else {
                // There are more actions after the parallel group
                let rest_expr = build_expr_recursive(
                    actions, 
                    next_start, 
                    end, 
                    action_to_group, 
                    parallel_groups
                )?;
                return Ok(Expr::Seq { 
                    e1: Box::new(parallel_expr), 
                    e2: Box::new(rest_expr) 
                });
            }
        }
    }

    // Not in a parallel group, build sequential expression
    let first_expr = Expr::Action { action: actions[start].action.clone() };
    
    if start + 1 >= end {
        return Ok(first_expr);
    }

    let rest_expr = build_expr_recursive(
        actions,
        start + 1,
        end,
        action_to_group,
        parallel_groups
    )?;

    Ok(Expr::Seq { 
        e1: Box::new(first_expr), 
        e2: Box::new(rest_expr) 
    })
}

/// Wrap expression with chain context (OnChain)
fn wrap_with_chain_context(expr: Expr, actions: &[TypedAction]) -> Result<Expr, CompilerError> {
    // Group consecutive actions by chain
    let mut chain_groups = Vec::new();
    let mut current_chain = None;
    let mut current_start = 0;

    for (i, action) in actions.iter().enumerate() {
        if current_chain.is_none() {
            current_chain = action.chain.clone();
            current_start = i;
        } else if action.chain != current_chain {
            // Chain changed, save the current group
            if let Some(chain) = current_chain {
                chain_groups.push((chain, current_start, i));
            }
            current_chain = action.chain.clone();
            current_start = i;
        }
    }

    // Don't forget the last group
    if let Some(chain) = current_chain {
        chain_groups.push((chain, current_start, actions.len()));
    }

    // If all actions are on the same chain, wrap the entire expression
    if chain_groups.len() == 1 {
        let (chain, _, _) = &chain_groups[0];
        return Ok(Expr::OnChain { chain: chain.clone(), expr: Box::new(expr) });
    }

    // Otherwise, we need to rebuild the expression with OnChain wrappers
    // This is complex because we need to preserve the parallel structure
    wrap_expr_with_chains(expr, actions, &chain_groups)
}

/// Wrap expression tree with chain contexts
fn wrap_expr_with_chains(
    expr: Expr,
    actions: &[TypedAction],
    chain_groups: &[(Chain, usize, usize)],
) -> Result<Expr, CompilerError> {
    // For now, use a simpler approach: wrap the entire expression
    // In a more sophisticated implementation, we would traverse the expression
    // tree and wrap sub-expressions based on their chain context
    
    // Find the starting chain (should be the same as ending chain for atomicity)
    if let Some((chain, _, _)) = chain_groups.first() {
        Ok(Expr::OnChain { chain: chain.clone(), expr: Box::new(expr) })
    } else {
        Ok(expr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use common::{Action, Token, Protocol, Rational, Chain};

    fn create_action(token: Token) -> TypedAction {
        TypedAction {
            action: Action::Swap {
                amount_in: Rational::from_integer(100),
                token_in: Token::WETH,
                token_out: token,
                min_out: Rational::from_integer(0),
                protocol: Protocol::UniswapV2,
            },
            chain: Some(Chain::Polygon),
        }
    }

    #[test]
    fn test_single_action() {
        let actions = vec![create_action(Token::USDC)];
        let parallel_groups = vec![];

        let expr = build_expression_tree(&actions, &parallel_groups).unwrap();
        
        match expr {
            Expr::OnChain { chain, expr: inner } => {
                assert_eq!(chain, Chain::Polygon);
                assert!(matches!(*inner, Expr::Action { action: _ }));
            },
            _ => panic!("Expected OnChain wrapper"),
        }
    }

    #[test]
    fn test_sequential_actions() {
        let actions = vec![
            create_action(Token::USDC),
            create_action(Token::DAI),
            create_action(Token::WBTC),
        ];
        let parallel_groups = vec![];

        let expr = build_expression_tree(&actions, &parallel_groups).unwrap();
        
        match expr {
            Expr::OnChain { chain: Chain::Polygon, expr: inner } => {
                // Should be Seq(action1, Seq(action2, action3))
                match *inner {
                    Expr::Seq { e1: first, e2: rest } => {
                        assert!(matches!(*first, Expr::Action { action: _ }));
                        assert!(matches!(*rest, Expr::Seq { e1: _, e2: _ }));
                    },
                    _ => panic!("Expected Seq"),
                }
            },
            _ => panic!("Expected OnChain wrapper"),
        }
    }

    #[test]
    fn test_parallel_actions() {
        let actions = vec![
            create_action(Token::USDC),
            create_action(Token::DAI),
            create_action(Token::WBTC),
        ];
        
        // All three actions in parallel
        let parallel_groups = vec![
            ParallelGroup {
                start_index: 0,
                end_index: 2,
                actions: vec![0, 1, 2],
            }
        ];

        let expr = build_expression_tree(&actions, &parallel_groups).unwrap();
        
        match expr {
            Expr::OnChain { chain: Chain::Polygon, expr: inner } => {
                match *inner {
                    Expr::Parallel { exprs } => {
                        assert_eq!(exprs.len(), 3);
                        for expr in exprs {
                            assert!(matches!(expr, Expr::Action { action: _ }));
                        }
                    },
                    _ => panic!("Expected Parallel"),
                }
            },
            _ => panic!("Expected OnChain wrapper"),
        }
    }

    #[test]
    fn test_mixed_sequential_parallel() {
        let actions = vec![
            create_action(Token::USDC),  // Sequential
            create_action(Token::DAI),   // Parallel with next
            create_action(Token::WBTC),  // Parallel with prev
            create_action(Token::Custom("LINK".to_string())), // Sequential
        ];
        
        let parallel_groups = vec![
            ParallelGroup {
                start_index: 1,
                end_index: 2,
                actions: vec![1, 2],
            }
        ];

        let expr = build_expression_tree(&actions, &parallel_groups).unwrap();
        
        match expr {
            Expr::OnChain { chain: Chain::Polygon, expr: inner } => {
                // Should be Seq(action0, Seq(Parallel(action1, action2), action3))
                match *inner {
                    Expr::Seq { e1: first, e2: rest } => {
                        assert!(matches!(*first, Expr::Action { action: _ }));
                        match *rest {
                            Expr::Seq { e1: parallel, e2: last } => {
                                assert!(matches!(*parallel, Expr::Parallel { exprs: _ }));
                                assert!(matches!(*last, Expr::Action { action: _ }));
                            },
                            _ => panic!("Expected nested Seq"),
                        }
                    },
                    _ => panic!("Expected Seq"),
                }
            },
            _ => panic!("Expected OnChain wrapper"),
        }
    }

    #[test]
    fn test_multiple_chains() {
        let mut actions = vec![
            create_action(Token::USDC),
            create_action(Token::DAI),
        ];
        
        // Change the chain of the second action
        actions[1].chain = Some(Chain::Arbitrum);
        
        let parallel_groups = vec![];

        let expr = build_expression_tree(&actions, &parallel_groups).unwrap();
        
        // For now, the implementation wraps with the starting chain
        match expr {
            Expr::OnChain { chain, expr: _ } => {
                assert_eq!(chain, Chain::Polygon);
            },
            _ => panic!("Expected OnChain wrapper"),
        }
    }

    #[test]
    fn test_empty_actions() {
        let actions = vec![];
        let parallel_groups = vec![];

        let result = build_expression_tree(&actions, &parallel_groups);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().code, build_errors::EMPTY_ACTIONS);
    }
}